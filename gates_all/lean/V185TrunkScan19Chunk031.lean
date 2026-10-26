import V185TrunkScan19Chunk030

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_310814 : List Nat := [4, 3, 3, 1, 2, 1, 2, 3]
def baseStart_310814 : Nat := 118140960795 + 310814 * 2 ^ 59
def prefixEnd_310814 : Nat := 4983230072969 + 3 ^ 40 * 310814 * 2
def baseEnd_310814 : Nat := 94575985864682768886281

theorem tailTrace_310814 : CollatzResearch.WordTrace tailWord_310814 prefixEnd_310814 94575985864682768886281 := by
  unfold tailWord_310814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417039736997679456271437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7557545263987623766780997 1417039736997679456271437)
  ·
    refine ⟨531389901374129796101789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1417039736997679456271437 531389901374129796101789)
    ·
      refine ⟨199271213015298673538171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 531389901374129796101789 199271213015298673538171)
      ·
        refine ⟨298906819522948010307257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199271213015298673538171 298906819522948010307257)
        ·
          refine ⟨224180114642211007730443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298906819522948010307257 224180114642211007730443)
          ·
            refine ⟨336270171963316511595665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224180114642211007730443 336270171963316511595665)
            ·
              refine ⟨252202628972487383696749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336270171963316511595665 252202628972487383696749)
              ·
                refine ⟨94575985864682768886281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252202628972487383696749 94575985864682768886281)
                ·
                  rfl

theorem cell19_310814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_310814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310814 prefixEnd_310814 := by exact prefixLift 310814
  have htrace : WordTrace (prefixWord ++ tailWord_310814) baseStart_310814 baseEnd_310814 := by
    simpa [prefixWord, tailWord_310814, baseEnd_310814] using wordTrace_append hprefix tailTrace_310814
  have hstable : (prefixWord ++ tailWord_310814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310814).length < 2 ^ (prefixWord ++ tailWord_310814).sum := by decide
  have hdescent : baseEnd_310814 < baseStart_310814 := by decide
  rcases family_descends (prefixWord ++ tailWord_310814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310864 : List Nat := [2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_310864 : Nat := 118140960795 + 310864 * 2 ^ 59
def prefixEnd_310864 : Nat := 4983230072969 + 3 ^ 40 * 310864 * 2
def baseEnd_310864 : Nat := 94591200106297467775033

theorem tailTrace_310864 : CollatzResearch.WordTrace tailWord_310864 prefixEnd_310864 94591200106297467775033 := by
  unfold tailWord_310864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669070772900147094745823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7558761030533529459661097 5669070772900147094745823)
  ·
    refine ⟨8503606159350220642118735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5669070772900147094745823 8503606159350220642118735)
    ·
      refine ⟨12755409239025330963178103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8503606159350220642118735 12755409239025330963178103)
      ·
        refine ⟨19133113858537996444767155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12755409239025330963178103 19133113858537996444767155)
        ·
          refine ⟨28699670787806994667150733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19133113858537996444767155 28699670787806994667150733)
          ·
            refine ⟨10762376545427623000181525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28699670787806994667150733 10762376545427623000181525)
            ·
              refine ⟨504486400566919828133509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10762376545427623000181525 504486400566919828133509)
              ·
                refine ⟨94591200106297467775033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504486400566919828133509 94591200106297467775033)
                ·
                  rfl

theorem cell19_310864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_310864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310864 prefixEnd_310864 := by exact prefixLift 310864
  have htrace : WordTrace (prefixWord ++ tailWord_310864) baseStart_310864 baseEnd_310864 := by
    simpa [prefixWord, tailWord_310864, baseEnd_310864] using wordTrace_append hprefix tailTrace_310864
  have hstable : (prefixWord ++ tailWord_310864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310864).length < 2 ^ (prefixWord ++ tailWord_310864).sum := by decide
  have hdescent : baseEnd_310864 < baseStart_310864 := by decide
  rcases family_descends (prefixWord ++ tailWord_310864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310883 : List Nat := [1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_310883 : Nat := 118140960795 + 310883 * 2 ^ 59
def prefixEnd_310883 : Nat := 4983230072969 + 3 ^ 40 * 310883 * 2
def baseEnd_310883 : Nat := 94596981518111053352759

theorem tailTrace_310883 : CollatzResearch.WordTrace tailWord_310883 prefixEnd_310883 94596981518111053352759 := by
  unfold tailWord_310883
  simp only [CollatzResearch.WordTrace]
  refine ⟨11338834532731460434433303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7559223021820973622955535 11338834532731460434433303)
  ·
    refine ⟨17008251799097190651649955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11338834532731460434433303 17008251799097190651649955)
    ·
      refine ⟨25512377698645785977474933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17008251799097190651649955 25512377698645785977474933)
      ·
        refine ⟨2391785409248042435388275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25512377698645785977474933 2391785409248042435388275)
        ·
          refine ⟨3587678113872063653082413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391785409248042435388275 3587678113872063653082413)
          ·
            refine ⟨1345379292702023869905905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3587678113872063653082413 1345379292702023869905905)
            ·
              refine ⟨1009034469526517902429429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345379292702023869905905 1009034469526517902429429)
              ·
                refine ⟨94596981518111053352759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1009034469526517902429429 94596981518111053352759)
                ·
                  rfl

theorem cell19_310883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_310883 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310883 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310883 prefixEnd_310883 := by exact prefixLift 310883
  have htrace : WordTrace (prefixWord ++ tailWord_310883) baseStart_310883 baseEnd_310883 := by
    simpa [prefixWord, tailWord_310883, baseEnd_310883] using wordTrace_append hprefix tailTrace_310883
  have hstable : (prefixWord ++ tailWord_310883).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310883).length < 2 ^ (prefixWord ++ tailWord_310883).sum := by decide
  have hdescent : baseEnd_310883 < baseStart_310883 := by decide
  rcases family_descends (prefixWord ++ tailWord_310883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310919 : List Nat := [1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_310919 : Nat := 118140960795 + 310919 * 2 ^ 59
def prefixEnd_310919 : Nat := 4983230072969 + 3 ^ 40 * 310919 * 2
def baseEnd_310919 : Nat := 94607935772073636552661

theorem tailTrace_310919 : CollatzResearch.WordTrace tailWord_310919 prefixEnd_310919 94607935772073636552661 := by
  unfold tailWord_310919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340147560601038582743811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7560098373734025721829207 11340147560601038582743811)
  ·
    refine ⟨17010221340901557874115717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11340147560601038582743811 17010221340901557874115717)
    ·
      refine ⟨3189416501419042101396697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17010221340901557874115717 3189416501419042101396697)
      ·
        refine ⟨2392062376064281576047523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189416501419042101396697 2392062376064281576047523)
        ·
          refine ⟨3588093564096422364071285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392062376064281576047523 3588093564096422364071285)
          ·
            refine ⟨336383771634039596631683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3588093564096422364071285 336383771634039596631683)
            ·
              refine ⟨504575657451059394947525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336383771634039596631683 504575657451059394947525)
              ·
                refine ⟨94607935772073636552661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504575657451059394947525 94607935772073636552661)
                ·
                  rfl

theorem cell19_310919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_310919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310919 prefixEnd_310919 := by exact prefixLift 310919
  have htrace : WordTrace (prefixWord ++ tailWord_310919) baseStart_310919 baseEnd_310919 := by
    simpa [prefixWord, tailWord_310919, baseEnd_310919] using wordTrace_append hprefix tailTrace_310919
  have hstable : (prefixWord ++ tailWord_310919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310919).length < 2 ^ (prefixWord ++ tailWord_310919).sum := by decide
  have hdescent : baseEnd_310919 < baseStart_310919 := by decide
  rcases family_descends (prefixWord ++ tailWord_310919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310921 : List Nat := [1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_310921 : Nat := 118140960795 + 310921 * 2 ^ 59
def prefixEnd_310921 : Nat := 4983230072969 + 3 ^ 40 * 310921 * 2
def baseEnd_310921 : Nat := 94608544341738224508211

theorem tailTrace_310921 : CollatzResearch.WordTrace tailWord_310921 prefixEnd_310921 94608544341738224508211 := by
  unfold tailWord_310921
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340220506593792924316617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7560147004395861949544411 11340220506593792924316617)
  ·
    refine ⟨8505165379945344693237463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11340220506593792924316617 8505165379945344693237463)
    ·
      refine ⟨12757748069918017039856195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8505165379945344693237463 12757748069918017039856195)
      ·
        refine ⟨19136622104877025559784293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12757748069918017039856195 19136622104877025559784293)
        ·
          refine ⟨3588116644664442292459555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19136622104877025559784293 3588116644664442292459555)
          ·
            refine ⟨5382174966996663438689333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588116644664442292459555 5382174966996663438689333)
            ·
              refine ⟨504578903155937197377125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5382174966996663438689333 504578903155937197377125)
              ·
                refine ⟨94608544341738224508211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504578903155937197377125 94608544341738224508211)
                ·
                  rfl

theorem cell19_310921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_310921 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_310921 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_310921 prefixEnd_310921 := by exact prefixLift 310921
  have htrace : WordTrace (prefixWord ++ tailWord_310921) baseStart_310921 baseEnd_310921 := by
    simpa [prefixWord, tailWord_310921, baseEnd_310921] using wordTrace_append hprefix tailTrace_310921
  have hstable : (prefixWord ++ tailWord_310921).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310921).length < 2 ^ (prefixWord ++ tailWord_310921).sum := by decide
  have hdescent : baseEnd_310921 < baseStart_310921 := by decide
  rcases family_descends (prefixWord ++ tailWord_310921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311016 : List Nat := [2, 1, 4, 1, 3, 1, 7]
def baseStart_311016 : Nat := 118140960795 + 311016 * 2 ^ 59
def prefixEnd_311016 : Nat := 4983230072969 + 3 ^ 40 * 311016 * 2
def baseEnd_311016 : Nat := 31545817133602050798947

theorem tailTrace_311016 : CollatzResearch.WordTrace tailWord_311016 prefixEnd_311016 31545817133602050798947 := by
  unfold tailWord_311016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671842720624812074512451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7562456960833082766016601 5671842720624812074512451)
  ·
    refine ⟨8507764080937218111768677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671842720624812074512451 8507764080937218111768677)
    ·
      refine ⟨1595205765175728395956627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8507764080937218111768677 1595205765175728395956627)
      ·
        refine ⟨2392808647763592593934941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595205765175728395956627 2392808647763592593934941)
        ·
          refine ⟨897303242911347222725603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2392808647763592593934941 897303242911347222725603)
          ·
            refine ⟨1345954864367020834088405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897303242911347222725603 1345954864367020834088405)
            ·
              refine ⟨31545817133602050798947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1345954864367020834088405 31545817133602050798947)
              ·
                rfl

theorem cell19_311016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 7].length) (baseStart_311016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311016 prefixEnd_311016 := by exact prefixLift 311016
  have htrace : WordTrace (prefixWord ++ tailWord_311016) baseStart_311016 baseEnd_311016 := by
    simpa [prefixWord, tailWord_311016, baseEnd_311016] using wordTrace_append hprefix tailTrace_311016
  have hstable : (prefixWord ++ tailWord_311016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311016).length < 2 ^ (prefixWord ++ tailWord_311016).sum := by decide
  have hdescent : baseEnd_311016 < baseStart_311016 := by decide
  rcases family_descends (prefixWord ++ tailWord_311016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311054 : List Nat := [4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_311054 : Nat := 118140960795 + 311054 * 2 ^ 59
def prefixEnd_311054 : Nat := 4983230072969 + 3 ^ 40 * 311054 * 2
def baseEnd_311054 : Nat := 94649014224433323552293

theorem tailTrace_311054 : CollatzResearch.WordTrace tailWord_311054 prefixEnd_311054 94649014224433323552293 := by
  unfold tailWord_311054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418133926888994579863527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7563380943407971092605477 1418133926888994579863527)
  ·
    refine ⟨2127200890333491869795291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418133926888994579863527 2127200890333491869795291)
    ·
      refine ⟨3190801335500237804692937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127200890333491869795291 3190801335500237804692937)
      ·
        refine ⟨2393101001625178353519703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3190801335500237804692937 2393101001625178353519703)
        ·
          refine ⟨3589651502437767530279555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393101001625178353519703 3589651502437767530279555)
          ·
            refine ⟨5384477253656651295419333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589651502437767530279555 5384477253656651295419333)
            ·
              refine ⟨1009589485060622117891125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5384477253656651295419333 1009589485060622117891125)
              ·
                refine ⟨94649014224433323552293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1009589485060622117891125 94649014224433323552293)
                ·
                  rfl

theorem cell19_311054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_311054 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311054 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311054 prefixEnd_311054 := by exact prefixLift 311054
  have htrace : WordTrace (prefixWord ++ tailWord_311054) baseStart_311054 baseEnd_311054 := by
    simpa [prefixWord, tailWord_311054, baseEnd_311054] using wordTrace_append hprefix tailTrace_311054
  have hstable : (prefixWord ++ tailWord_311054).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311054).length < 2 ^ (prefixWord ++ tailWord_311054).sum := by decide
  have hdescent : baseEnd_311054 < baseStart_311054 := by decide
  rcases family_descends (prefixWord ++ tailWord_311054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311086 : List Nat := [4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_311086 : Nat := 118140960795 + 311086 * 2 ^ 59
def prefixEnd_311086 : Nat := 4983230072969 + 3 ^ 40 * 311086 * 2
def baseEnd_311086 : Nat := 94658751339066730841095

theorem tailTrace_311086 : CollatzResearch.WordTrace tailWord_311086 prefixEnd_311086 94658751339066730841095 := by
  unfold tailWord_311086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418279818874503263009139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7564159033997350736048741 1418279818874503263009139)
  ·
    refine ⟨2127419728311754894513709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418279818874503263009139 2127419728311754894513709)
    ·
      refine ⟨797782398116908085442641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2127419728311754894513709 797782398116908085442641)
      ·
        refine ⟨598336798587681064081981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797782398116908085442641 598336798587681064081981)
        ·
          refine ⟨224376299470380399030743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 598336798587681064081981 224376299470380399030743)
          ·
            refine ⟨336564449205570598546115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224376299470380399030743 336564449205570598546115)
            ·
              refine ⟨504846673808355897819173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336564449205570598546115 504846673808355897819173)
              ·
                refine ⟨94658751339066730841095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504846673808355897819173 94658751339066730841095)
                ·
                  rfl

theorem cell19_311086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_311086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311086 prefixEnd_311086 := by exact prefixLift 311086
  have htrace : WordTrace (prefixWord ++ tailWord_311086) baseStart_311086 baseEnd_311086 := by
    simpa [prefixWord, tailWord_311086, baseEnd_311086] using wordTrace_append hprefix tailTrace_311086
  have hstable : (prefixWord ++ tailWord_311086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311086).length < 2 ^ (prefixWord ++ tailWord_311086).sum := by decide
  have hdescent : baseEnd_311086 < baseStart_311086 := by decide
  rcases family_descends (prefixWord ++ tailWord_311086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311090 : List Nat := [3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_311090 : Nat := 118140960795 + 311090 * 2 ^ 59
def prefixEnd_311090 : Nat := 4983230072969 + 3 ^ 40 * 311090 * 2
def baseEnd_311090 : Nat := 94659968478395906752195

theorem tailTrace_311090 : CollatzResearch.WordTrace tailWord_311090 prefixEnd_311090 94659968478395906752195 := by
  unfold tailWord_311090
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836596110745383696804681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7564256295321023191479149 2836596110745383696804681)
  ·
    refine ⟨2127447083059037772603511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2836596110745383696804681 2127447083059037772603511)
    ·
      refine ⟨3191170624588556658905267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127447083059037772603511 3191170624588556658905267)
      ·
        refine ⟨4786755936882834988357901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191170624588556658905267 4786755936882834988357901)
        ·
          refine ⟨1795033476331063120634213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4786755936882834988357901 1795033476331063120634213)
          ·
            refine ⟨336568776812074335118915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1795033476331063120634213 336568776812074335118915)
            ·
              refine ⟨504853165218111502678373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336568776812074335118915 504853165218111502678373)
              ·
                refine ⟨94659968478395906752195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504853165218111502678373 94659968478395906752195)
                ·
                  rfl

theorem cell19_311090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_311090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311090 prefixEnd_311090 := by exact prefixLift 311090
  have htrace : WordTrace (prefixWord ++ tailWord_311090) baseStart_311090 baseEnd_311090 := by
    simpa [prefixWord, tailWord_311090, baseEnd_311090] using wordTrace_append hprefix tailTrace_311090
  have hstable : (prefixWord ++ tailWord_311090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311090).length < 2 ^ (prefixWord ++ tailWord_311090).sum := by decide
  have hdescent : baseEnd_311090 < baseStart_311090 := by decide
  rcases family_descends (prefixWord ++ tailWord_311090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311263 : List Nat := [1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_311263 : Nat := 118140960795 + 311263 * 2 ^ 59
def prefixEnd_311263 : Nat := 4983230072969 + 3 ^ 40 * 311263 * 2
def baseEnd_311263 : Nat := 94712609754382764907279

theorem tailTrace_311263 : CollatzResearch.WordTrace tailWord_311263 prefixEnd_311263 94712609754382764907279 := by
  unfold tailWord_311263
  simp only [CollatzResearch.WordTrace]
  refine ⟨11352694271354785333266443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7568462847569856888844295 11352694271354785333266443)
  ·
    refine ⟨17029041407032177999899665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11352694271354785333266443 17029041407032177999899665)
    ·
      refine ⟨12771781055274133499924749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17029041407032177999899665 12771781055274133499924749)
      ·
        refine ⟨4789417895727800062471781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12771781055274133499924749 4789417895727800062471781)
        ·
          refine ⟨898015855448962511713459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4789417895727800062471781 898015855448962511713459)
          ·
            refine ⟨1347023783173443767570189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898015855448962511713459 1347023783173443767570189)
            ·
              refine ⟨505133918690041412838821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1347023783173443767570189 505133918690041412838821)
              ·
                refine ⟨94712609754382764907279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505133918690041412838821 94712609754382764907279)
                ·
                  rfl

theorem cell19_311263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_311263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311263 prefixEnd_311263 := by exact prefixLift 311263
  have htrace : WordTrace (prefixWord ++ tailWord_311263) baseStart_311263 baseEnd_311263 := by
    simpa [prefixWord, tailWord_311263, baseEnd_311263] using wordTrace_append hprefix tailTrace_311263
  have hstable : (prefixWord ++ tailWord_311263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311263).length < 2 ^ (prefixWord ++ tailWord_311263).sum := by decide
  have hdescent : baseEnd_311263 < baseStart_311263 := by decide
  rcases family_descends (prefixWord ++ tailWord_311263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311360 : List Nat := [2, 1, 1, 2, 2, 4, 7]
def baseStart_311360 : Nat := 118140960795 + 311360 * 2 ^ 59
def prefixEnd_311360 : Nat := 4983230072969 + 3 ^ 40 * 311360 * 2
def baseEnd_311360 : Nat := 31580708461038426917153

theorem tailTrace_311360 : CollatzResearch.WordTrace tailWord_311360 prefixEnd_311360 31580708461038426917153 := by
  unfold tailWord_311360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678116076001685449773767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7570821434668913933031689 5678116076001685449773767)
  ·
    refine ⟨8517174114002528174660651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5678116076001685449773767 8517174114002528174660651)
    ·
      refine ⟨12775761171003792261990977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8517174114002528174660651 12775761171003792261990977)
      ·
        refine ⟨9581820878252844196493233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12775761171003792261990977 9581820878252844196493233)
        ·
          refine ⟨7186365658689633147369925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9581820878252844196493233 7186365658689633147369925)
          ·
            refine ⟨1347443561004306215131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7186365658689633147369925 1347443561004306215131861)
            ·
              refine ⟨31580708461038426917153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1347443561004306215131861 31580708461038426917153)
              ·
                rfl

theorem cell19_311360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_311360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311360 prefixEnd_311360 := by exact prefixLift 311360
  have htrace : WordTrace (prefixWord ++ tailWord_311360) baseStart_311360 baseEnd_311360 := by
    simpa [prefixWord, tailWord_311360, baseEnd_311360] using wordTrace_append hprefix tailTrace_311360
  have hstable : (prefixWord ++ tailWord_311360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311360).length < 2 ^ (prefixWord ++ tailWord_311360).sum := by decide
  have hdescent : baseEnd_311360 < baseStart_311360 := by decide
  rcases family_descends (prefixWord ++ tailWord_311360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311417 : List Nat := [1, 2, 1, 3, 4, 8]
def baseStart_311417 : Nat := 118140960795 + 311417 * 2 ^ 59
def prefixEnd_311417 : Nat := 4983230072969 + 3 ^ 40 * 311417 * 2
def baseEnd_311417 : Nat := 10528829957617337498293

theorem tailTrace_311417 : CollatzResearch.WordTrace tailWord_311417 prefixEnd_311417 10528829957617337498293 := by
  unfold tailWord_311417
  simp only [CollatzResearch.WordTrace]
  refine ⟨11358311112796869634372505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7572207408531246422915003 11358311112796869634372505)
  ·
    refine ⟨8518733334597652225779379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11358311112796869634372505 8518733334597652225779379)
    ·
      refine ⟨12778100001896478338669069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8518733334597652225779379 12778100001896478338669069)
      ·
        refine ⟨4791787500711179377000901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12778100001896478338669069 4791787500711179377000901)
        ·
          refine ⟨898460156383346133187669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4791787500711179377000901 898460156383346133187669)
          ·
            refine ⟨10528829957617337498293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 898460156383346133187669 10528829957617337498293)
            ·
              rfl

theorem cell19_311417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_311417 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311417 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311417 prefixEnd_311417 := by exact prefixLift 311417
  have htrace : WordTrace (prefixWord ++ tailWord_311417) baseStart_311417 baseEnd_311417 := by
    simpa [prefixWord, tailWord_311417, baseEnd_311417] using wordTrace_append hprefix tailTrace_311417
  have hstable : (prefixWord ++ tailWord_311417).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311417).length < 2 ^ (prefixWord ++ tailWord_311417).sum := by decide
  have hdescent : baseEnd_311417 < baseStart_311417 := by decide
  rcases family_descends (prefixWord ++ tailWord_311417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311432 : List Nat := [2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_311432 : Nat := 118140960795 + 311432 * 2 ^ 59
def prefixEnd_311432 : Nat := 4983230072969 + 3 ^ 40 * 311432 * 2
def baseEnd_311432 : Nat := 94764033891040447151263

theorem tailTrace_311432 : CollatzResearch.WordTrace tailWord_311432 prefixEnd_311432 94764033891040447151263 := by
  unfold tailWord_311432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5679429103871263598084275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7572572138495018130779033 5679429103871263598084275)
  ·
    refine ⟨8519143655806895397126413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5679429103871263598084275 8519143655806895397126413)
    ·
      refine ⟨3194678870927585773922405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8519143655806895397126413 3194678870927585773922405)
      ·
        refine ⟨599002288298922332610451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3194678870927585773922405 599002288298922332610451)
        ·
          refine ⟨898503432448383498915677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599002288298922332610451 898503432448383498915677)
          ·
            refine ⟨336938787168143812093379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 898503432448383498915677 336938787168143812093379)
            ·
              refine ⟨505408180752215718140069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336938787168143812093379 505408180752215718140069)
              ·
                refine ⟨94764033891040447151263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505408180752215718140069 94764033891040447151263)
                ·
                  rfl

theorem cell19_311432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_311432 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311432 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311432 prefixEnd_311432 := by exact prefixLift 311432
  have htrace : WordTrace (prefixWord ++ tailWord_311432) baseStart_311432 baseEnd_311432 := by
    simpa [prefixWord, tailWord_311432, baseEnd_311432] using wordTrace_append hprefix tailTrace_311432
  have hstable : (prefixWord ++ tailWord_311432).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311432).length < 2 ^ (prefixWord ++ tailWord_311432).sum := by decide
  have hdescent : baseEnd_311432 < baseStart_311432 := by decide
  rcases family_descends (prefixWord ++ tailWord_311432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311434 : List Nat := [3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_311434 : Nat := 118140960795 + 311434 * 2 ^ 59
def prefixEnd_311434 : Nat := 4983230072969 + 3 ^ 40 * 311434 * 2
def baseEnd_311434 : Nat := 94764642460705035106813

theorem tailTrace_311434 : CollatzResearch.WordTrace tailWord_311434 prefixEnd_311434 94764642460705035106813 := by
  unfold tailWord_311434
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839732788433820384435339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7572620769156854358494237 2839732788433820384435339)
  ·
    refine ⟨4259599182650730576653009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2839732788433820384435339 4259599182650730576653009)
    ·
      refine ⟨3194699386988047932489757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4259599182650730576653009 3194699386988047932489757)
      ·
        refine ⟨1198012270120517974683659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3194699386988047932489757 1198012270120517974683659)
        ·
          refine ⟨1797018405180776962025489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198012270120517974683659 1797018405180776962025489)
          ·
            refine ⟨1347763803885582721519117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797018405180776962025489 1347763803885582721519117)
            ·
              refine ⟨505411426457093520569669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1347763803885582721519117 505411426457093520569669)
              ·
                refine ⟨94764642460705035106813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505411426457093520569669 94764642460705035106813)
                ·
                  rfl

theorem cell19_311434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_311434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311434 prefixEnd_311434 := by exact prefixLift 311434
  have htrace : WordTrace (prefixWord ++ tailWord_311434) baseStart_311434 baseEnd_311434 := by
    simpa [prefixWord, tailWord_311434, baseEnd_311434] using wordTrace_append hprefix tailTrace_311434
  have hstable : (prefixWord ++ tailWord_311434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311434).length < 2 ^ (prefixWord ++ tailWord_311434).sum := by decide
  have hdescent : baseEnd_311434 < baseStart_311434 := by decide
  rcases family_descends (prefixWord ++ tailWord_311434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311474 : List Nat := [3, 2, 1, 1, 1, 3, 8]
def baseStart_311474 : Nat := 118140960795 + 311474 * 2 ^ 59
def prefixEnd_311474 : Nat := 4983230072969 + 3 ^ 40 * 311474 * 2
def baseEnd_311474 : Nat := 31592271284665598072605

theorem tailTrace_311474 : CollatzResearch.WordTrace tailWord_311474 prefixEnd_311474 31592271284665598072605 := by
  unfold tailWord_311474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2840097518397592092299369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7573593382393578912798317 2840097518397592092299369)
  ·
    refine ⟨2130073138798194069224527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2840097518397592092299369 2130073138798194069224527)
    ·
      refine ⟨3195109708197291103836791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130073138798194069224527 3195109708197291103836791)
      ·
        refine ⟨4792664562295936655755187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195109708197291103836791 4792664562295936655755187)
        ·
          refine ⟨7188996843443904983632781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792664562295936655755187 7188996843443904983632781)
          ·
            refine ⟨2695873816291464368862293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7188996843443904983632781 2695873816291464368862293)
            ·
              refine ⟨31592271284665598072605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2695873816291464368862293 31592271284665598072605)
              ·
                rfl

theorem cell19_311474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 8].length) (baseStart_311474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311474 prefixEnd_311474 := by exact prefixLift 311474
  have htrace : WordTrace (prefixWord ++ tailWord_311474) baseStart_311474 baseEnd_311474 := by
    simpa [prefixWord, tailWord_311474, baseEnd_311474] using wordTrace_append hprefix tailTrace_311474
  have hstable : (prefixWord ++ tailWord_311474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311474).length < 2 ^ (prefixWord ++ tailWord_311474).sum := by decide
  have hdescent : baseEnd_311474 < baseStart_311474 := by decide
  rcases family_descends (prefixWord ++ tailWord_311474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311548 : List Nat := [2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_311548 : Nat := 118140960795 + 311548 * 2 ^ 59
def prefixEnd_311548 : Nat := 4983230072969 + 3 ^ 40 * 311548 * 2
def baseEnd_311548 : Nat := 94799330931586548573169

theorem tailTrace_311548 : CollatzResearch.WordTrace tailWord_311548 prefixEnd_311548 94799330931586548573169 := by
  unfold tailWord_311548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681544537661139503695649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7575392716881519338260865 5681544537661139503695649)
  ·
    refine ⟨4261158403245854627771737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5681544537661139503695649 4261158403245854627771737)
    ·
      refine ⟨3195868802434390970828803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4261158403245854627771737 3195868802434390970828803)
      ·
        refine ⟨4793803203651586456243205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195868802434390970828803 4793803203651586456243205)
        ·
          refine ⟨898838100684672460545601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4793803203651586456243205 898838100684672460545601)
          ·
            refine ⟨674128575513504345409201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898838100684672460545601 674128575513504345409201)
            ·
              refine ⟨505596431635128259056901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674128575513504345409201 505596431635128259056901)
              ·
                refine ⟨94799330931586548573169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505596431635128259056901 94799330931586548573169)
                ·
                  rfl

theorem cell19_311548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_311548 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311548 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311548 prefixEnd_311548 := by exact prefixLift 311548
  have htrace : WordTrace (prefixWord ++ tailWord_311548) baseStart_311548 baseEnd_311548 := by
    simpa [prefixWord, tailWord_311548, baseEnd_311548] using wordTrace_append hprefix tailTrace_311548
  have hstable : (prefixWord ++ tailWord_311548).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311548).length < 2 ^ (prefixWord ++ tailWord_311548).sum := by decide
  have hdescent : baseEnd_311548 < baseStart_311548 := by decide
  rcases family_descends (prefixWord ++ tailWord_311548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311569 : List Nat := [1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_311569 : Nat := 118140960795 + 311569 * 2 ^ 59
def prefixEnd_311569 : Nat := 4983230072969 + 3 ^ 40 * 311569 * 2
def baseEnd_311569 : Nat := 94805720913064722106445

theorem tailTrace_311569 : CollatzResearch.WordTrace tailWord_311569 prefixEnd_311569 94805720913064722106445 := by
  unfold tailWord_311569
  simp only [CollatzResearch.WordTrace]
  refine ⟨11363855008246199593905761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7575903338830799729270507 11363855008246199593905761)
  ·
    refine ⟨8522891256184649695429321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11363855008246199593905761 8522891256184649695429321)
    ·
      refine ⟨6392168442138487271571991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8522891256184649695429321 6392168442138487271571991)
      ·
        refine ⟨9588252663207730907357987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392168442138487271571991 9588252663207730907357987)
        ·
          refine ⟨14382378994811596361036981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9588252663207730907357987 14382378994811596361036981)
          ·
            refine ⟨1348348030763587158847217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14382378994811596361036981 1348348030763587158847217)
            ·
              refine ⟨1011261023072690369135413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348348030763587158847217 1011261023072690369135413)
              ·
                refine ⟨94805720913064722106445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011261023072690369135413 94805720913064722106445)
                ·
                  rfl

theorem cell19_311569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_311569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311569 prefixEnd_311569 := by exact prefixLift 311569
  have htrace : WordTrace (prefixWord ++ tailWord_311569) baseStart_311569 baseEnd_311569 := by
    simpa [prefixWord, tailWord_311569, baseEnd_311569] using wordTrace_append hprefix tailTrace_311569
  have hstable : (prefixWord ++ tailWord_311569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311569).length < 2 ^ (prefixWord ++ tailWord_311569).sum := by decide
  have hdescent : baseEnd_311569 < baseStart_311569 := by decide
  rcases family_descends (prefixWord ++ tailWord_311569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311588 : List Nat := [2, 3, 1, 3, 1, 9]
def baseStart_311588 : Nat := 118140960795 + 311588 * 2 ^ 59
def prefixEnd_311588 : Nat := 4983230072969 + 3 ^ 40 * 311588 * 2
def baseEnd_311588 : Nat := 10534611369430923076019

theorem tailTrace_311588 : CollatzResearch.WordTrace tailWord_311588 prefixEnd_311588 10534611369430923076019 := by
  unfold tailWord_311588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682273997588682919423709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7576365330118243892564945 5682273997588682919423709)
  ·
    refine ⟨2130852749095756094783891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5682273997588682919423709 2130852749095756094783891)
    ·
      refine ⟨3196279123643634142175837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130852749095756094783891 3196279123643634142175837)
      ·
        refine ⟨1198604671366362803315939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3196279123643634142175837 1198604671366362803315939)
        ·
          refine ⟨1797907007049544204973909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198604671366362803315939 1797907007049544204973909)
          ·
            refine ⟨10534611369430923076019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1797907007049544204973909 10534611369430923076019)
            ·
              rfl

theorem cell19_311588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 9].length) (baseStart_311588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311588 prefixEnd_311588 := by exact prefixLift 311588
  have htrace : WordTrace (prefixWord ++ tailWord_311588) baseStart_311588 baseEnd_311588 := by
    simpa [prefixWord, tailWord_311588, baseEnd_311588] using wordTrace_append hprefix tailTrace_311588
  have hstable : (prefixWord ++ tailWord_311588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311588).length < 2 ^ (prefixWord ++ tailWord_311588).sum := by decide
  have hdescent : baseEnd_311588 < baseStart_311588 := by decide
  rcases family_descends (prefixWord ++ tailWord_311588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311620 : List Nat := [2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_311620 : Nat := 118140960795 + 311620 * 2 ^ 59
def prefixEnd_311620 : Nat := 4983230072969 + 3 ^ 40 * 311620 * 2
def baseEnd_311620 : Nat := 94821239439511714972973

theorem tailTrace_311620 : CollatzResearch.WordTrace tailWord_311620 prefixEnd_311620 94821239439511714972973 := by
  unfold tailWord_311620
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682857565530717652006157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7577143420707623536008209 5682857565530717652006157)
  ·
    refine ⟨2131071587074019119502309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5682857565530717652006157 2131071587074019119502309)
    ·
      refine ⟨399575922576378584906683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2131071587074019119502309 399575922576378584906683)
      ·
        refine ⟨599363883864567877360025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399575922576378584906683 599363883864567877360025)
        ·
          refine ⟨449522912898425908020019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599363883864567877360025 449522912898425908020019)
          ·
            refine ⟨674284369347638862030029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449522912898425908020019 674284369347638862030029)
            ·
              refine ⟨252856638505364573261261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 674284369347638862030029 252856638505364573261261)
              ·
                refine ⟨94821239439511714972973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252856638505364573261261 94821239439511714972973)
                ·
                  rfl

theorem cell19_311620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_311620 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311620 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311620 prefixEnd_311620 := by exact prefixLift 311620
  have htrace : WordTrace (prefixWord ++ tailWord_311620) baseStart_311620 baseEnd_311620 := by
    simpa [prefixWord, tailWord_311620, baseEnd_311620] using wordTrace_append hprefix tailTrace_311620
  have hstable : (prefixWord ++ tailWord_311620).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311620).length < 2 ^ (prefixWord ++ tailWord_311620).sum := by decide
  have hdescent : baseEnd_311620 < baseStart_311620 := by decide
  rcases family_descends (prefixWord ++ tailWord_311620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311681 : List Nat := [1, 2, 4, 3, 1, 2, 1, 5]
def baseStart_311681 : Nat := 118140960795 + 311681 * 2 ^ 59
def prefixEnd_311681 : Nat := 4983230072969 + 3 ^ 40 * 311681 * 2
def baseEnd_311681 : Nat := 94839800814281647617251

theorem tailTrace_311681 : CollatzResearch.WordTrace tailWord_311681 prefixEnd_311681 94839800814281647617251 := by
  unfold tailWord_311681
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367939983840442721982897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7578626655893628481321931 11367939983840442721982897)
  ·
    refine ⟨8525954987880332041487173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11367939983840442721982897 8525954987880332041487173)
    ·
      refine ⟨1598616560227562257778845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8525954987880332041487173 1598616560227562257778845)
      ·
        refine ⟨599481210085335846667067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1598616560227562257778845 599481210085335846667067)
        ·
          refine ⟨899221815128003770000601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599481210085335846667067 899221815128003770000601)
          ·
            refine ⟨674416361346002827500451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899221815128003770000601 674416361346002827500451)
            ·
              refine ⟨1011624542019004241250677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674416361346002827500451 1011624542019004241250677)
              ·
                refine ⟨94839800814281647617251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011624542019004241250677 94839800814281647617251)
                ·
                  rfl

theorem cell19_311681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 5].length) (baseStart_311681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311681 prefixEnd_311681 := by exact prefixLift 311681
  have htrace : WordTrace (prefixWord ++ tailWord_311681) baseStart_311681 baseEnd_311681 := by
    simpa [prefixWord, tailWord_311681, baseEnd_311681] using wordTrace_append hprefix tailTrace_311681
  have hstable : (prefixWord ++ tailWord_311681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311681).length < 2 ^ (prefixWord ++ tailWord_311681).sum := by decide
  have hdescent : baseEnd_311681 < baseStart_311681 := by decide
  rcases family_descends (prefixWord ++ tailWord_311681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311719 : List Nat := [1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_311719 : Nat := 118140960795 + 311719 * 2 ^ 59
def prefixEnd_311719 : Nat := 4983230072969 + 3 ^ 40 * 311719 * 2
def baseEnd_311719 : Nat := 94851363637908818772703

theorem tailTrace_311719 : CollatzResearch.WordTrace tailWord_311719 prefixEnd_311719 94851363637908818772703 := by
  unfold tailWord_311719
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369325957702775211866211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7579550638468516807910807 11369325957702775211866211)
  ·
    refine ⟨17053988936554162817799317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11369325957702775211866211 17053988936554162817799317)
    ·
      refine ⟨799405731400976382084343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17053988936554162817799317 799405731400976382084343)
      ·
        refine ⟨1199108597101464573126515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799405731400976382084343 1199108597101464573126515)
        ·
          refine ⟨1798662895652196859689773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199108597101464573126515 1798662895652196859689773)
          ·
            refine ⟨674498585869573822383665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1798662895652196859689773 674498585869573822383665)
            ·
              refine ⟨505873939402180366787749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674498585869573822383665 505873939402180366787749)
              ·
                refine ⟨94851363637908818772703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505873939402180366787749 94851363637908818772703)
                ·
                  rfl

theorem cell19_311719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_311719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311719 prefixEnd_311719 := by exact prefixLift 311719
  have htrace : WordTrace (prefixWord ++ tailWord_311719) baseStart_311719 baseEnd_311719 := by
    simpa [prefixWord, tailWord_311719, baseEnd_311719] using wordTrace_append hprefix tailTrace_311719
  have hstable : (prefixWord ++ tailWord_311719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311719).length < 2 ^ (prefixWord ++ tailWord_311719).sum := by decide
  have hdescent : baseEnd_311719 < baseStart_311719 := by decide
  rcases family_descends (prefixWord ++ tailWord_311719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311850 : List Nat := [3, 1, 4, 1, 1, 4, 2, 3]
def baseStart_311850 : Nat := 118140960795 + 311850 * 2 ^ 59
def prefixEnd_311850 : Nat := 4983230072969 + 3 ^ 40 * 311850 * 2
def baseEnd_311850 : Nat := 94891224950939329861235

theorem tailTrace_311850 : CollatzResearch.WordTrace tailWord_311850 prefixEnd_311850 94891224950939329861235 := by
  unfold tailWord_311850
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843525980057046146221251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7582735946818789723256669 2843525980057046146221251)
  ·
    refine ⟨4265288970085569219331877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2843525980057046146221251 4265288970085569219331877)
    ·
      refine ⟨799741681891044228624727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4265288970085569219331877 799741681891044228624727)
      ·
        refine ⟨1199612522836566342937091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799741681891044228624727 1199612522836566342937091)
        ·
          refine ⟨1799418784254849514405637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199612522836566342937091 1799418784254849514405637)
          ·
            refine ⟨337391022047784283951057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1799418784254849514405637 337391022047784283951057)
            ·
              refine ⟨253043266535838212963293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337391022047784283951057 253043266535838212963293)
              ·
                refine ⟨94891224950939329861235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253043266535838212963293 94891224950939329861235)
                ·
                  rfl

theorem cell19_311850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_311850 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311850 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311850 prefixEnd_311850 := by exact prefixLift 311850
  have htrace : WordTrace (prefixWord ++ tailWord_311850) baseStart_311850 baseEnd_311850 := by
    simpa [prefixWord, tailWord_311850, baseEnd_311850] using wordTrace_append hprefix tailTrace_311850
  have hstable : (prefixWord ++ tailWord_311850).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311850).length < 2 ^ (prefixWord ++ tailWord_311850).sum := by decide
  have hdescent : baseEnd_311850 < baseStart_311850 := by decide
  rcases family_descends (prefixWord ++ tailWord_311850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311873 : List Nat := [1, 2, 5, 1, 1, 2, 7]
def baseStart_311873 : Nat := 118140960795 + 311873 * 2 ^ 59
def prefixEnd_311873 : Nat := 4983230072969 + 3 ^ 40 * 311873 * 2
def baseEnd_311873 : Nat := 31632741167360697116687

theorem tailTrace_311873 : CollatzResearch.WordTrace tailWord_311873 prefixEnd_311873 31632741167360697116687 := by
  unfold tailWord_311873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11374942799144859512972273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7583295199429906341981515 11374942799144859512972273)
  ·
    refine ⟨8531207099358644634729205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11374942799144859512972273 8531207099358644634729205)
    ·
      refine ⟨799800665564872934505863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8531207099358644634729205 799800665564872934505863)
      ·
        refine ⟨1199700998347309401758795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799800665564872934505863 1199700998347309401758795)
        ·
          refine ⟨1799551497520964102638193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199700998347309401758795 1799551497520964102638193)
          ·
            refine ⟨1349663623140723076978645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799551497520964102638193 1349663623140723076978645)
            ·
              refine ⟨31632741167360697116687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1349663623140723076978645 31632741167360697116687)
              ·
                rfl

theorem cell19_311873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_311873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311873 prefixEnd_311873 := by exact prefixLift 311873
  have htrace : WordTrace (prefixWord ++ tailWord_311873) baseStart_311873 baseEnd_311873 := by
    simpa [prefixWord, tailWord_311873, baseEnd_311873] using wordTrace_append hprefix tailTrace_311873
  have hstable : (prefixWord ++ tailWord_311873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311873).length < 2 ^ (prefixWord ++ tailWord_311873).sum := by decide
  have hdescent : baseEnd_311873 < baseStart_311873 := by decide
  rcases family_descends (prefixWord ++ tailWord_311873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311892 : List Nat := [2, 4, 1, 1, 1, 3, 1, 6]
def baseStart_311892 : Nat := 118140960795 + 311892 * 2 ^ 59
def prefixEnd_311892 : Nat := 4983230072969 + 3 ^ 40 * 311892 * 2
def baseEnd_311892 : Nat := 94904004913895676927787

theorem tailTrace_311892 : CollatzResearch.WordTrace tailWord_311892 prefixEnd_311892 94904004913895676927787 := by
  unfold tailWord_311892
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687817893038012878956965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7583757190717350505275953 5687817893038012878956965)
  ·
    refine ⟨1066465854944627414804431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5687817893038012878956965 1066465854944627414804431)
    ·
      refine ⟨1599698782416941122206647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1066465854944627414804431 1599698782416941122206647)
      ·
        refine ⟨2399548173625411683309971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599698782416941122206647 2399548173625411683309971)
        ·
          refine ⟨3599322260438117524964957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399548173625411683309971 3599322260438117524964957)
          ·
            refine ⟨1349745847664294071861859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3599322260438117524964957 1349745847664294071861859)
            ·
              refine ⟨2024618771496441107792789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349745847664294071861859 2024618771496441107792789)
              ·
                refine ⟨94904004913895676927787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2024618771496441107792789 94904004913895676927787)
                ·
                  rfl

theorem cell19_311892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_311892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311892 prefixEnd_311892 := by exact prefixLift 311892
  have htrace : WordTrace (prefixWord ++ tailWord_311892) baseStart_311892 baseEnd_311892 := by
    simpa [prefixWord, tailWord_311892, baseEnd_311892] using wordTrace_append hprefix tailTrace_311892
  have hstable : (prefixWord ++ tailWord_311892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311892).length < 2 ^ (prefixWord ++ tailWord_311892).sum := by decide
  have hdescent : baseEnd_311892 < baseStart_311892 := by decide
  rcases family_descends (prefixWord ++ tailWord_311892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_311985 : List Nat := [1, 2, 2, 6, 1, 1, 6]
def baseStart_311985 : Nat := 118140960795 + 311985 * 2 ^ 59
def prefixEnd_311985 : Nat := 4983230072969 + 3 ^ 40 * 311985 * 2
def baseEnd_311985 : Nat := 31644101134433005620289

theorem tailTrace_311985 : CollatzResearch.WordTrace tailWord_311985 prefixEnd_311985 31644101134433005620289 := by
  unfold tailWord_311985
  simp only [CollatzResearch.WordTrace]
  refine ⟨11379027774739102641049409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7586018516492735094032939 11379027774739102641049409)
  ·
    refine ⟨8534270831054326980787057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11379027774739102641049409 8534270831054326980787057)
    ·
      refine ⟨6400703123290745235590293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8534270831054326980787057 6400703123290745235590293)
      ·
        refine ⟨300032958904253682918295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6400703123290745235590293 300032958904253682918295)
        ·
          refine ⟨450049438356380524377443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300032958904253682918295 450049438356380524377443)
          ·
            refine ⟨675074157534570786566165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450049438356380524377443 675074157534570786566165)
            ·
              refine ⟨31644101134433005620289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 675074157534570786566165 31644101134433005620289)
              ·
                rfl

theorem cell19_311985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 6].length) (baseStart_311985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_311985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_311985 prefixEnd_311985 := by exact prefixLift 311985
  have htrace : WordTrace (prefixWord ++ tailWord_311985) baseStart_311985 baseEnd_311985 := by
    simpa [prefixWord, tailWord_311985, baseEnd_311985] using wordTrace_append hprefix tailTrace_311985
  have hstable : (prefixWord ++ tailWord_311985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_311985).length < 2 ^ (prefixWord ++ tailWord_311985).sum := by decide
  have hdescent : baseEnd_311985 < baseStart_311985 := by decide
  rcases family_descends (prefixWord ++ tailWord_311985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312023 : List Nat := [1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_312023 : Nat := 118140960795 + 312023 * 2 ^ 59
def prefixEnd_312023 : Nat := 4983230072969 + 3 ^ 40 * 312023 * 2
def baseEnd_312023 : Nat := 94943866226926188016319

theorem tailTrace_312023 : CollatzResearch.WordTrace tailWord_312023 prefixEnd_312023 94943866226926188016319 := by
  unfold tailWord_312023
  simp only [CollatzResearch.WordTrace]
  refine ⟨11380413748601435130932723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7586942499067623420621815 11380413748601435130932723)
  ·
    refine ⟨17070620622902152696399085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11380413748601435130932723 17070620622902152696399085)
    ·
      refine ⟨6401482733588307261149657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17070620622902152696399085 6401482733588307261149657)
      ·
        refine ⟨4801112050191230445862243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6401482733588307261149657 4801112050191230445862243)
        ·
          refine ⟨7201668075286845668793365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4801112050191230445862243 7201668075286845668793365)
          ·
            refine ⟨337578191029070890724689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7201668075286845668793365 337578191029070890724689)
            ·
              refine ⟨253183643271803168043517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337578191029070890724689 253183643271803168043517)
              ·
                refine ⟨94943866226926188016319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253183643271803168043517 94943866226926188016319)
                ·
                  rfl

theorem cell19_312023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_312023 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312023 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312023 prefixEnd_312023 := by exact prefixLift 312023
  have htrace : WordTrace (prefixWord ++ tailWord_312023) baseStart_312023 baseEnd_312023 := by
    simpa [prefixWord, tailWord_312023, baseEnd_312023] using wordTrace_append hprefix tailTrace_312023
  have hstable : (prefixWord ++ tailWord_312023).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312023).length < 2 ^ (prefixWord ++ tailWord_312023).sum := by decide
  have hdescent : baseEnd_312023 < baseStart_312023 := by decide
  rcases family_descends (prefixWord ++ tailWord_312023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312116 : List Nat := [2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_312116 : Nat := 118140960795 + 312116 * 2 ^ 59
def prefixEnd_312116 : Nat := 4983230072969 + 3 ^ 40 * 312116 * 2
def baseEnd_312116 : Nat := 94972164716329527949399

theorem tailTrace_312116 : CollatzResearch.WordTrace tailWord_312116 prefixEnd_312116 94972164716329527949399 := by
  unfold tailWord_312116
  simp only [CollatzResearch.WordTrace]
  refine ⟨5691902868632256007034101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7589203824843008009378801 5691902868632256007034101)
  ·
    refine ⟨533615893934274000659447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5691902868632256007034101 533615893934274000659447)
    ·
      refine ⟨800423840901411000989171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533615893934274000659447 800423840901411000989171)
      ·
        refine ⟨1200635761352116501483757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800423840901411000989171 1200635761352116501483757)
        ·
          refine ⟨450238410507043688056409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1200635761352116501483757 450238410507043688056409)
          ·
            refine ⟨337678807880282766042307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450238410507043688056409 337678807880282766042307)
            ·
              refine ⟨506518211820424149063461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337678807880282766042307 506518211820424149063461)
              ·
                refine ⟨94972164716329527949399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506518211820424149063461 94972164716329527949399)
                ·
                  rfl

theorem cell19_312116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_312116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312116 prefixEnd_312116 := by exact prefixLift 312116
  have htrace : WordTrace (prefixWord ++ tailWord_312116) baseStart_312116 baseEnd_312116 := by
    simpa [prefixWord, tailWord_312116, baseEnd_312116] using wordTrace_append hprefix tailTrace_312116
  have hstable : (prefixWord ++ tailWord_312116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312116).length < 2 ^ (prefixWord ++ tailWord_312116).sum := by decide
  have hdescent : baseEnd_312116 < baseStart_312116 := by decide
  rcases family_descends (prefixWord ++ tailWord_312116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312160 : List Nat := [2, 1, 1, 3, 3, 1, 8]
def baseStart_312160 : Nat := 118140960795 + 312160 * 2 ^ 59
def prefixEnd_312160 : Nat := 4983230072969 + 3 ^ 40 * 312160 * 2
def baseEnd_312160 : Nat := 31661851082983487657167

theorem tailTrace_312160 : CollatzResearch.WordTrace tailWord_312160 prefixEnd_312160 31661851082983487657167 := by
  unfold tailWord_312160
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692705274552553764334967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7590273699403405019113289 5692705274552553764334967)
  ·
    refine ⟨8539057911828830646502451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5692705274552553764334967 8539057911828830646502451)
    ·
      refine ⟨12808586867743245969753677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8539057911828830646502451 12808586867743245969753677)
      ·
        refine ⟨4803220075403717238657629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12808586867743245969753677 4803220075403717238657629)
        ·
          refine ⟨1801207528276393964496611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4803220075403717238657629 1801207528276393964496611)
          ·
            refine ⟨2701811292414590946744917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801207528276393964496611 2701811292414590946744917)
            ·
              refine ⟨31661851082983487657167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2701811292414590946744917 31661851082983487657167)
              ·
                rfl

theorem cell19_312160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_312160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312160 prefixEnd_312160 := by exact prefixLift 312160
  have htrace : WordTrace (prefixWord ++ tailWord_312160) baseStart_312160 baseEnd_312160 := by
    simpa [prefixWord, tailWord_312160, baseEnd_312160] using wordTrace_append hprefix tailTrace_312160
  have hstable : (prefixWord ++ tailWord_312160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312160).length < 2 ^ (prefixWord ++ tailWord_312160).sum := by decide
  have hdescent : baseEnd_312160 < baseStart_312160 := by decide
  rcases family_descends (prefixWord ++ tailWord_312160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312190 : List Nat := [4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_312190 : Nat := 118140960795 + 312190 * 2 ^ 59
def prefixEnd_312190 : Nat := 4983230072969 + 3 ^ 40 * 312190 * 2
def baseEnd_312190 : Nat := 94994681793919282304753

theorem tailTrace_312190 : CollatzResearch.WordTrace tailWord_312190 prefixEnd_312190 94994681793919282304753 := by
  unfold tailWord_312190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423313092374552831532753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7591003159330948434841349 1423313092374552831532753)
  ·
    refine ⟨1067484819280914623649565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1423313092374552831532753 1067484819280914623649565)
    ·
      refine ⟨400306807230342983868587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1067484819280914623649565 400306807230342983868587)
      ·
        refine ⟨600460210845514475802881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400306807230342983868587 600460210845514475802881)
        ·
          refine ⟨450345158134135856852161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600460210845514475802881 450345158134135856852161)
          ·
            refine ⟨337758868600601892639121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450345158134135856852161 337758868600601892639121)
            ·
              refine ⟨253319151450451419479341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337758868600601892639121 253319151450451419479341)
              ·
                refine ⟨94994681793919282304753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253319151450451419479341 94994681793919282304753)
                ·
                  rfl

theorem cell19_312190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_312190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312190 prefixEnd_312190 := by exact prefixLift 312190
  have htrace : WordTrace (prefixWord ++ tailWord_312190) baseStart_312190 baseEnd_312190 := by
    simpa [prefixWord, tailWord_312190, baseEnd_312190] using wordTrace_append hprefix tailTrace_312190
  have hstable : (prefixWord ++ tailWord_312190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312190).length < 2 ^ (prefixWord ++ tailWord_312190).sum := by decide
  have hdescent : baseEnd_312190 < baseStart_312190 := by decide
  rcases family_descends (prefixWord ++ tailWord_312190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312306 : List Nat := [3, 2, 1, 5, 1, 1, 3, 3]
def baseStart_312306 : Nat := 118140960795 + 312306 * 2 ^ 59
def prefixEnd_312306 : Nat := 4983230072969 + 3 ^ 40 * 312306 * 2
def baseEnd_312306 : Nat := 95029978834465383726659

theorem tailTrace_312306 : CollatzResearch.WordTrace tailWord_312306 prefixEnd_312306 95029978834465383726659 := by
  unfold tailWord_312306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847683901644043615871193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7593823737717449642323181 2847683901644043615871193)
  ·
    refine ⟨2135762926233032711903395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2847683901644043615871193 2135762926233032711903395)
    ·
      refine ⟨3203644389349549067855093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2135762926233032711903395 3203644389349549067855093)
      ·
        refine ⟨300341661501520225111415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3203644389349549067855093 300341661501520225111415)
        ·
          refine ⟨450512492252280337667123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300341661501520225111415 450512492252280337667123)
          ·
            refine ⟨675768738378420506500685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450512492252280337667123 675768738378420506500685)
            ·
              refine ⟨253413276891907689937757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675768738378420506500685 253413276891907689937757)
              ·
                refine ⟨95029978834465383726659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253413276891907689937757 95029978834465383726659)
                ·
                  rfl

theorem cell19_312306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_312306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312306 prefixEnd_312306 := by exact prefixLift 312306
  have htrace : WordTrace (prefixWord ++ tailWord_312306) baseStart_312306 baseEnd_312306 := by
    simpa [prefixWord, tailWord_312306, baseEnd_312306] using wordTrace_append hprefix tailTrace_312306
  have hstable : (prefixWord ++ tailWord_312306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312306).length < 2 ^ (prefixWord ++ tailWord_312306).sum := by decide
  have hdescent : baseEnd_312306 < baseStart_312306 := by decide
  rcases family_descends (prefixWord ++ tailWord_312306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312331 : List Nat := [1, 1, 1, 1, 6, 3, 6]
def baseStart_312331 : Nat := 118140960795 + 312331 * 2 ^ 59
def prefixEnd_312331 : Nat := 4983230072969 + 3 ^ 40 * 312331 * 2
def baseEnd_312331 : Nat := 31679195318424244390345

theorem tailTrace_312331 : CollatzResearch.WordTrace tailWord_312331 prefixEnd_312331 31679195318424244390345 := by
  unfold tailWord_312331
  simp only [CollatzResearch.WordTrace]
  refine ⟨11391647431485603733144847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7594431620990402488763231 11391647431485603733144847)
  ·
    refine ⟨17087471147228405599717271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11391647431485603733144847 17087471147228405599717271)
    ·
      refine ⟨25631206720842608399575907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17087471147228405599717271 25631206720842608399575907)
      ·
        refine ⟨38446810081263912599363861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25631206720842608399575907 38446810081263912599363861)
        ·
          refine ⟨1802194222559245903095181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38446810081263912599363861 1802194222559245903095181)
          ·
            refine ⟨675822833459717213660693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1802194222559245903095181 675822833459717213660693)
            ·
              refine ⟨31679195318424244390345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 675822833459717213660693 31679195318424244390345)
              ·
                rfl

theorem cell19_312331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_312331 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312331 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312331 prefixEnd_312331 := by exact prefixLift 312331
  have htrace : WordTrace (prefixWord ++ tailWord_312331) baseStart_312331 baseEnd_312331 := by
    simpa [prefixWord, tailWord_312331, baseEnd_312331] using wordTrace_append hprefix tailTrace_312331
  have hstable : (prefixWord ++ tailWord_312331).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312331).length < 2 ^ (prefixWord ++ tailWord_312331).sum := by decide
  have hdescent : baseEnd_312331 < baseStart_312331 := by decide
  rcases family_descends (prefixWord ++ tailWord_312331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312369 : List Nat := [1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_312369 : Nat := 118140960795 + 312369 * 2 ^ 59
def prefixEnd_312369 : Nat := 4983230072969 + 3 ^ 40 * 312369 * 2
def baseEnd_312369 : Nat := 95049148778899904326487

theorem tailTrace_312369 : CollatzResearch.WordTrace tailWord_312369 prefixEnd_312369 95049148778899904326487 := by
  unfold tailWord_312369
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393033405347936223028161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7595355603565290815352107 11393033405347936223028161)
  ·
    refine ⟨8544775054010952167271121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11393033405347936223028161 8544775054010952167271121)
    ·
      refine ⟨6408581290508214125453341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8544775054010952167271121 6408581290508214125453341)
      ·
        refine ⟨2403217983940580297045003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6408581290508214125453341 2403217983940580297045003)
        ·
          refine ⟨3604826975910870445567505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403217983940580297045003 3604826975910870445567505)
          ·
            refine ⟨2703620231933152834175629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3604826975910870445567505 2703620231933152834175629)
            ·
              refine ⟨1013857586974932312815861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2703620231933152834175629 1013857586974932312815861)
              ·
                refine ⟨95049148778899904326487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1013857586974932312815861 95049148778899904326487)
                ·
                  rfl

theorem cell19_312369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_312369 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312369 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312369 prefixEnd_312369 := by exact prefixLift 312369
  have htrace : WordTrace (prefixWord ++ tailWord_312369) baseStart_312369 baseEnd_312369 := by
    simpa [prefixWord, tailWord_312369, baseEnd_312369] using wordTrace_append hprefix tailTrace_312369
  have hstable : (prefixWord ++ tailWord_312369).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312369).length < 2 ^ (prefixWord ++ tailWord_312369).sum := by decide
  have hdescent : baseEnd_312369 < baseStart_312369 := by decide
  rcases family_descends (prefixWord ++ tailWord_312369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312462 : List Nat := [4, 1, 1, 3, 2, 1, 3, 4]
def baseStart_312462 : Nat := 118140960795 + 312462 * 2 ^ 59
def prefixEnd_312462 : Nat := 4983230072969 + 3 ^ 40 * 312462 * 2
def baseEnd_312462 : Nat := 95077447268303244259567

theorem tailTrace_312462 : CollatzResearch.WordTrace tailWord_312462 prefixEnd_312462 95077447268303244259567 := by
  unfold tailWord_312462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424553174251376638270455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7597616929340675404109093 1424553174251376638270455)
  ·
    refine ⟨2136829761377064957405683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424553174251376638270455 2136829761377064957405683)
    ·
      refine ⟨3205244642065597436108525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2136829761377064957405683 3205244642065597436108525)
      ·
        refine ⟨1201966740774599038540697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3205244642065597436108525 1201966740774599038540697)
        ·
          refine ⟨901475055580949278905523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201966740774599038540697 901475055580949278905523)
          ·
            refine ⟨1352212583371423918358285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901475055580949278905523 1352212583371423918358285)
            ·
              refine ⟨507079718764283969384357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1352212583371423918358285 507079718764283969384357)
              ·
                refine ⟨95077447268303244259567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507079718764283969384357 95077447268303244259567)
                ·
                  rfl

theorem cell19_312462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_312462 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312462 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312462 prefixEnd_312462 := by exact prefixLift 312462
  have htrace : WordTrace (prefixWord ++ tailWord_312462) baseStart_312462 baseEnd_312462 := by
    simpa [prefixWord, tailWord_312462, baseEnd_312462] using wordTrace_append hprefix tailTrace_312462
  have hstable : (prefixWord ++ tailWord_312462).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312462).length < 2 ^ (prefixWord ++ tailWord_312462).sum := by decide
  have hdescent : baseEnd_312462 < baseStart_312462 := by decide
  rcases family_descends (prefixWord ++ tailWord_312462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312479 : List Nat := [1, 1, 2, 6, 2, 1, 3, 3]
def baseStart_312479 : Nat := 118140960795 + 312479 * 2 ^ 59
def prefixEnd_312479 : Nat := 4983230072969 + 3 ^ 40 * 312479 * 2
def baseEnd_312479 : Nat := 95082620110452241881743

theorem tailTrace_312479 : CollatzResearch.WordTrace tailWord_312479 prefixEnd_312479 95082620110452241881743 := by
  unfold tailWord_312479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397045434949425009532491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7598030289966283339688327 11397045434949425009532491)
  ·
    refine ⟨17095568152424137514298737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11397045434949425009532491 17095568152424137514298737)
    ·
      refine ⟨12821676114318103135724053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17095568152424137514298737 12821676114318103135724053)
      ·
        refine ⟨601016067858661084487065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12821676114318103135724053 601016067858661084487065)
        ·
          refine ⟨450762050893995813365299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601016067858661084487065 450762050893995813365299)
          ·
            refine ⟨676143076340993720047949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450762050893995813365299 676143076340993720047949)
            ·
              refine ⟨253553653627872645017981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676143076340993720047949 253553653627872645017981)
              ·
                refine ⟨95082620110452241881743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253553653627872645017981 95082620110452241881743)
                ·
                  rfl

theorem cell19_312479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 3, 3].length) (baseStart_312479 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312479 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312479 prefixEnd_312479 := by exact prefixLift 312479
  have htrace : WordTrace (prefixWord ++ tailWord_312479) baseStart_312479 baseEnd_312479 := by
    simpa [prefixWord, tailWord_312479, baseEnd_312479] using wordTrace_append hprefix tailTrace_312479
  have hstable : (prefixWord ++ tailWord_312479).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312479).length < 2 ^ (prefixWord ++ tailWord_312479).sum := by decide
  have hdescent : baseEnd_312479 < baseStart_312479 := by decide
  rcases family_descends (prefixWord ++ tailWord_312479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312481 : List Nat := [1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_312481 : Nat := 118140960795 + 312481 * 2 ^ 59
def prefixEnd_312481 : Nat := 4983230072969 + 3 ^ 40 * 312481 * 2
def baseEnd_312481 : Nat := 95083228680116829837293

theorem tailTrace_312481 : CollatzResearch.WordTrace tailWord_312481 prefixEnd_312481 95083228680116829837293 := by
  unfold tailWord_312481
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397118380942179351105297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7598078920628119567403531 11397118380942179351105297)
  ·
    refine ⟨8547838785706634513328973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11397118380942179351105297 8547838785706634513328973)
    ·
      refine ⟨3205439544639987942498365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8547838785706634513328973 3205439544639987942498365)
      ·
        refine ⟨1202039829239995478436887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3205439544639987942498365 1202039829239995478436887)
        ·
          refine ⟨1803059743859993217655331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202039829239995478436887 1803059743859993217655331)
          ·
            refine ⟨2704589615789989826482997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803059743859993217655331 2704589615789989826482997)
            ·
              refine ⟨253555276480311546232781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2704589615789989826482997 253555276480311546232781)
              ·
                refine ⟨95083228680116829837293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253555276480311546232781 95083228680116829837293)
                ·
                  rfl

theorem cell19_312481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_312481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312481 prefixEnd_312481 := by exact prefixLift 312481
  have htrace : WordTrace (prefixWord ++ tailWord_312481) baseStart_312481 baseEnd_312481 := by
    simpa [prefixWord, tailWord_312481, baseEnd_312481] using wordTrace_append hprefix tailTrace_312481
  have hstable : (prefixWord ++ tailWord_312481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312481).length < 2 ^ (prefixWord ++ tailWord_312481).sum := by decide
  have hdescent : baseEnd_312481 < baseStart_312481 := by decide
  rcases family_descends (prefixWord ++ tailWord_312481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312532 : List Nat := [2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_312532 : Nat := 118140960795 + 312532 * 2 ^ 59
def prefixEnd_312532 : Nat := 4983230072969 + 3 ^ 40 * 312532 * 2
def baseEnd_312532 : Nat := 95098747206563822703821

theorem tailTrace_312532 : CollatzResearch.WordTrace tailWord_312532 prefixEnd_312532 95098747206563822703821 := by
  unfold tailWord_312532
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699489251878707530605925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7599319002504943374141233 5699489251878707530605925)
  ·
    refine ⟨1068654234727257661988611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5699489251878707530605925 1068654234727257661988611)
    ·
      refine ⟨1602981352090886492982917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068654234727257661988611 1602981352090886492982917)
      ·
        refine ⟨300559003517041217434297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1602981352090886492982917 300559003517041217434297)
        ·
          refine ⟨225419252637780913075723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300559003517041217434297 225419252637780913075723)
          ·
            refine ⟨338128878956671369613585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225419252637780913075723 338128878956671369613585)
            ·
              refine ⟨253596659217503527210189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338128878956671369613585 253596659217503527210189)
              ·
                refine ⟨95098747206563822703821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253596659217503527210189 95098747206563822703821)
                ·
                  rfl

theorem cell19_312532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_312532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312532 prefixEnd_312532 := by exact prefixLift 312532
  have htrace : WordTrace (prefixWord ++ tailWord_312532) baseStart_312532 baseEnd_312532 := by
    simpa [prefixWord, tailWord_312532, baseEnd_312532] using wordTrace_append hprefix tailTrace_312532
  have hstable : (prefixWord ++ tailWord_312532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312532).length < 2 ^ (prefixWord ++ tailWord_312532).sum := by decide
  have hdescent : baseEnd_312532 < baseStart_312532 := by decide
  rcases family_descends (prefixWord ++ tailWord_312532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312536 : List Nat := [2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_312536 : Nat := 118140960795 + 312536 * 2 ^ 59
def prefixEnd_312536 : Nat := 4983230072969 + 3 ^ 40 * 312536 * 2
def baseEnd_312536 : Nat := 95099964345892998614921

theorem tailTrace_312536 : CollatzResearch.WordTrace tailWord_312536 prefixEnd_312536 95099964345892998614921 := by
  unfold tailWord_312536
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699562197871461872178731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7599416263828615829571641 5699562197871461872178731)
  ·
    refine ⟨8549343296807192808268097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5699562197871461872178731 8549343296807192808268097)
    ·
      refine ⟨6412007472605394606201073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8549343296807192808268097 6412007472605394606201073)
      ·
        refine ⟨4809005604454045954650805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6412007472605394606201073 4809005604454045954650805)
        ·
          refine ⟨450844275417566808248513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4809005604454045954650805 450844275417566808248513)
          ·
            refine ⟨338133206563175106186385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450844275417566808248513 338133206563175106186385)
            ·
              refine ⟨253599904922381329639789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338133206563175106186385 253599904922381329639789)
              ·
                refine ⟨95099964345892998614921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253599904922381329639789 95099964345892998614921)
                ·
                  rfl

theorem cell19_312536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_312536 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312536 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312536 prefixEnd_312536 := by exact prefixLift 312536
  have htrace : WordTrace (prefixWord ++ tailWord_312536) baseStart_312536 baseEnd_312536 := by
    simpa [prefixWord, tailWord_312536, baseEnd_312536] using wordTrace_append hprefix tailTrace_312536
  have hstable : (prefixWord ++ tailWord_312536).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312536).length < 2 ^ (prefixWord ++ tailWord_312536).sum := by decide
  have hdescent : baseEnd_312536 < baseStart_312536 := by decide
  rcases family_descends (prefixWord ++ tailWord_312536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312557 : List Nat := [1, 5, 1, 2, 2, 3, 5]
def baseStart_312557 : Nat := 118140960795 + 312557 * 2 ^ 59
def prefixEnd_312557 : Nat := 4983230072969 + 3 ^ 40 * 312557 * 2
def baseEnd_312557 : Nat := 31702118109123724049399

theorem tailTrace_312557 : CollatzResearch.WordTrace tailWord_312557 prefixEnd_312557 31702118109123724049399 := by
  unfold tailWord_312557
  simp only [CollatzResearch.WordTrace]
  refine ⟨11399890328666844330871925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7599926885777896220581283 11399890328666844330871925)
  ·
    refine ⟨1068739718312516656019243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11399890328666844330871925 1068739718312516656019243)
    ·
      refine ⟨1603109577468774984028865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068739718312516656019243 1603109577468774984028865)
      ·
        refine ⟨1202332183101581238021649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603109577468774984028865 1202332183101581238021649)
        ·
          refine ⟨901749137326185928516237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202332183101581238021649 901749137326185928516237)
          ·
            refine ⟨338155926497319723193589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 901749137326185928516237 338155926497319723193589)
            ·
              refine ⟨31702118109123724049399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338155926497319723193589 31702118109123724049399)
              ·
                rfl

theorem cell19_312557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_312557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312557 prefixEnd_312557 := by exact prefixLift 312557
  have htrace : WordTrace (prefixWord ++ tailWord_312557) baseStart_312557 baseEnd_312557 := by
    simpa [prefixWord, tailWord_312557, baseEnd_312557] using wordTrace_append hprefix tailTrace_312557
  have hstable : (prefixWord ++ tailWord_312557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312557).length < 2 ^ (prefixWord ++ tailWord_312557).sum := by decide
  have hdescent : baseEnd_312557 < baseStart_312557 := by decide
  rcases family_descends (prefixWord ++ tailWord_312557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312616 : List Nat := [2, 1, 5, 1, 2, 8]
def baseStart_312616 : Nat := 118140960795 + 312616 * 2 ^ 59
def prefixEnd_312616 : Nat := 4983230072969 + 3 ^ 40 * 312616 * 2
def baseEnd_312616 : Nat := 10569367459164057426325

theorem tailTrace_312616 : CollatzResearch.WordTrace tailWord_312616 prefixEnd_312616 10569367459164057426325 := by
  unfold tailWord_312616
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701021117726548703634851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7601361490302064938179801 5701021117726548703634851)
  ·
    refine ⟨8551531676589823055452277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5701021117726548703634851 8551531676589823055452277)
    ·
      refine ⟨801706094680295911448651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8551531676589823055452277 801706094680295911448651)
      ·
        refine ⟨1202559142020443867172977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801706094680295911448651 1202559142020443867172977)
        ·
          refine ⟨901919356515332900379733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202559142020443867172977 901919356515332900379733)
          ·
            refine ⟨10569367459164057426325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 901919356515332900379733 10569367459164057426325)
            ·
              rfl

theorem cell19_312616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_312616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312616 prefixEnd_312616 := by exact prefixLift 312616
  have htrace : WordTrace (prefixWord ++ tailWord_312616) baseStart_312616 baseEnd_312616 := by
    simpa [prefixWord, tailWord_312616, baseEnd_312616] using wordTrace_append hprefix tailTrace_312616
  have hstable : (prefixWord ++ tailWord_312616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312616).length < 2 ^ (prefixWord ++ tailWord_312616).sum := by decide
  have hdescent : baseEnd_312616 < baseStart_312616 := by decide
  rcases family_descends (prefixWord ++ tailWord_312616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312646 : List Nat := [6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_312646 : Nat := 118140960795 + 312646 * 2 ^ 59
def prefixEnd_312646 : Nat := 4983230072969 + 3 ^ 40 * 312646 * 2
def baseEnd_312646 : Nat := 95133435677445336170177

theorem tailTrace_312646 : CollatzResearch.WordTrace tailWord_312646 prefixEnd_312646 95133435677445336170177 := by
  unfold tailWord_312646
  simp only [CollatzResearch.WordTrace]
  refine ⟨356348013292012891589431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7602090950229608353907861 356348013292012891589431)
  ·
    refine ⟨534522019938019337384147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 356348013292012891589431 534522019938019337384147)
    ·
      refine ⟨801783029907029006076221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534522019938019337384147 801783029907029006076221)
      ·
        refine ⟨300668636215135877278583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 801783029907029006076221 300668636215135877278583)
        ·
          refine ⟨451002954322703815917875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300668636215135877278583 451002954322703815917875)
          ·
            refine ⟨676504431484055723876813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451002954322703815917875 676504431484055723876813)
            ·
              refine ⟨253689161806520896453805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676504431484055723876813 253689161806520896453805)
              ·
                refine ⟨95133435677445336170177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253689161806520896453805 95133435677445336170177)
                ·
                  rfl

theorem cell19_312646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_312646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312646 prefixEnd_312646 := by exact prefixLift 312646
  have htrace : WordTrace (prefixWord ++ tailWord_312646) baseStart_312646 baseEnd_312646 := by
    simpa [prefixWord, tailWord_312646, baseEnd_312646] using wordTrace_append hprefix tailTrace_312646
  have hstable : (prefixWord ++ tailWord_312646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312646).length < 2 ^ (prefixWord ++ tailWord_312646).sum := by decide
  have hdescent : baseEnd_312646 < baseStart_312646 := by decide
  rcases family_descends (prefixWord ++ tailWord_312646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312652 : List Nat := [2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_312652 : Nat := 118140960795 + 312652 * 2 ^ 59
def prefixEnd_312652 : Nat := 4983230072969 + 3 ^ 40 * 312652 * 2
def baseEnd_312652 : Nat := 95135261386439100036827

theorem tailTrace_312652 : CollatzResearch.WordTrace tailWord_312652 prefixEnd_312652 95135261386439100036827 := by
  unfold tailWord_312652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701677631661337777790105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7602236842215117037053473 5701677631661337777790105)
  ·
    refine ⟨4276258223746003333342579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5701677631661337777790105 4276258223746003333342579)
    ·
      refine ⟨6414387335619005000013869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276258223746003333342579 6414387335619005000013869)
      ·
        refine ⟨2405395250857126875005201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6414387335619005000013869 2405395250857126875005201)
        ·
          refine ⟨1804046438142845156253901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405395250857126875005201 1804046438142845156253901)
          ·
            refine ⟨676517414303566933595213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804046438142845156253901 676517414303566933595213)
            ·
              refine ⟨253694030363837600098205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676517414303566933595213 253694030363837600098205)
              ·
                refine ⟨95135261386439100036827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253694030363837600098205 95135261386439100036827)
                ·
                  rfl

theorem cell19_312652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_312652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312652 prefixEnd_312652 := by exact prefixLift 312652
  have htrace : WordTrace (prefixWord ++ tailWord_312652) baseStart_312652 baseEnd_312652 := by
    simpa [prefixWord, tailWord_312652, baseEnd_312652] using wordTrace_append hprefix tailTrace_312652
  have hstable : (prefixWord ++ tailWord_312652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312652).length < 2 ^ (prefixWord ++ tailWord_312652).sum := by decide
  have hdescent : baseEnd_312652 < baseStart_312652 := by decide
  rcases family_descends (prefixWord ++ tailWord_312652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312705 : List Nat := [1, 2, 4, 3, 3, 1, 2, 3]
def baseStart_312705 : Nat := 118140960795 + 312705 * 2 ^ 59
def prefixEnd_312705 : Nat := 4983230072969 + 3 ^ 40 * 312705 * 2
def baseEnd_312705 : Nat := 95151388482550680858905

theorem tailTrace_312705 : CollatzResearch.WordTrace tailWord_312705 prefixEnd_312705 95151388482550680858905 := by
  unfold tailWord_312705
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405288332130665607259569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7603525554753777071506379 11405288332130665607259569)
  ·
    refine ⟨8553966249097999205444677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11405288332130665607259569 8553966249097999205444677)
    ·
      refine ⟨1603868671705874851020877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8553966249097999205444677 1603868671705874851020877)
      ·
        refine ⟨601450751889703069132829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1603868671705874851020877 601450751889703069132829)
        ·
          refine ⟨225544031958638650924811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 601450751889703069132829 225544031958638650924811)
          ·
            refine ⟨338316047937957976387217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225544031958638650924811 338316047937957976387217)
            ·
              refine ⟨253737035953468482290413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338316047937957976387217 253737035953468482290413)
              ·
                refine ⟨95151388482550680858905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253737035953468482290413 95151388482550680858905)
                ·
                  rfl

theorem cell19_312705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_312705 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312705 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312705 prefixEnd_312705 := by exact prefixLift 312705
  have htrace : WordTrace (prefixWord ++ tailWord_312705) baseStart_312705 baseEnd_312705 := by
    simpa [prefixWord, tailWord_312705, baseEnd_312705] using wordTrace_append hprefix tailTrace_312705
  have hstable : (prefixWord ++ tailWord_312705).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312705).length < 2 ^ (prefixWord ++ tailWord_312705).sum := by decide
  have hdescent : baseEnd_312705 < baseStart_312705 := by decide
  rcases family_descends (prefixWord ++ tailWord_312705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312711 : List Nat := [1, 1, 4, 2, 2, 3, 1, 5]
def baseStart_312711 : Nat := 118140960795 + 312711 * 2 ^ 59
def prefixEnd_312711 : Nat := 4983230072969 + 3 ^ 40 * 312711 * 2
def baseEnd_312711 : Nat := 95153214191544444725555

theorem tailTrace_312711 : CollatzResearch.WordTrace tailWord_312711 prefixEnd_312711 95153214191544444725555 := by
  unfold tailWord_312711
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405507170108928631977987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7603671446739285754651991 11405507170108928631977987)
  ·
    refine ⟨17108260755163392947966981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405507170108928631977987 17108260755163392947966981)
    ·
      refine ⟨3207798891593136177743809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17108260755163392947966981 3207798891593136177743809)
      ·
        refine ⟨2405849168694852133307857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3207798891593136177743809 2405849168694852133307857)
        ·
          refine ⟨1804386876521139099980893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405849168694852133307857 1804386876521139099980893)
          ·
            refine ⟨676645078695427162492835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804386876521139099980893 676645078695427162492835)
            ·
              refine ⟨1014967618043140743739253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676645078695427162492835 1014967618043140743739253)
              ·
                refine ⟨95153214191544444725555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1014967618043140743739253 95153214191544444725555)
                ·
                  rfl

theorem cell19_312711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_312711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312711 prefixEnd_312711 := by exact prefixLift 312711
  have htrace : WordTrace (prefixWord ++ tailWord_312711) baseStart_312711 baseEnd_312711 := by
    simpa [prefixWord, tailWord_312711, baseEnd_312711] using wordTrace_append hprefix tailTrace_312711
  have hstable : (prefixWord ++ tailWord_312711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312711).length < 2 ^ (prefixWord ++ tailWord_312711).sum := by decide
  have hdescent : baseEnd_312711 < baseStart_312711 := by decide
  rcases family_descends (prefixWord ++ tailWord_312711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312728 : List Nat := [2, 1, 2, 5, 2, 2, 5]
def baseStart_312728 : Nat := 118140960795 + 312728 * 2 ^ 59
def prefixEnd_312728 : Nat := 4983230072969 + 3 ^ 40 * 312728 * 2
def baseEnd_312728 : Nat := 31719462344564480782577

theorem tailTrace_312728 : CollatzResearch.WordTrace tailWord_312728 prefixEnd_312728 31719462344564480782577 := by
  unfold tailWord_312728
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703063605523670267673419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7604084807364893690231225 5703063605523670267673419)
  ·
    refine ⟨8554595408285505401510129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5703063605523670267673419 8554595408285505401510129)
    ·
      refine ⟨6415946556214129051132597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8554595408285505401510129 6415946556214129051132597)
      ·
        refine ⟨601494989645074598543681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6415946556214129051132597 601494989645074598543681)
        ·
          refine ⟨451121242233805948907761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601494989645074598543681 451121242233805948907761)
          ·
            refine ⟨338340931675354461680821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 451121242233805948907761 338340931675354461680821)
            ·
              refine ⟨31719462344564480782577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338340931675354461680821 31719462344564480782577)
              ·
                rfl

theorem cell19_312728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_312728 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312728 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312728 prefixEnd_312728 := by exact prefixLift 312728
  have htrace : WordTrace (prefixWord ++ tailWord_312728) baseStart_312728 baseEnd_312728 := by
    simpa [prefixWord, tailWord_312728, baseEnd_312728] using wordTrace_append hprefix tailTrace_312728
  have hstable : (prefixWord ++ tailWord_312728).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312728).length < 2 ^ (prefixWord ++ tailWord_312728).sum := by decide
  have hdescent : baseEnd_312728 < baseStart_312728 := by decide
  rcases family_descends (prefixWord ++ tailWord_312728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312821 : List Nat := [1, 3, 5, 1, 1, 2, 3, 3]
def baseStart_312821 : Nat := 118140960795 + 312821 * 2 ^ 59
def prefixEnd_312821 : Nat := 4983230072969 + 3 ^ 40 * 312821 * 2
def baseEnd_312821 : Nat := 95186685523096782280811

theorem tailTrace_312821 : CollatzResearch.WordTrace tailWord_312821 prefixEnd_312821 95186685523096782280811 := by
  unfold tailWord_312821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11409519199710417418482317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7606346133140278278988211 11409519199710417418482317)
  ·
    refine ⟨4278569699891406531930869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11409519199710417418482317 4278569699891406531930869)
    ·
      refine ⟨401115909364819362368519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4278569699891406531930869 401115909364819362368519)
      ·
        refine ⟨601673864047229043552779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401115909364819362368519 601673864047229043552779)
        ·
          refine ⟨902510796070843565329169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601673864047229043552779 902510796070843565329169)
          ·
            refine ⟨676883097053132673996877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902510796070843565329169 676883097053132673996877)
            ·
              refine ⟨253831161394924752748829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676883097053132673996877 253831161394924752748829)
              ·
                refine ⟨95186685523096782280811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253831161394924752748829 95186685523096782280811)
                ·
                  rfl

theorem cell19_312821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 3].length) (baseStart_312821 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312821 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312821 prefixEnd_312821 := by exact prefixLift 312821
  have htrace : WordTrace (prefixWord ++ tailWord_312821) baseStart_312821 baseEnd_312821 := by
    simpa [prefixWord, tailWord_312821, baseEnd_312821] using wordTrace_append hprefix tailTrace_312821
  have hstable : (prefixWord ++ tailWord_312821).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312821).length < 2 ^ (prefixWord ++ tailWord_312821).sum := by decide
  have hdescent : baseEnd_312821 < baseStart_312821 := by decide
  rcases family_descends (prefixWord ++ tailWord_312821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312838 : List Nat := [6, 2, 1, 1, 2, 1, 6]
def baseStart_312838 : Nat := 118140960795 + 312838 * 2 ^ 59
def prefixEnd_312838 : Nat := 4983230072969 + 3 ^ 40 * 312838 * 2
def baseEnd_312838 : Nat := 31730619455081926634329

theorem tailTrace_312838 : CollatzResearch.WordTrace tailWord_312838 prefixEnd_312838 31730619455081926634329 := by
  unfold tailWord_312838
  simp only [CollatzResearch.WordTrace]
  refine ⟨356566851270275916307849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7606759493765886214567445 356566851270275916307849)
  ·
    refine ⟨267425138452706937230887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 356566851270275916307849 267425138452706937230887)
    ·
      refine ⟨401137707679060405846331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267425138452706937230887 401137707679060405846331)
      ·
        refine ⟨601706561518590608769497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401137707679060405846331 601706561518590608769497)
        ·
          refine ⟨451279921138942956577123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601706561518590608769497 451279921138942956577123)
          ·
            refine ⟨676919881708414434865685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451279921138942956577123 676919881708414434865685)
            ·
              refine ⟨31730619455081926634329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 676919881708414434865685 31730619455081926634329)
              ·
                rfl

theorem cell19_312838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_312838 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312838 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312838 prefixEnd_312838 := by exact prefixLift 312838
  have htrace : WordTrace (prefixWord ++ tailWord_312838) baseStart_312838 baseEnd_312838 := by
    simpa [prefixWord, tailWord_312838, baseEnd_312838] using wordTrace_append hprefix tailTrace_312838
  have hstable : (prefixWord ++ tailWord_312838).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312838).length < 2 ^ (prefixWord ++ tailWord_312838).sum := by decide
  have hdescent : baseEnd_312838 < baseStart_312838 := by decide
  rcases family_descends (prefixWord ++ tailWord_312838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312844 : List Nat := [2, 2, 1, 2, 5, 1, 6]
def baseStart_312844 : Nat := 118140960795 + 312844 * 2 ^ 59
def prefixEnd_312844 : Nat := 4983230072969 + 3 ^ 40 * 312844 * 2
def baseEnd_312844 : Nat := 31731228024746514589879

theorem tailTrace_312844 : CollatzResearch.WordTrace tailWord_312844 prefixEnd_312844 31731228024746514589879 := by
  unfold tailWord_312844
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705179039313546173284793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7606905385751394897713057 5705179039313546173284793)
  ·
    refine ⟨4278884279485159629963595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5705179039313546173284793 4278884279485159629963595)
    ·
      refine ⟨6418326419227739444945393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278884279485159629963595 6418326419227739444945393)
      ·
        refine ⟨4813744814420804583709045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6418326419227739444945393 4813744814420804583709045)
        ·
          refine ⟨451288576351950429722723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4813744814420804583709045 451288576351950429722723)
          ·
            refine ⟨676932864527925644584085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451288576351950429722723 676932864527925644584085)
            ·
              refine ⟨31731228024746514589879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 676932864527925644584085 31731228024746514589879)
              ·
                rfl

theorem cell19_312844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_312844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312844 prefixEnd_312844 := by exact prefixLift 312844
  have htrace : WordTrace (prefixWord ++ tailWord_312844) baseStart_312844 baseEnd_312844 := by
    simpa [prefixWord, tailWord_312844, baseEnd_312844] using wordTrace_append hprefix tailTrace_312844
  have hstable : (prefixWord ++ tailWord_312844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312844).length < 2 ^ (prefixWord ++ tailWord_312844).sum := by decide
  have hdescent : baseEnd_312844 < baseStart_312844 := by decide
  rcases family_descends (prefixWord ++ tailWord_312844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_312878 : List Nat := [4, 1, 3, 1, 2, 3, 2, 3]
def baseStart_312878 : Nat := 118140960795 + 312878 * 2 ^ 59
def prefixEnd_312878 : Nat := 4983230072969 + 3 ^ 40 * 312878 * 2
def baseEnd_312878 : Nat := 95204029758537539013989

theorem tailTrace_312878 : CollatzResearch.WordTrace tailWord_312878 prefixEnd_312878 95204029758537539013989 := by
  unfold tailWord_312878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426449770062989519163411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7607732107002610768871525 1426449770062989519163411)
  ·
    refine ⟨2139674655094484278745117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426449770062989519163411 2139674655094484278745117)
    ·
      refine ⟨802377995660431604529419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2139674655094484278745117 802377995660431604529419)
      ·
        refine ⟨1203566993490647406794129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802377995660431604529419 1203566993490647406794129)
        ·
          refine ⟨902675245117985555095597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203566993490647406794129 902675245117985555095597)
          ·
            refine ⟨338503216919244583160849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 902675245117985555095597 338503216919244583160849)
            ·
              refine ⟨253877412689433437370637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338503216919244583160849 253877412689433437370637)
              ·
                refine ⟨95204029758537539013989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253877412689433437370637 95204029758537539013989)
                ·
                  rfl

theorem cell19_312878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_312878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_312878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_312878 prefixEnd_312878 := by exact prefixLift 312878
  have htrace : WordTrace (prefixWord ++ tailWord_312878) baseStart_312878 baseEnd_312878 := by
    simpa [prefixWord, tailWord_312878, baseEnd_312878] using wordTrace_append hprefix tailTrace_312878
  have hstable : (prefixWord ++ tailWord_312878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_312878).length < 2 ^ (prefixWord ++ tailWord_312878).sum := by decide
  have hdescent : baseEnd_312878 < baseStart_312878 := by decide
  rcases family_descends (prefixWord ++ tailWord_312878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313055 : List Nat := [1, 1, 2, 3, 2, 2, 3, 5]
def baseStart_313055 : Nat := 118140960795 + 313055 * 2 ^ 59
def prefixEnd_313055 : Nat := 4983230072969 + 3 ^ 40 * 313055 * 2
def baseEnd_313055 : Nat := 95257888173853573080173

theorem tailTrace_313055 : CollatzResearch.WordTrace tailWord_313055 prefixEnd_313055 95257888173853573080173 := by
  unfold tailWord_313055
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418053880862675382500619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7612035920575116921667079 11418053880862675382500619)
  ·
    refine ⟨17127080821294013073750929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11418053880862675382500619 17127080821294013073750929)
    ·
      refine ⟨12845310615970509805313197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17127080821294013073750929 12845310615970509805313197)
      ·
        refine ⟨4816991480988941176992449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12845310615970509805313197 4816991480988941176992449)
        ·
          refine ⟨3612743610741705882744337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4816991480988941176992449 3612743610741705882744337)
          ·
            refine ⟨2709557708056279412058253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3612743610741705882744337 2709557708056279412058253)
            ·
              refine ⟨1016084140521104779521845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2709557708056279412058253 1016084140521104779521845)
              ·
                refine ⟨95257888173853573080173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016084140521104779521845 95257888173853573080173)
                ·
                  rfl

theorem cell19_313055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 5].length) (baseStart_313055 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313055 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313055 prefixEnd_313055 := by exact prefixLift 313055
  have htrace : WordTrace (prefixWord ++ tailWord_313055) baseStart_313055 baseEnd_313055 := by
    simpa [prefixWord, tailWord_313055, baseEnd_313055] using wordTrace_append hprefix tailTrace_313055
  have hstable : (prefixWord ++ tailWord_313055).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313055).length < 2 ^ (prefixWord ++ tailWord_313055).sum := by decide
  have hdescent : baseEnd_313055 < baseStart_313055 := by decide
  rcases family_descends (prefixWord ++ tailWord_313055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313112 : List Nat := [2, 1, 2, 3, 1, 1, 4, 5]
def baseStart_313112 : Nat := 118140960795 + 313112 * 2 ^ 59
def prefixEnd_313112 : Nat := 4983230072969 + 3 ^ 40 * 313112 * 2
def baseEnd_313112 : Nat := 95275232409294329813351

theorem tailTrace_313112 : CollatzResearch.WordTrace tailWord_313112 prefixEnd_313112 95275232409294329813351 := by
  unfold tailWord_313112
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710066420828087058662795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7613421894437449411550393 5710066420828087058662795)
  ·
    refine ⟨8565099631242130587994193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5710066420828087058662795 8565099631242130587994193)
    ·
      refine ⟨6423824723431597940995645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8565099631242130587994193 6423824723431597940995645)
      ·
        refine ⟨2408934271286849227873367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6423824723431597940995645 2408934271286849227873367)
        ·
          refine ⟨3613401406930273841810051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408934271286849227873367 3613401406930273841810051)
          ·
            refine ⟨5420102110395410762715077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613401406930273841810051 5420102110395410762715077)
            ·
              refine ⟨1016269145699139518009077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5420102110395410762715077 1016269145699139518009077)
              ·
                refine ⟨95275232409294329813351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016269145699139518009077 95275232409294329813351)
                ·
                  rfl

theorem cell19_313112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_313112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313112 prefixEnd_313112 := by exact prefixLift 313112
  have htrace : WordTrace (prefixWord ++ tailWord_313112) baseStart_313112 baseEnd_313112 := by
    simpa [prefixWord, tailWord_313112, baseEnd_313112] using wordTrace_append hprefix tailTrace_313112
  have hstable : (prefixWord ++ tailWord_313112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313112).length < 2 ^ (prefixWord ++ tailWord_313112).sum := by decide
  have hdescent : baseEnd_313112 < baseStart_313112 := by decide
  rcases family_descends (prefixWord ++ tailWord_313112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313186 : List Nat := [3, 3, 2, 1, 2, 2, 6]
def baseStart_313186 : Nat := 118140960795 + 313186 * 2 ^ 59
def prefixEnd_313186 : Nat := 4983230072969 + 3 ^ 40 * 313186 * 2
def baseEnd_313186 : Nat := 31765916495628028056235

theorem tailTrace_313186 : CollatzResearch.WordTrace tailWord_313186 prefixEnd_313186 31765916495628028056235 := by
  unfold tailWord_313186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855707960847021188879853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7615221228925389837012941 2855707960847021188879853)
  ·
    refine ⟨1070890485317632945829945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2855707960847021188879853 1070890485317632945829945)
    ·
      refine ⟨803167863988224709372459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1070890485317632945829945 803167863988224709372459)
      ·
        refine ⟨1204751795982337064058689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803167863988224709372459 1204751795982337064058689)
        ·
          refine ⟨903563846986752798044017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204751795982337064058689 903563846986752798044017)
          ·
            refine ⟨677672885240064598533013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903563846986752798044017 677672885240064598533013)
            ·
              refine ⟨31765916495628028056235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 677672885240064598533013 31765916495628028056235)
              ·
                rfl

theorem cell19_313186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_313186 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313186 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313186 prefixEnd_313186 := by exact prefixLift 313186
  have htrace : WordTrace (prefixWord ++ tailWord_313186) baseStart_313186 baseEnd_313186 := by
    simpa [prefixWord, tailWord_313186, baseEnd_313186] using wordTrace_append hprefix tailTrace_313186
  have hstable : (prefixWord ++ tailWord_313186).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313186).length < 2 ^ (prefixWord ++ tailWord_313186).sum := by decide
  have hdescent : baseEnd_313186 < baseStart_313186 := by decide
  rcases family_descends (prefixWord ++ tailWord_313186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313224 : List Nat := [2, 1, 3, 3, 3, 1, 1, 5]
def baseStart_313224 : Nat := 118140960795 + 313224 * 2 ^ 59
def prefixEnd_313224 : Nat := 4983230072969 + 3 ^ 40 * 313224 * 2
def baseEnd_313224 : Nat := 95309312310511255324157

theorem tailTrace_313224 : CollatzResearch.WordTrace tailWord_313224 prefixEnd_313224 95309312310511255324157 := by
  unfold tailWord_313224
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712108908625208622701363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7616145211500278163601817 5712108908625208622701363)
  ·
    refine ⟨8568163362937812934052045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5712108908625208622701363 8568163362937812934052045)
    ·
      refine ⟨3213061261101679850269517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8568163362937812934052045 3213061261101679850269517)
      ·
        refine ⟨1204897972913129943851069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3213061261101679850269517 1204897972913129943851069)
        ·
          refine ⟨451836739842423728944151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1204897972913129943851069 451836739842423728944151)
          ·
            refine ⟨677755109763635593416227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451836739842423728944151 677755109763635593416227)
            ·
              refine ⟨1016632664645453390124341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677755109763635593416227 1016632664645453390124341)
              ·
                refine ⟨95309312310511255324157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1016632664645453390124341 95309312310511255324157)
                ·
                  rfl

theorem cell19_313224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_313224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313224 prefixEnd_313224 := by exact prefixLift 313224
  have htrace : WordTrace (prefixWord ++ tailWord_313224) baseStart_313224 baseEnd_313224 := by
    simpa [prefixWord, tailWord_313224, baseEnd_313224] using wordTrace_append hprefix tailTrace_313224
  have hstable : (prefixWord ++ tailWord_313224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313224).length < 2 ^ (prefixWord ++ tailWord_313224).sum := by decide
  have hdescent : baseEnd_313224 < baseStart_313224 := by decide
  rcases family_descends (prefixWord ++ tailWord_313224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313245 : List Nat := [1, 4, 2, 1, 2, 2, 7]
def baseStart_313245 : Nat := 118140960795 + 313245 * 2 ^ 59
def prefixEnd_313245 : Nat := 4983230072969 + 3 ^ 40 * 313245 * 2
def baseEnd_313245 : Nat := 31771900763996476285811

theorem tailTrace_313245 : CollatzResearch.WordTrace tailWord_313245 prefixEnd_313245 31771900763996476285811 := by
  unfold tailWord_313245
  simp only [CollatzResearch.WordTrace]
  refine ⟨11424983750174337831917189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7616655833449558554611459 11424983750174337831917189)
  ·
    refine ⟨2142184453157688343484473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11424983750174337831917189 2142184453157688343484473)
    ·
      refine ⟨1606638339868266257613355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2142184453157688343484473 1606638339868266257613355)
      ·
        refine ⟨2409957509802399386420033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606638339868266257613355 2409957509802399386420033)
        ·
          refine ⟨1807468132351799539815025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2409957509802399386420033 1807468132351799539815025)
          ·
            refine ⟨1355601099263849654861269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807468132351799539815025 1355601099263849654861269)
            ·
              refine ⟨31771900763996476285811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1355601099263849654861269 31771900763996476285811)
              ·
                rfl

theorem cell19_313245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 7].length) (baseStart_313245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313245 prefixEnd_313245 := by exact prefixLift 313245
  have htrace : WordTrace (prefixWord ++ tailWord_313245) baseStart_313245 baseEnd_313245 := by
    simpa [prefixWord, tailWord_313245, baseEnd_313245] using wordTrace_append hprefix tailTrace_313245
  have hstable : (prefixWord ++ tailWord_313245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313245).length < 2 ^ (prefixWord ++ tailWord_313245).sum := by decide
  have hdescent : baseEnd_313245 < baseStart_313245 := by decide
  rcases family_descends (prefixWord ++ tailWord_313245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313378 : List Nat := [3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_313378 : Nat := 118140960795 + 313378 * 2 ^ 59
def prefixEnd_313378 : Nat := 4983230072969 + 3 ^ 40 * 313378 * 2
def baseEnd_313378 : Nat := 95356172174684527901515

theorem tailTrace_313378 : CollatzResearch.WordTrace tailWord_313378 prefixEnd_313378 95356172174684527901515 := by
  unfold tailWord_313378
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857458664673125386627197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7619889772461667697672525 2857458664673125386627197)
  ·
    refine ⟨1071546999252422019985199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2857458664673125386627197 1071546999252422019985199)
    ·
      refine ⟨1607320498878633029977799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071546999252422019985199 1607320498878633029977799)
      ·
        refine ⟨2410980748317949544966699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607320498878633029977799 2410980748317949544966699)
        ·
          refine ⟨3616471122476924317450049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410980748317949544966699 3616471122476924317450049)
          ·
            refine ⟨2712353341857693238087537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616471122476924317450049 2712353341857693238087537)
            ·
              refine ⟨2034265006393269928565653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712353341857693238087537 2034265006393269928565653)
              ·
                refine ⟨95356172174684527901515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2034265006393269928565653 95356172174684527901515)
                ·
                  rfl

theorem cell19_313378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_313378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313378 prefixEnd_313378 := by exact prefixLift 313378
  have htrace : WordTrace (prefixWord ++ tailWord_313378) baseStart_313378 baseEnd_313378 := by
    simpa [prefixWord, tailWord_313378, baseEnd_313378] using wordTrace_append hprefix tailTrace_313378
  have hstable : (prefixWord ++ tailWord_313378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313378).length < 2 ^ (prefixWord ++ tailWord_313378).sum := by decide
  have hdescent : baseEnd_313378 < baseStart_313378 := by decide
  rcases family_descends (prefixWord ++ tailWord_313378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313454 : List Nat := [4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_313454 : Nat := 118140960795 + 313454 * 2 ^ 59
def prefixEnd_313454 : Nat := 4983230072969 + 3 ^ 40 * 313454 * 2
def baseEnd_313454 : Nat := 95379297821938870212419

theorem tailTrace_313454 : CollatzResearch.WordTrace tailWord_313454 prefixEnd_313454 95379297821938870212419 := by
  unfold tailWord_313454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429075825802145815784427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7621737737611444350850277 1429075825802145815784427)
  ·
    refine ⟨2143613738703218723676641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1429075825802145815784427 2143613738703218723676641)
    ·
      refine ⟨1607710304027414042757481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143613738703218723676641 1607710304027414042757481)
      ·
        refine ⟨1205782728020560532068111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1607710304027414042757481 1205782728020560532068111)
        ·
          refine ⟨1808674092030840798102167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205782728020560532068111 1808674092030840798102167)
          ·
            refine ⟨2713011138046261197153251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808674092030840798102167 2713011138046261197153251)
            ·
              refine ⟨4069516707069391795729877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713011138046261197153251 4069516707069391795729877)
              ·
                refine ⟨95379297821938870212419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4069516707069391795729877 95379297821938870212419)
                ·
                  rfl

theorem cell19_313454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_313454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313454 prefixEnd_313454 := by exact prefixLift 313454
  have htrace : WordTrace (prefixWord ++ tailWord_313454) baseStart_313454 baseEnd_313454 := by
    simpa [prefixWord, tailWord_313454, baseEnd_313454] using wordTrace_append hprefix tailTrace_313454
  have hstable : (prefixWord ++ tailWord_313454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313454).length < 2 ^ (prefixWord ++ tailWord_313454).sum := by decide
  have hdescent : baseEnd_313454 < baseStart_313454 := by decide
  rcases family_descends (prefixWord ++ tailWord_313454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313473 : List Nat := [1, 2, 4, 2, 3, 7]
def baseStart_313473 : Nat := 118140960795 + 313473 * 2 ^ 59
def prefixEnd_313473 : Nat := 4983230072969 + 3 ^ 40 * 313473 * 2
def baseEnd_313473 : Nat := 10598342137083606198905

theorem tailTrace_313473 : CollatzResearch.WordTrace tailWord_313473 prefixEnd_313473 10598342137083606198905 := by
  unfold tailWord_313473
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433299593348332771217073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7622199728898888514144715 11433299593348332771217073)
  ·
    refine ⟨8574974695011249578412805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11433299593348332771217073 8574974695011249578412805)
    ·
      refine ⟨1607807755314609295952401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8574974695011249578412805 1607807755314609295952401)
      ·
        refine ⟨1205855816485956971964301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1607807755314609295952401 1205855816485956971964301)
        ·
          refine ⟨452195931182233864486613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1205855816485956971964301 452195931182233864486613)
          ·
            refine ⟨10598342137083606198905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 452195931182233864486613 10598342137083606198905)
            ·
              rfl

theorem cell19_313473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_313473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313473 prefixEnd_313473 := by exact prefixLift 313473
  have htrace : WordTrace (prefixWord ++ tailWord_313473) baseStart_313473 baseEnd_313473 := by
    simpa [prefixWord, tailWord_313473, baseEnd_313473] using wordTrace_append hprefix tailTrace_313473
  have hstable : (prefixWord ++ tailWord_313473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313473).length < 2 ^ (prefixWord ++ tailWord_313473).sum := by decide
  have hdescent : baseEnd_313473 < baseStart_313473 := by decide
  rcases family_descends (prefixWord ++ tailWord_313473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313475 : List Nat := [1, 1, 1, 3, 3, 10]
def baseStart_313475 : Nat := 118140960795 + 313475 * 2 ^ 59
def prefixEnd_313475 : Nat := 4983230072969 + 3 ^ 40 * 313475 * 2
def baseEnd_313475 : Nat := 10598409755935227082855

theorem tailTrace_313475 : CollatzResearch.WordTrace tailWord_313475 prefixEnd_313475 10598409755935227082855 := by
  unfold tailWord_313475
  simp only [CollatzResearch.WordTrace]
  refine ⟨11433372539341087112789879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7622248359560724741859919 11433372539341087112789879)
  ·
    refine ⟨17150058809011630669184819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11433372539341087112789879 17150058809011630669184819)
    ·
      refine ⟨25725088213517446003777229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17150058809011630669184819 25725088213517446003777229)
      ·
        refine ⟨9646908080069042251416461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25725088213517446003777229 9646908080069042251416461)
        ·
          refine ⟨3617590530025890844281173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9646908080069042251416461 3617590530025890844281173)
          ·
            refine ⟨10598409755935227082855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3617590530025890844281173 10598409755935227082855)
            ·
              rfl

theorem cell19_313475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_313475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313475 prefixEnd_313475 := by exact prefixLift 313475
  have htrace : WordTrace (prefixWord ++ tailWord_313475) baseStart_313475 baseEnd_313475 := by
    simpa [prefixWord, tailWord_313475, baseEnd_313475] using wordTrace_append hprefix tailTrace_313475
  have hstable : (prefixWord ++ tailWord_313475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313475).length < 2 ^ (prefixWord ++ tailWord_313475).sum := by decide
  have hdescent : baseEnd_313475 < baseStart_313475 := by decide
  rcases family_descends (prefixWord ++ tailWord_313475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313524 : List Nat := [2, 5, 3, 1, 1, 1, 6]
def baseStart_313524 : Nat := 118140960795 + 313524 * 2 ^ 59
def prefixEnd_313524 : Nat := 4983230072969 + 3 ^ 40 * 313524 * 2
def baseEnd_313524 : Nat := 31800199253399816218891

theorem tailTrace_313524 : CollatzResearch.WordTrace tailWord_313524 prefixEnd_313524 31800199253399816218891 := by
  unfold tailWord_313524
  simp only [CollatzResearch.WordTrace]
  refine ⟨5717579858081784240661813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7623439810775712320882417 5717579858081784240661813)
  ·
    refine ⟨536023111695167272562045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5717579858081784240661813 536023111695167272562045)
    ·
      refine ⟨201008666885687727210767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 536023111695167272562045 201008666885687727210767)
      ·
        refine ⟨301513000328531590816151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201008666885687727210767 301513000328531590816151)
        ·
          refine ⟨452269500492797386224227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301513000328531590816151 452269500492797386224227)
          ·
            refine ⟨678404250739196079336341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452269500492797386224227 678404250739196079336341)
            ·
              refine ⟨31800199253399816218891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 678404250739196079336341 31800199253399816218891)
              ·
                rfl

theorem cell19_313524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 6].length) (baseStart_313524 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313524 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313524 prefixEnd_313524 := by exact prefixLift 313524
  have htrace : WordTrace (prefixWord ++ tailWord_313524) baseStart_313524 baseEnd_313524 := by
    simpa [prefixWord, tailWord_313524, baseEnd_313524] using wordTrace_append hprefix tailTrace_313524
  have hstable : (prefixWord ++ tailWord_313524).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313524).length < 2 ^ (prefixWord ++ tailWord_313524).sum := by decide
  have hdescent : baseEnd_313524 < baseStart_313524 := by decide
  rcases family_descends (prefixWord ++ tailWord_313524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313551 : List Nat := [1, 1, 2, 1, 1, 3, 4, 6]
def baseStart_313551 : Nat := 118140960795 + 313551 * 2 ^ 59
def prefixEnd_313551 : Nat := 4983230072969 + 3 ^ 40 * 313551 * 2
def baseEnd_313551 : Nat := 95408813450671386056599

theorem tailTrace_313551 : CollatzResearch.WordTrace tailWord_313551 prefixEnd_313551 95408813450671386056599 := by
  unfold tailWord_313551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11436144487065752092556507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7624096324710501395037671 11436144487065752092556507)
  ·
    refine ⟨17154216730598628138834761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11436144487065752092556507 17154216730598628138834761)
    ·
      refine ⟨12865662547948971104126071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17154216730598628138834761 12865662547948971104126071)
      ·
        refine ⟨19298493821923456656189107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12865662547948971104126071 19298493821923456656189107)
        ·
          refine ⟨28947740732885184984283661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19298493821923456656189107 28947740732885184984283661)
          ·
            refine ⟨10855402774831944369106373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28947740732885184984283661 10855402774831944369106373)
            ·
              refine ⟨2035388020280989569207445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10855402774831944369106373 2035388020280989569207445)
              ·
                refine ⟨95408813450671386056599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2035388020280989569207445 95408813450671386056599)
                ·
                  rfl

theorem cell19_313551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_313551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313551 prefixEnd_313551 := by exact prefixLift 313551
  have htrace : WordTrace (prefixWord ++ tailWord_313551) baseStart_313551 baseEnd_313551 := by
    simpa [prefixWord, tailWord_313551, baseEnd_313551] using wordTrace_append hprefix tailTrace_313551
  have hstable : (prefixWord ++ tailWord_313551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313551).length < 2 ^ (prefixWord ++ tailWord_313551).sum := by decide
  have hdescent : baseEnd_313551 < baseStart_313551 := by decide
  rcases family_descends (prefixWord ++ tailWord_313551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313564 : List Nat := [2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_313564 : Nat := 118140960795 + 313564 * 2 ^ 59
def prefixEnd_313564 : Nat := 4983230072969 + 3 ^ 40 * 313564 * 2
def baseEnd_313564 : Nat := 95412769153491207767675

theorem tailTrace_313564 : CollatzResearch.WordTrace tailWord_313564 prefixEnd_313564 95412769153491207767675 := by
  unfold tailWord_313564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5718309318009327656389873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7624412424012436875186497 5718309318009327656389873)
  ·
    refine ⟨4288731988506995742292405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5718309318009327656389873 4288731988506995742292405)
    ·
      refine ⟨402068623922530850839913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4288731988506995742292405 402068623922530850839913)
      ·
        refine ⟨301551467941898138129935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402068623922530850839913 301551467941898138129935)
        ·
          refine ⟨452327201912847207194903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301551467941898138129935 452327201912847207194903)
          ·
            refine ⟨678490802869270810792355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452327201912847207194903 678490802869270810792355)
            ·
              refine ⟨1017736204303906216188533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678490802869270810792355 1017736204303906216188533)
              ·
                refine ⟨95412769153491207767675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1017736204303906216188533 95412769153491207767675)
                ·
                  rfl

theorem cell19_313564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_313564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313564 prefixEnd_313564 := by exact prefixLift 313564
  have htrace : WordTrace (prefixWord ++ tailWord_313564) baseStart_313564 baseEnd_313564 := by
    simpa [prefixWord, tailWord_313564, baseEnd_313564] using wordTrace_append hprefix tailTrace_313564
  have hstable : (prefixWord ++ tailWord_313564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313564).length < 2 ^ (prefixWord ++ tailWord_313564).sum := by decide
  have hdescent : baseEnd_313564 < baseStart_313564 := by decide
  rcases family_descends (prefixWord ++ tailWord_313564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313604 : List Nat := [2, 3, 2, 2, 3, 1, 2, 4]
def baseStart_313604 : Nat := 118140960795 + 313604 * 2 ^ 59
def prefixEnd_313604 : Nat := 4983230072969 + 3 ^ 40 * 313604 * 2
def baseEnd_313604 : Nat := 95424940546782966878677

theorem tailTrace_313604 : CollatzResearch.WordTrace tailWord_313604 prefixEnd_313604 95424940546782966878677 := by
  unfold tailWord_313604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719038777936871072117933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7625385037249161429490577 5719038777936871072117933)
  ·
    refine ⟨2144639541726326652044225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5719038777936871072117933 2144639541726326652044225)
    ·
      refine ⟨1608479656294744989033169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2144639541726326652044225 1608479656294744989033169)
      ·
        refine ⟨1206359742221058741774877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1608479656294744989033169 1206359742221058741774877)
        ·
          refine ⟨452384903332897028165579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1206359742221058741774877 452384903332897028165579)
          ·
            refine ⟨678577354999345542248369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452384903332897028165579 678577354999345542248369)
            ·
              refine ⟨508933016249509156686277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678577354999345542248369 508933016249509156686277)
              ·
                refine ⟨95424940546782966878677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508933016249509156686277 95424940546782966878677)
                ·
                  rfl

theorem cell19_313604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_313604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313604 prefixEnd_313604 := by exact prefixLift 313604
  have htrace : WordTrace (prefixWord ++ tailWord_313604) baseStart_313604 baseEnd_313604 := by
    simpa [prefixWord, tailWord_313604, baseEnd_313604] using wordTrace_append hprefix tailTrace_313604
  have hstable : (prefixWord ++ tailWord_313604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313604).length < 2 ^ (prefixWord ++ tailWord_313604).sum := by decide
  have hdescent : baseEnd_313604 < baseStart_313604 := by decide
  rcases family_descends (prefixWord ++ tailWord_313604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313627 : List Nat := [1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_313627 : Nat := 118140960795 + 313627 * 2 ^ 59
def prefixEnd_313627 : Nat := 4983230072969 + 3 ^ 40 * 313627 * 2
def baseEnd_313627 : Nat := 95431939097925728367503

theorem tailTrace_313627 : CollatzResearch.WordTrace tailWord_313627 prefixEnd_313627 95431939097925728367503 := by
  unfold tailWord_313627
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438916434790417072323135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7625944289860278048215423 11438916434790417072323135)
  ·
    refine ⟨17158374652185625608484703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11438916434790417072323135 17158374652185625608484703)
    ·
      refine ⟨25737561978278438412727055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17158374652185625608484703 25737561978278438412727055)
      ·
        refine ⟨38606342967417657619090583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25737561978278438412727055 38606342967417657619090583)
        ·
          refine ⟨57909514451126486428635875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38606342967417657619090583 57909514451126486428635875)
          ·
            refine ⟨86864271676689729642953813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57909514451126486428635875 86864271676689729642953813)
            ·
              refine ⟨1017940683711207769253365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 86864271676689729642953813 1017940683711207769253365)
              ·
                refine ⟨95431939097925728367503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1017940683711207769253365 95431939097925728367503)
                ·
                  rfl

theorem cell19_313627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_313627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313627 prefixEnd_313627 := by exact prefixLift 313627
  have htrace : WordTrace (prefixWord ++ tailWord_313627) baseStart_313627 baseEnd_313627 := by
    simpa [prefixWord, tailWord_313627, baseEnd_313627] using wordTrace_append hprefix tailTrace_313627
  have hstable : (prefixWord ++ tailWord_313627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313627).length < 2 ^ (prefixWord ++ tailWord_313627).sum := by decide
  have hdescent : baseEnd_313627 < baseStart_313627 := by decide
  rcases family_descends (prefixWord ++ tailWord_313627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313642 : List Nat := [3, 1, 4, 2, 3, 6]
def baseStart_313642 : Nat := 118140960795 + 313642 * 2 ^ 59
def prefixEnd_313642 : Nat := 4983230072969 + 3 ^ 40 * 313642 * 2
def baseEnd_313642 : Nat := 10604055930045570892681

theorem tailTrace_313642 : CollatzResearch.WordTrace tailWord_313642 prefixEnd_313642 10604055930045570892681 := by
  unfold tailWord_313642
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859865882434018658529795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7626309019824049756079453 2859865882434018658529795)
  ·
    refine ⟨4289798823651027987794693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859865882434018658529795 4289798823651027987794693)
    ·
      refine ⟨804337279434567747711505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4289798823651027987794693 804337279434567747711505)
      ·
        refine ⟨603252959575925810783629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 804337279434567747711505 603252959575925810783629)
        ·
          refine ⟨226219859840972179043861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 603252959575925810783629 226219859840972179043861)
          ·
            refine ⟨10604055930045570892681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 226219859840972179043861 10604055930045570892681)
            ·
              rfl

theorem cell19_313642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_313642 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313642 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313642 prefixEnd_313642 := by exact prefixLift 313642
  have htrace : WordTrace (prefixWord ++ tailWord_313642) baseStart_313642 baseEnd_313642 := by
    simpa [prefixWord, tailWord_313642, baseEnd_313642] using wordTrace_append hprefix tailTrace_313642
  have hstable : (prefixWord ++ tailWord_313642).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313642).length < 2 ^ (prefixWord ++ tailWord_313642).sum := by decide
  have hdescent : baseEnd_313642 < baseStart_313642 := by decide
  rcases family_descends (prefixWord ++ tailWord_313642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313737 : List Nat := [1, 2, 1, 1, 6, 3, 2, 3]
def baseStart_313737 : Nat := 118140960795 + 313737 * 2 ^ 59
def prefixEnd_313737 : Nat := 4983230072969 + 3 ^ 40 * 313737 * 2
def baseEnd_313737 : Nat := 95465410429478065922759

theorem tailTrace_313737 : CollatzResearch.WordTrace tailWord_313737 prefixEnd_313737 95465410429478065922759 := by
  unfold tailWord_313737
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442928464391905858827465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7628618976261270572551643 11442928464391905858827465)
  ·
    refine ⟨8582196348293929394120599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11442928464391905858827465 8582196348293929394120599)
    ·
      refine ⟨12873294522440894091180899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582196348293929394120599 12873294522440894091180899)
      ·
        refine ⟨19309941783661341136771349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12873294522440894091180899 19309941783661341136771349)
        ·
          refine ⟨905153521109125365786157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19309941783661341136771349 905153521109125365786157)
          ·
            refine ⟨339432570415922012169809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 905153521109125365786157 339432570415922012169809)
            ·
              refine ⟨254574427811941509127357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339432570415922012169809 254574427811941509127357)
              ·
                refine ⟨95465410429478065922759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254574427811941509127357 95465410429478065922759)
                ·
                  rfl

theorem cell19_313737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 3].length) (baseStart_313737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313737 prefixEnd_313737 := by exact prefixLift 313737
  have htrace : WordTrace (prefixWord ++ tailWord_313737) baseStart_313737 baseEnd_313737 := by
    simpa [prefixWord, tailWord_313737, baseEnd_313737] using wordTrace_append hprefix tailTrace_313737
  have hstable : (prefixWord ++ tailWord_313737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313737).length < 2 ^ (prefixWord ++ tailWord_313737).sum := by decide
  have hdescent : baseEnd_313737 < baseStart_313737 := by decide
  rcases family_descends (prefixWord ++ tailWord_313737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313739 : List Nat := [1, 1, 1, 1, 4, 4, 4, 3]
def baseStart_313739 : Nat := 118140960795 + 313739 * 2 ^ 59
def prefixEnd_313739 : Nat := 4983230072969 + 3 ^ 40 * 313739 * 2
def baseEnd_313739 : Nat := 95466018999142653878309

theorem tailTrace_313739 : CollatzResearch.WordTrace tailWord_313739 prefixEnd_313739 95466018999142653878309 := by
  unfold tailWord_313739
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443001410384660200400271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7628667606923106800266847 11443001410384660200400271)
  ·
    refine ⟨17164502115576990300600407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11443001410384660200400271 17164502115576990300600407)
    ·
      refine ⟨25746753173365485450900611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17164502115576990300600407 25746753173365485450900611)
      ·
        refine ⟨38620129760048228176350917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25746753173365485450900611 38620129760048228176350917)
        ·
          refine ⟨7241274330009042783065797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38620129760048228176350917 7241274330009042783065797)
          ·
            refine ⟨1357738936876695521824837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7241274330009042783065797 1357738936876695521824837)
            ·
              refine ⟨254576050664380410342157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1357738936876695521824837 254576050664380410342157)
              ·
                refine ⟨95466018999142653878309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254576050664380410342157 95466018999142653878309)
                ·
                  rfl

theorem cell19_313739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 4, 3].length) (baseStart_313739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313739 prefixEnd_313739 := by exact prefixLift 313739
  have htrace : WordTrace (prefixWord ++ tailWord_313739) baseStart_313739 baseEnd_313739 := by
    simpa [prefixWord, tailWord_313739, baseEnd_313739] using wordTrace_append hprefix tailTrace_313739
  have hstable : (prefixWord ++ tailWord_313739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313739).length < 2 ^ (prefixWord ++ tailWord_313739).sum := by decide
  have hdescent : baseEnd_313739 < baseStart_313739 := by decide
  rcases family_descends (prefixWord ++ tailWord_313739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313750 : List Nat := [5, 3, 1, 2, 2, 1, 5]
def baseStart_313750 : Nat := 118140960795 + 313750 * 2 ^ 59
def prefixEnd_313750 : Nat := 4983230072969 + 3 ^ 40 * 313750 * 2
def baseEnd_313750 : Nat := 31823122044099295877945

theorem tailTrace_313750 : CollatzResearch.WordTrace tailWord_313750 prefixEnd_313750 31823122044099295877945 := by
  unfold tailWord_313750
  simp only [CollatzResearch.WordTrace]
  refine ⟨715212663334050567440669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7628935075563206052700469 715212663334050567440669)
  ·
    refine ⟨268204748750268962790251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 715212663334050567440669 268204748750268962790251)
    ·
      refine ⟨402307123125403444185377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268204748750268962790251 402307123125403444185377)
      ·
        refine ⟨301730342344052583139033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402307123125403444185377 301730342344052583139033)
        ·
          refine ⟨226297756758039437354275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301730342344052583139033 226297756758039437354275)
          ·
            refine ⟨339446635137059156031413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226297756758039437354275 339446635137059156031413)
            ·
              refine ⟨31823122044099295877945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 339446635137059156031413 31823122044099295877945)
              ·
                rfl

theorem cell19_313750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_313750 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313750 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313750 prefixEnd_313750 := by exact prefixLift 313750
  have htrace : WordTrace (prefixWord ++ tailWord_313750) baseStart_313750 baseEnd_313750 := by
    simpa [prefixWord, tailWord_313750, baseEnd_313750] using wordTrace_append hprefix tailTrace_313750
  have hstable : (prefixWord ++ tailWord_313750).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313750).length < 2 ^ (prefixWord ++ tailWord_313750).sum := by decide
  have hdescent : baseEnd_313750 < baseStart_313750 := by decide
  rcases family_descends (prefixWord ++ tailWord_313750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313760 : List Nat := [2, 1, 1, 4, 1, 3, 7]
def baseStart_313760 : Nat := 118140960795 + 313760 * 2 ^ 59
def prefixEnd_313760 : Nat := 4983230072969 + 3 ^ 40 * 313760 * 2
def baseEnd_313760 : Nat := 31824136326873609137195

theorem tailTrace_313760 : CollatzResearch.WordTrace tailWord_313760 prefixEnd_313760 31824136326873609137195 := by
  unfold tailWord_313760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5721883671654290393457367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7629178228872387191276489 5721883671654290393457367)
  ·
    refine ⟨8582825507481435590186051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5721883671654290393457367 8582825507481435590186051)
    ·
      refine ⟨12874238261222153385279077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582825507481435590186051 12874238261222153385279077)
      ·
        refine ⟨2413919673979153759739827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12874238261222153385279077 2413919673979153759739827)
        ·
          refine ⟨3620879510968730639609741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413919673979153759739827 3620879510968730639609741)
          ·
            refine ⟨1357829816613273989853653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3620879510968730639609741 1357829816613273989853653)
            ·
              refine ⟨31824136326873609137195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1357829816613273989853653 31824136326873609137195)
              ·
                rfl

theorem cell19_313760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 7].length) (baseStart_313760 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313760 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313760 prefixEnd_313760 := by exact prefixLift 313760
  have htrace : WordTrace (prefixWord ++ tailWord_313760) baseStart_313760 baseEnd_313760 := by
    simpa [prefixWord, tailWord_313760, baseEnd_313760] using wordTrace_append hprefix tailTrace_313760
  have hstable : (prefixWord ++ tailWord_313760).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313760).length < 2 ^ (prefixWord ++ tailWord_313760).sum := by decide
  have hdescent : baseEnd_313760 < baseStart_313760 := by decide
  rcases family_descends (prefixWord ++ tailWord_313760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313777 : List Nat := [1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_313777 : Nat := 118140960795 + 313777 * 2 ^ 59
def prefixEnd_313777 : Nat := 4983230072969 + 3 ^ 40 * 313777 * 2
def baseEnd_313777 : Nat := 95477581822769825033761

theorem tailTrace_313777 : CollatzResearch.WordTrace tailWord_313777 prefixEnd_313777 95477581822769825033761 := by
  unfold tailWord_313777
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444387384246992690283585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7629591589497995126855723 11444387384246992690283585)
  ·
    refine ⟨8583290538185244517712689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11444387384246992690283585 8583290538185244517712689)
    ·
      refine ⟨6437467903638933388284517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8583290538185244517712689 6437467903638933388284517)
      ·
        refine ⟨1207025231932300010303347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6437467903638933388284517 1207025231932300010303347)
        ·
          refine ⟨1810537847898450015455021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207025231932300010303347 1810537847898450015455021)
          ·
            refine ⟨678951692961918755795633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1810537847898450015455021 678951692961918755795633)
            ·
              refine ⟨509213769721439066846725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678951692961918755795633 509213769721439066846725)
              ·
                refine ⟨95477581822769825033761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509213769721439066846725 95477581822769825033761)
                ·
                  rfl

theorem cell19_313777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_313777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313777 prefixEnd_313777 := by exact prefixLift 313777
  have htrace : WordTrace (prefixWord ++ tailWord_313777) baseStart_313777 baseEnd_313777 := by
    simpa [prefixWord, tailWord_313777, baseEnd_313777] using wordTrace_append hprefix tailTrace_313777
  have hstable : (prefixWord ++ tailWord_313777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313777).length < 2 ^ (prefixWord ++ tailWord_313777).sum := by decide
  have hdescent : baseEnd_313777 < baseStart_313777 := by decide
  rcases family_descends (prefixWord ++ tailWord_313777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313834 : List Nat := [3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_313834 : Nat := 118140960795 + 313834 * 2 ^ 59
def prefixEnd_313834 : Nat := 4983230072969 + 3 ^ 40 * 313834 * 2
def baseEnd_313834 : Nat := 95494926058210581766939

theorem tailTrace_313834 : CollatzResearch.WordTrace tailWord_313834 prefixEnd_313834 95494926058210581766939 := by
  unfold tailWord_313834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2861616586260122856277139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7630977563360327616739037 2861616586260122856277139)
  ·
    refine ⟨4292424879390184284415709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2861616586260122856277139 4292424879390184284415709)
    ·
      refine ⟨1609659329771319106655891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4292424879390184284415709 1609659329771319106655891)
      ·
        refine ⟨2414488994656978659983837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609659329771319106655891 2414488994656978659983837)
        ·
          refine ⟨905433372996366997493939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2414488994656978659983837 905433372996366997493939)
          ·
            refine ⟨1358150059494550496240909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905433372996366997493939 1358150059494550496240909)
            ·
              refine ⟨509306272310456436090341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358150059494550496240909 509306272310456436090341)
              ·
                refine ⟨95494926058210581766939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509306272310456436090341 95494926058210581766939)
                ·
                  rfl

theorem cell19_313834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_313834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313834 prefixEnd_313834 := by exact prefixLift 313834
  have htrace : WordTrace (prefixWord ++ tailWord_313834) baseStart_313834 baseEnd_313834 := by
    simpa [prefixWord, tailWord_313834, baseEnd_313834] using wordTrace_append hprefix tailTrace_313834
  have hstable : (prefixWord ++ tailWord_313834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313834).length < 2 ^ (prefixWord ++ tailWord_313834).sum := by decide
  have hdescent : baseEnd_313834 < baseStart_313834 := by decide
  rcases family_descends (prefixWord ++ tailWord_313834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313853 : List Nat := [1, 4, 1, 1, 1, 3, 5, 3]
def baseStart_313853 : Nat := 118140960795 + 313853 * 2 ^ 59
def prefixEnd_313853 : Nat := 4983230072969 + 3 ^ 40 * 313853 * 2
def baseEnd_313853 : Nat := 95500707470024167344665

theorem tailTrace_313853 : CollatzResearch.WordTrace tailWord_313853 prefixEnd_313853 95500707470024167344665 := by
  unfold tailWord_313853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447159331971657670050213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7631439554647771780033475 11447159331971657670050213)
  ·
    refine ⟨2146342374744685813134415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11447159331971657670050213 2146342374744685813134415)
    ·
      refine ⟨3219513562117028719701623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146342374744685813134415 3219513562117028719701623)
      ·
        refine ⟨4829270343175543079552435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219513562117028719701623 4829270343175543079552435)
        ·
          refine ⟨7243905514763314619328653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829270343175543079552435 7243905514763314619328653)
          ·
            refine ⟨2716464568036242982248245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7243905514763314619328653 2716464568036242982248245)
            ·
              refine ⟨254668553253397779585773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2716464568036242982248245 254668553253397779585773)
              ·
                refine ⟨95500707470024167344665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254668553253397779585773 95500707470024167344665)
                ·
                  rfl

theorem cell19_313853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 5, 3].length) (baseStart_313853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313853 prefixEnd_313853 := by exact prefixLift 313853
  have htrace : WordTrace (prefixWord ++ tailWord_313853) baseStart_313853 baseEnd_313853 := by
    simpa [prefixWord, tailWord_313853, baseEnd_313853] using wordTrace_append hprefix tailTrace_313853
  have hstable : (prefixWord ++ tailWord_313853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313853).length < 2 ^ (prefixWord ++ tailWord_313853).sum := by decide
  have hdescent : baseEnd_313853 < baseStart_313853 := by decide
  rcases family_descends (prefixWord ++ tailWord_313853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313912 : List Nat := [2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_313912 : Nat := 118140960795 + 313912 * 2 ^ 59
def prefixEnd_313912 : Nat := 4983230072969 + 3 ^ 40 * 313912 * 2
def baseEnd_313912 : Nat := 95518660275129512033393

theorem tailTrace_313912 : CollatzResearch.WordTrace tailWord_313912 prefixEnd_313912 95518660275129512033393 := by
  unfold tailWord_313912
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724655619378955373223995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7632874159171940497631993 5724655619378955373223995)
  ·
    refine ⟨8586983429068433059835993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724655619378955373223995 8586983429068433059835993)
    ·
      refine ⟨6440237571801324794876995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8586983429068433059835993 6440237571801324794876995)
      ·
        refine ⟨9660356357701987192315493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440237571801324794876995 9660356357701987192315493)
        ·
          refine ⟨1811316817069122598559155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9660356357701987192315493 1811316817069122598559155)
          ·
            refine ⟨2716975225603683897838733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811316817069122598559155 2716975225603683897838733)
            ·
              refine ⟨1018865709601381461689525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2716975225603683897838733 1018865709601381461689525)
              ·
                refine ⟨95518660275129512033393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1018865709601381461689525 95518660275129512033393)
                ·
                  rfl

theorem cell19_313912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_313912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313912 prefixEnd_313912 := by exact prefixLift 313912
  have htrace : WordTrace (prefixWord ++ tailWord_313912) baseStart_313912 baseEnd_313912 := by
    simpa [prefixWord, tailWord_313912, baseEnd_313912] using wordTrace_append hprefix tailTrace_313912
  have hstable : (prefixWord ++ tailWord_313912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313912).length < 2 ^ (prefixWord ++ tailWord_313912).sum := by decide
  have hdescent : baseEnd_313912 < baseStart_313912 := by decide
  rcases family_descends (prefixWord ++ tailWord_313912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_313988 : List Nat := [2, 3, 2, 1, 3, 8]
def baseStart_313988 : Nat := 118140960795 + 313988 * 2 ^ 59
def prefixEnd_313988 : Nat := 4983230072969 + 3 ^ 40 * 313988 * 2
def baseEnd_313988 : Nat := 10615753991375983816033

theorem tailTrace_313988 : CollatzResearch.WordTrace tailWord_313988 prefixEnd_313988 10615753991375983816033 := by
  unfold tailWord_313988
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726041593241287863107309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7634722124321717150809745 5726041593241287863107309)
  ·
    refine ⟨2147265597465482948665241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5726041593241287863107309 2147265597465482948665241)
    ·
      refine ⟨1610449198099112211498931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2147265597465482948665241 1610449198099112211498931)
      ·
        refine ⟨2415673797148668317248397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1610449198099112211498931 2415673797148668317248397)
        ·
          refine ⟨905877673930750618968149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2415673797148668317248397 905877673930750618968149)
          ·
            refine ⟨10615753991375983816033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 905877673930750618968149 10615753991375983816033)
            ·
              rfl

theorem cell19_313988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_313988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_313988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_313988 prefixEnd_313988 := by exact prefixLift 313988
  have htrace : WordTrace (prefixWord ++ tailWord_313988) baseStart_313988 baseEnd_313988 := by
    simpa [prefixWord, tailWord_313988, baseEnd_313988] using wordTrace_append hprefix tailTrace_313988
  have hstable : (prefixWord ++ tailWord_313988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_313988).length < 2 ^ (prefixWord ++ tailWord_313988).sum := by decide
  have hdescent : baseEnd_313988 < baseStart_313988 := by decide
  rcases family_descends (prefixWord ++ tailWord_313988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314045 : List Nat := [1, 4, 1, 2, 1, 4, 6]
def baseStart_314045 : Nat := 118140960795 + 314045 * 2 ^ 59
def prefixEnd_314045 : Nat := 4983230072969 + 3 ^ 40 * 314045 * 2
def baseEnd_314045 : Nat := 31853043385941537025825

theorem tailTrace_314045 : CollatzResearch.WordTrace tailWord_314045 prefixEnd_314045 31853043385941537025825 := by
  unfold tailWord_314045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11454162147276074461039589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7636108098184049640693059 11454162147276074461039589)
  ·
    refine ⟨2147655402614263961444923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11454162147276074461039589 2147655402614263961444923)
    ·
      refine ⟨3221483103921395942167385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147655402614263961444923 3221483103921395942167385)
      ·
        refine ⟨2416112327941046956625539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3221483103921395942167385 2416112327941046956625539)
        ·
          refine ⟨3624168491911570434938309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416112327941046956625539 3624168491911570434938309)
          ·
            refine ⟨679531592233419456550933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3624168491911570434938309 679531592233419456550933)
            ·
              refine ⟨31853043385941537025825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 679531592233419456550933 31853043385941537025825)
              ·
                rfl

theorem cell19_314045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_314045 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314045 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314045 prefixEnd_314045 := by exact prefixLift 314045
  have htrace : WordTrace (prefixWord ++ tailWord_314045) baseStart_314045 baseEnd_314045 := by
    simpa [prefixWord, tailWord_314045, baseEnd_314045] using wordTrace_append hprefix tailTrace_314045
  have hstable : (prefixWord ++ tailWord_314045).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314045).length < 2 ^ (prefixWord ++ tailWord_314045).sum := by decide
  have hdescent : baseEnd_314045 < baseStart_314045 := by decide
  rcases family_descends (prefixWord ++ tailWord_314045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314081 : List Nat := [1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_314081 : Nat := 118140960795 + 314081 * 2 ^ 59
def prefixEnd_314081 : Nat := 4983230072969 + 3 ^ 40 * 314081 * 2
def baseEnd_314081 : Nat := 95570084411787194277377

theorem tailTrace_314081 : CollatzResearch.WordTrace tailWord_314081 prefixEnd_314081 95570084411787194277377 := by
  unfold tailWord_314081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11455475175145652609350097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7636983450097101739566731 11455475175145652609350097)
  ·
    refine ⟨8591606381359239457012573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11455475175145652609350097 8591606381359239457012573)
    ·
      refine ⟨3221852393009714796379715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8591606381359239457012573 3221852393009714796379715)
      ·
        refine ⟨4832778589514572194569573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3221852393009714796379715 4832778589514572194569573)
        ·
          refine ⟨906145985533982286481795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4832778589514572194569573 906145985533982286481795)
          ·
            refine ⟨1359218978300973429722693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906145985533982286481795 1359218978300973429722693)
            ·
              refine ⟨254853558431432518073005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1359218978300973429722693 254853558431432518073005)
              ·
                refine ⟨95570084411787194277377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254853558431432518073005 95570084411787194277377)
                ·
                  rfl

theorem cell19_314081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_314081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314081 prefixEnd_314081 := by exact prefixLift 314081
  have htrace : WordTrace (prefixWord ++ tailWord_314081) baseStart_314081 baseEnd_314081 := by
    simpa [prefixWord, tailWord_314081, baseEnd_314081] using wordTrace_append hprefix tailTrace_314081
  have hstable : (prefixWord ++ tailWord_314081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314081).length < 2 ^ (prefixWord ++ tailWord_314081).sum := by decide
  have hdescent : baseEnd_314081 < baseStart_314081 := by decide
  rcases family_descends (prefixWord ++ tailWord_314081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314119 : List Nat := [1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_314119 : Nat := 118140960795 + 314119 * 2 ^ 59
def prefixEnd_314119 : Nat := 4983230072969 + 3 ^ 40 * 314119 * 2
def baseEnd_314119 : Nat := 95581647235414365432829

theorem tailTrace_314119 : CollatzResearch.WordTrace tailWord_314119 prefixEnd_314119 95581647235414365432829 := by
  unfold tailWord_314119
  simp only [CollatzResearch.WordTrace]
  refine ⟨11456861149007985099233411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7637907432671990066155607 11456861149007985099233411)
  ·
    refine ⟨17185291723511977648850117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11456861149007985099233411 17185291723511977648850117)
    ·
      refine ⟨3222242198158495809159397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17185291723511977648850117 3222242198158495809159397)
      ·
        refine ⟨604170412154717964217387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3222242198158495809159397 604170412154717964217387)
        ·
          refine ⟨906255618232076946326081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604170412154717964217387 906255618232076946326081)
          ·
            refine ⟨679691713674057709744561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 906255618232076946326081 679691713674057709744561)
            ·
              refine ⟨509768785255543282308421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679691713674057709744561 509768785255543282308421)
              ·
                refine ⟨95581647235414365432829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509768785255543282308421 95581647235414365432829)
                ·
                  rfl

theorem cell19_314119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_314119 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314119 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314119 prefixEnd_314119 := by exact prefixLift 314119
  have htrace : WordTrace (prefixWord ++ tailWord_314119) baseStart_314119 baseEnd_314119 := by
    simpa [prefixWord, tailWord_314119, baseEnd_314119] using wordTrace_append hprefix tailTrace_314119
  have hstable : (prefixWord ++ tailWord_314119).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314119).length < 2 ^ (prefixWord ++ tailWord_314119).sum := by decide
  have hdescent : baseEnd_314119 < baseStart_314119 := by decide
  rcases family_descends (prefixWord ++ tailWord_314119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314140 : List Nat := [2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_314140 : Nat := 118140960795 + 314140 * 2 ^ 59
def prefixEnd_314140 : Nat := 4983230072969 + 3 ^ 40 * 314140 * 2
def baseEnd_314140 : Nat := 95588037216892538966105

theorem tailTrace_314140 : CollatzResearch.WordTrace tailWord_314140 prefixEnd_314140 95588037216892538966105 := by
  unfold tailWord_314140
  simp only [CollatzResearch.WordTrace]
  refine ⟨5728813540965952842873937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7638418054621270457165249 5728813540965952842873937)
  ·
    refine ⟨4296610155724464632155453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5728813540965952842873937 4296610155724464632155453)
    ·
      refine ⟨1611228808396674237058295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4296610155724464632155453 1611228808396674237058295)
      ·
        refine ⟨2416843212595011355587443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1611228808396674237058295 2416843212595011355587443)
        ·
          refine ⟨3625264818892517033381165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2416843212595011355587443 3625264818892517033381165)
          ·
            refine ⟨1359474307084693887517937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3625264818892517033381165 1359474307084693887517937)
            ·
              refine ⟨1019605730313520415638453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1359474307084693887517937 1019605730313520415638453)
              ·
                refine ⟨95588037216892538966105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1019605730313520415638453 95588037216892538966105)
                ·
                  rfl

theorem cell19_314140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_314140 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314140 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314140 prefixEnd_314140 := by exact prefixLift 314140
  have htrace : WordTrace (prefixWord ++ tailWord_314140) baseStart_314140 baseEnd_314140 := by
    simpa [prefixWord, tailWord_314140, baseEnd_314140] using wordTrace_append hprefix tailTrace_314140
  have hstable : (prefixWord ++ tailWord_314140).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314140).length < 2 ^ (prefixWord ++ tailWord_314140).sum := by decide
  have hdescent : baseEnd_314140 < baseStart_314140 := by decide
  rcases family_descends (prefixWord ++ tailWord_314140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314157 : List Nat := [1, 5, 3, 2, 8]
def baseStart_314157 : Nat := 118140960795 + 314157 * 2 ^ 59
def prefixEnd_314157 : Nat := 4983230072969 + 3 ^ 40 * 314157 * 2
def baseEnd_314157 : Nat := 3540489261445982836603

theorem tailTrace_314157 : CollatzResearch.WordTrace tailWord_314157 prefixEnd_314157 3540489261445982836603 := by
  unfold tailWord_314157
  simp only [CollatzResearch.WordTrace]
  refine ⟨11458247122870317589116725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7638831415246878392744483 11458247122870317589116725)
  ·
    refine ⟨1074210667769092273979693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11458247122870317589116725 1074210667769092273979693)
    ·
      refine ⟨402829000413409602742385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1074210667769092273979693 402829000413409602742385)
      ·
        refine ⟨302121750310057202056789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402829000413409602742385 302121750310057202056789)
        ·
          refine ⟨3540489261445982836603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 302121750310057202056789 3540489261445982836603)
          ·
            rfl

theorem cell19_314157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 8].length) (baseStart_314157 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314157 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314157 prefixEnd_314157 := by exact prefixLift 314157
  have htrace : WordTrace (prefixWord ++ tailWord_314157) baseStart_314157 baseEnd_314157 := by
    simpa [prefixWord, tailWord_314157, baseEnd_314157] using wordTrace_append hprefix tailTrace_314157
  have hstable : (prefixWord ++ tailWord_314157).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314157).length < 2 ^ (prefixWord ++ tailWord_314157).sum := by decide
  have hdescent : baseEnd_314157 < baseStart_314157 := by decide
  rcases family_descends (prefixWord ++ tailWord_314157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314174 : List Nat := [4, 2, 1, 2, 3, 2, 1, 4]
def baseStart_314174 : Nat := 118140960795 + 314174 * 2 ^ 59
def prefixEnd_314174 : Nat := 4983230072969 + 3 ^ 40 * 314174 * 2
def baseEnd_314174 : Nat := 95598382901190534210457

theorem tailTrace_314174 : CollatzResearch.WordTrace tailWord_314174 prefixEnd_314174 95598382901190534210457 := by
  unfold tailWord_314174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432358395476091186560697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7639244775872486328323717 1432358395476091186560697)
  ·
    refine ⟨1074268796607068389920523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1432358395476091186560697 1074268796607068389920523)
    ·
      refine ⟨1611403194910602584880785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1074268796607068389920523 1611403194910602584880785)
      ·
        refine ⟨1208552396182951938660589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611403194910602584880785 1208552396182951938660589)
        ·
          refine ⟨453207148568606976997721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1208552396182951938660589 453207148568606976997721)
          ·
            refine ⟨339905361426455232748291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 453207148568606976997721 339905361426455232748291)
            ·
              refine ⟨509858042139682849122437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339905361426455232748291 509858042139682849122437)
              ·
                refine ⟨95598382901190534210457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509858042139682849122437 95598382901190534210457)
                ·
                  rfl

theorem cell19_314174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_314174 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314174 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314174 prefixEnd_314174 := by exact prefixLift 314174
  have htrace : WordTrace (prefixWord ++ tailWord_314174) baseStart_314174 baseEnd_314174 := by
    simpa [prefixWord, tailWord_314174, baseEnd_314174] using wordTrace_append hprefix tailTrace_314174
  have hstable : (prefixWord ++ tailWord_314174).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314174).length < 2 ^ (prefixWord ++ tailWord_314174).sum := by decide
  have hdescent : baseEnd_314174 < baseStart_314174 := by decide
  rcases family_descends (prefixWord ++ tailWord_314174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314216 : List Nat := [2, 1, 4, 2, 1, 3, 6]
def baseStart_314216 : Nat := 118140960795 + 314216 * 2 ^ 59
def prefixEnd_314216 : Nat := 4983230072969 + 3 ^ 40 * 314216 * 2
def baseEnd_314216 : Nat := 31870387621382293759003

theorem tailTrace_314216 : CollatzResearch.WordTrace tailWord_314216 prefixEnd_314216 31870387621382293759003 := by
  unfold tailWord_314216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730199514828285332757251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7640266019771047110343001 5730199514828285332757251)
  ·
    refine ⟨8595299272242427999135877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5730199514828285332757251 8595299272242427999135877)
    ·
      refine ⟨1611618613545455249837977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8595299272242427999135877 1611618613545455249837977)
      ·
        refine ⟨1208713960159091437378483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1611618613545455249837977 1208713960159091437378483)
        ·
          refine ⟨1813070940238637156067725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1208713960159091437378483 1813070940238637156067725)
          ·
            refine ⟨679901602589488933525397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1813070940238637156067725 679901602589488933525397)
            ·
              refine ⟨31870387621382293759003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 679901602589488933525397 31870387621382293759003)
              ·
                rfl

theorem cell19_314216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_314216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314216 prefixEnd_314216 := by exact prefixLift 314216
  have htrace : WordTrace (prefixWord ++ tailWord_314216) baseStart_314216 baseEnd_314216 := by
    simpa [prefixWord, tailWord_314216, baseEnd_314216] using wordTrace_append hprefix tailTrace_314216
  have hstable : (prefixWord ++ tailWord_314216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314216).length < 2 ^ (prefixWord ++ tailWord_314216).sum := by decide
  have hdescent : baseEnd_314216 < baseStart_314216 := by decide
  rcases family_descends (prefixWord ++ tailWord_314216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314250 : List Nat := [3, 1, 2, 4, 1, 3, 2, 3]
def baseStart_314250 : Nat := 118140960795 + 314250 * 2 ^ 59
def prefixEnd_314250 : Nat := 4983230072969 + 3 ^ 40 * 314250 * 2
def baseEnd_314250 : Nat := 95621508548444876521361

theorem tailTrace_314250 : CollatzResearch.WordTrace tailWord_314250 prefixEnd_314250 95621508548444876521361 := by
  unfold tailWord_314250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2865409777883348618063051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7641092741022262981501469 2865409777883348618063051)
  ·
    refine ⟨4298114666825022927094577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2865409777883348618063051 4298114666825022927094577)
    ·
      refine ⟨3223586000118767195320933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4298114666825022927094577 3223586000118767195320933)
      ·
        refine ⟨604422375022268849122675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3223586000118767195320933 604422375022268849122675)
        ·
          refine ⟨906633562533403273684013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604422375022268849122675 906633562533403273684013)
          ·
            refine ⟨339987585950026227631505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906633562533403273684013 339987585950026227631505)
            ·
              refine ⟨254990689462519670723629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339987585950026227631505 254990689462519670723629)
              ·
                refine ⟨95621508548444876521361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254990689462519670723629 95621508548444876521361)
                ·
                  rfl

theorem cell19_314250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_314250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314250 prefixEnd_314250 := by exact prefixLift 314250
  have htrace : WordTrace (prefixWord ++ tailWord_314250) baseStart_314250 baseEnd_314250 := by
    simpa [prefixWord, tailWord_314250, baseEnd_314250] using wordTrace_append hprefix tailTrace_314250
  have hstable : (prefixWord ++ tailWord_314250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314250).length < 2 ^ (prefixWord ++ tailWord_314250).sum := by decide
  have hdescent : baseEnd_314250 < baseStart_314250 := by decide
  rcases family_descends (prefixWord ++ tailWord_314250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314273 : List Nat := [1, 2, 3, 4, 1, 1, 7]
def baseStart_314273 : Nat := 118140960795 + 314273 * 2 ^ 59
def prefixEnd_314273 : Nat := 4983230072969 + 3 ^ 40 * 314273 * 2
def baseEnd_314273 : Nat := 31876169033195879336729

theorem tailTrace_314273 : CollatzResearch.WordTrace tailWord_314273 prefixEnd_314273 31876169033195879336729 := by
  unfold tailWord_314273
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462477990450069400339473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7641651993633379600226315 11462477990450069400339473)
  ·
    refine ⟨8596858492837552050254605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11462477990450069400339473 8596858492837552050254605)
    ·
      refine ⟨3223821934814082018845477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8596858492837552050254605 3223821934814082018845477)
      ·
        refine ⟨604466612777640378533527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3223821934814082018845477 604466612777640378533527)
        ·
          refine ⟨906699919166460567800291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604466612777640378533527 906699919166460567800291)
          ·
            refine ⟨1360049878749690851700437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 906699919166460567800291 1360049878749690851700437)
            ·
              refine ⟨31876169033195879336729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1360049878749690851700437 31876169033195879336729)
              ·
                rfl

theorem cell19_314273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 7].length) (baseStart_314273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314273 prefixEnd_314273 := by exact prefixLift 314273
  have htrace : WordTrace (prefixWord ++ tailWord_314273) baseStart_314273 baseEnd_314273 := by
    simpa [prefixWord, tailWord_314273, baseEnd_314273] using wordTrace_append hprefix tailTrace_314273
  have hstable : (prefixWord ++ tailWord_314273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314273).length < 2 ^ (prefixWord ++ tailWord_314273).sum := by decide
  have hdescent : baseEnd_314273 < baseStart_314273 := by decide
  rcases family_descends (prefixWord ++ tailWord_314273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314275 : List Nat := [1, 1, 1, 4, 1, 2, 9]
def baseStart_314275 : Nat := 118140960795 + 314275 * 2 ^ 59
def prefixEnd_314275 : Nat := 4983230072969 + 3 ^ 40 * 314275 * 2
def baseEnd_314275 : Nat := 31876371889750741988579

theorem tailTrace_314275 : CollatzResearch.WordTrace tailWord_314275 prefixEnd_314275 31876371889750741988579 := by
  unfold tailWord_314275
  simp only [CollatzResearch.WordTrace]
  refine ⟨11462550936442823741912279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7641700624295215827941519 11462550936442823741912279)
  ·
    refine ⟨17193826404664235612868419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11462550936442823741912279 17193826404664235612868419)
    ·
      refine ⟨25790739606996353419302629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17193826404664235612868419 25790739606996353419302629)
      ·
        refine ⟨4835763676311816266119243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25790739606996353419302629 4835763676311816266119243)
        ·
          refine ⟨7253645514467724399178865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4835763676311816266119243 7253645514467724399178865)
          ·
            refine ⟨5440234135850793299384149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7253645514467724399178865 5440234135850793299384149)
            ·
              refine ⟨31876371889750741988579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5440234135850793299384149 31876371889750741988579)
              ·
                rfl

theorem cell19_314275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_314275 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314275 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314275 prefixEnd_314275 := by exact prefixLift 314275
  have htrace : WordTrace (prefixWord ++ tailWord_314275) baseStart_314275 baseEnd_314275 := by
    simpa [prefixWord, tailWord_314275, baseEnd_314275] using wordTrace_append hprefix tailTrace_314275
  have hstable : (prefixWord ++ tailWord_314275).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314275).length < 2 ^ (prefixWord ++ tailWord_314275).sum := by decide
  have hdescent : baseEnd_314275 < baseStart_314275 := by decide
  rcases family_descends (prefixWord ++ tailWord_314275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314425 : List Nat := [1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_314425 : Nat := 118140960795 + 314425 * 2 ^ 59
def prefixEnd_314425 : Nat := 4983230072969 + 3 ^ 40 * 314425 * 2
def baseEnd_314425 : Nat := 95674758394096322631995

theorem tailTrace_314425 : CollatzResearch.WordTrace tailWord_314425 prefixEnd_314425 95674758394096322631995 := by
  unfold tailWord_314425
  simp only [CollatzResearch.WordTrace]
  refine ⟨11468021885899399359872729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7645347923932932906581819 11468021885899399359872729)
  ·
    refine ⟨8601016414424549519904547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11468021885899399359872729 8601016414424549519904547)
    ·
      refine ⟨12901524621636824279856821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8601016414424549519904547 12901524621636824279856821)
      ·
        refine ⟨1209517933278452276236577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12901524621636824279856821 1209517933278452276236577)
        ·
          refine ⟨907138449958839207177433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209517933278452276236577 907138449958839207177433)
          ·
            refine ⟨680353837469129405383075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907138449958839207177433 680353837469129405383075)
            ·
              refine ⟨1020530756203694108074613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 680353837469129405383075 1020530756203694108074613)
              ·
                refine ⟨95674758394096322631995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1020530756203694108074613 95674758394096322631995)
                ·
                  rfl

theorem cell19_314425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_314425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314425 prefixEnd_314425 := by exact prefixLift 314425
  have htrace : WordTrace (prefixWord ++ tailWord_314425) baseStart_314425 baseEnd_314425 := by
    simpa [prefixWord, tailWord_314425, baseEnd_314425] using wordTrace_append hprefix tailTrace_314425
  have hstable : (prefixWord ++ tailWord_314425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314425).length < 2 ^ (prefixWord ++ tailWord_314425).sum := by decide
  have hdescent : baseEnd_314425 < baseStart_314425 := by decide
  rcases family_descends (prefixWord ++ tailWord_314425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314465 : List Nat := [1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_314465 : Nat := 118140960795 + 314465 * 2 ^ 59
def prefixEnd_314465 : Nat := 4983230072969 + 3 ^ 40 * 314465 * 2
def baseEnd_314465 : Nat := 95686929787388081742997

theorem tailTrace_314465 : CollatzResearch.WordTrace tailWord_314465 prefixEnd_314465 95686929787388081742997 := by
  unfold tailWord_314465
  simp only [CollatzResearch.WordTrace]
  refine ⟨11469480805754486191328849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7646320537169657460885899 11469480805754486191328849)
  ·
    refine ⟨8602110604315864643496637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11469480805754486191328849 8602110604315864643496637)
    ·
      refine ⟨3225791476618449241311239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8602110604315864643496637 3225791476618449241311239)
      ·
        refine ⟨4838687214927673861966859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3225791476618449241311239 4838687214927673861966859)
        ·
          refine ⟨7258030822391510792950289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4838687214927673861966859 7258030822391510792950289)
          ·
            refine ⟨5443523116793633094712717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7258030822391510792950289 5443523116793633094712717)
            ·
              refine ⟨2041321168797612410517269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5443523116793633094712717 2041321168797612410517269)
              ·
                refine ⟨95686929787388081742997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2041321168797612410517269 95686929787388081742997)
                ·
                  rfl

theorem cell19_314465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_314465 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314465 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314465 prefixEnd_314465 := by exact prefixLift 314465
  have htrace : WordTrace (prefixWord ++ tailWord_314465) baseStart_314465 baseEnd_314465 := by
    simpa [prefixWord, tailWord_314465, baseEnd_314465] using wordTrace_append hprefix tailTrace_314465
  have hstable : (prefixWord ++ tailWord_314465).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314465).length < 2 ^ (prefixWord ++ tailWord_314465).sum := by decide
  have hdescent : baseEnd_314465 < baseStart_314465 := by decide
  rcases family_descends (prefixWord ++ tailWord_314465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314501 : List Nat := [1, 3, 1, 1, 7, 6]
def baseStart_314501 : Nat := 118140960795 + 314501 * 2 ^ 59
def prefixEnd_314501 : Nat := 4983230072969 + 3 ^ 40 * 314501 * 2
def baseEnd_314501 : Nat := 10633098226816740549211

theorem tailTrace_314501 : CollatzResearch.WordTrace tailWord_314501 prefixEnd_314501 10633098226816740549211 := by
  unfold tailWord_314501
  simp only [CollatzResearch.WordTrace]
  refine ⟨11470793833624064339639357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7647195889082709559759571 11470793833624064339639357)
  ·
    refine ⟨4301547687609024127364759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11470793833624064339639357 4301547687609024127364759)
    ·
      refine ⟨6452321531413536191047139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4301547687609024127364759 6452321531413536191047139)
      ·
        refine ⟨9678482297120304286570709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6452321531413536191047139 9678482297120304286570709)
        ·
          refine ⟨226839428838757131716501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9678482297120304286570709 226839428838757131716501)
          ·
            refine ⟨10633098226816740549211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 226839428838757131716501 10633098226816740549211)
            ·
              rfl

theorem cell19_314501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_314501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314501 prefixEnd_314501 := by exact prefixLift 314501
  have htrace : WordTrace (prefixWord ++ tailWord_314501) baseStart_314501 baseEnd_314501 := by
    simpa [prefixWord, tailWord_314501, baseEnd_314501] using wordTrace_append hprefix tailTrace_314501
  have hstable : (prefixWord ++ tailWord_314501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314501).length < 2 ^ (prefixWord ++ tailWord_314501).sum := by decide
  have hdescent : baseEnd_314501 < baseStart_314501 := by decide
  rcases family_descends (prefixWord ++ tailWord_314501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314520 : List Nat := [2, 1, 2, 4, 2, 1, 3, 4]
def baseStart_314520 : Nat := 118140960795 + 314520 * 2 ^ 59
def prefixEnd_314520 : Nat := 4983230072969 + 3 ^ 40 * 314520 * 2
def baseEnd_314520 : Nat := 95703665453164250520625

theorem tailTrace_314520 : CollatzResearch.WordTrace tailWord_314520 prefixEnd_314520 95703665453164250520625 := by
  unfold tailWord_314520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5735743410277615292290507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7647657880370153723054009 5735743410277615292290507)
  ·
    refine ⟨8603615115416422938435761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5735743410277615292290507 8603615115416422938435761)
    ·
      refine ⟨6452711336562317203826821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8603615115416422938435761 6452711336562317203826821)
      ·
        refine ⟨1209883375605434475717529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6452711336562317203826821 1209883375605434475717529)
        ·
          refine ⟨907412531704075856788147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1209883375605434475717529 907412531704075856788147)
          ·
            refine ⟨1361118797556113785182221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907412531704075856788147 1361118797556113785182221)
            ·
              refine ⟨510419549083542669443333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1361118797556113785182221 510419549083542669443333)
              ·
                refine ⟨95703665453164250520625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510419549083542669443333 95703665453164250520625)
                ·
                  rfl

theorem cell19_314520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_314520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314520 prefixEnd_314520 := by exact prefixLift 314520
  have htrace : WordTrace (prefixWord ++ tailWord_314520) baseStart_314520 baseEnd_314520 := by
    simpa [prefixWord, tailWord_314520, baseEnd_314520] using wordTrace_append hprefix tailTrace_314520
  have hstable : (prefixWord ++ tailWord_314520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314520).length < 2 ^ (prefixWord ++ tailWord_314520).sum := by decide
  have hdescent : baseEnd_314520 < baseStart_314520 := by decide
  rcases family_descends (prefixWord ++ tailWord_314520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314558 : List Nat := [4, 2, 1, 1, 3, 2, 6]
def baseStart_314558 : Nat := 118140960795 + 314558 * 2 ^ 59
def prefixEnd_314558 : Nat := 4983230072969 + 3 ^ 40 * 314558 * 2
def baseEnd_314558 : Nat := 31905076092263807225359

theorem tailTrace_314558 : CollatzResearch.WordTrace tailWord_314558 prefixEnd_314558 31905076092263807225359 := by
  unfold tailWord_314558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1434109099302195384308041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7648581862945042049642885 1434109099302195384308041)
  ·
    refine ⟨1075581824476646538231031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1434109099302195384308041 1075581824476646538231031)
    ·
      refine ⟨1613372736714969807346547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1075581824476646538231031 1613372736714969807346547)
      ·
        refine ⟨2420059105072454711019821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1613372736714969807346547 2420059105072454711019821)
        ·
          refine ⟨907522164402170516632433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2420059105072454711019821 907522164402170516632433)
          ·
            refine ⟨680641623301627887474325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 907522164402170516632433 680641623301627887474325)
            ·
              refine ⟨31905076092263807225359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 680641623301627887474325 31905076092263807225359)
              ·
                rfl

theorem cell19_314558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_314558 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314558 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314558 prefixEnd_314558 := by exact prefixLift 314558
  have htrace : WordTrace (prefixWord ++ tailWord_314558) baseStart_314558 baseEnd_314558 := by
    simpa [prefixWord, tailWord_314558, baseEnd_314558] using wordTrace_append hprefix tailTrace_314558
  have hstable : (prefixWord ++ tailWord_314558).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314558).length < 2 ^ (prefixWord ++ tailWord_314558).sum := by decide
  have hdescent : baseEnd_314558 < baseStart_314558 := by decide
  rcases family_descends (prefixWord ++ tailWord_314558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314596 : List Nat := [2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_314596 : Nat := 118140960795 + 314596 * 2 ^ 59
def prefixEnd_314596 : Nat := 4983230072969 + 3 ^ 40 * 314596 * 2
def baseEnd_314596 : Nat := 95726791100418592831529

theorem tailTrace_314596 : CollatzResearch.WordTrace tailWord_314596 prefixEnd_314596 95726791100418592831529 := by
  unfold tailWord_314596
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737129384139947782173821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7649505845519930376231761 5737129384139947782173821)
  ·
    refine ⟨2151423519052480418315183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5737129384139947782173821 2151423519052480418315183)
    ·
      refine ⟨3227135278578720627472775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151423519052480418315183 3227135278578720627472775)
      ·
        refine ⟨4840702917868080941209163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227135278578720627472775 4840702917868080941209163)
        ·
          refine ⟨7261054376802121411813745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4840702917868080941209163 7261054376802121411813745)
          ·
            refine ⟨5445790782601591058860309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7261054376802121411813745 5445790782601591058860309)
            ·
              refine ⟨255271442934449580884077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5445790782601591058860309 255271442934449580884077)
              ·
                refine ⟨95726791100418592831529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255271442934449580884077 95726791100418592831529)
                ·
                  rfl

theorem cell19_314596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_314596 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314596 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314596 prefixEnd_314596 := by exact prefixLift 314596
  have htrace : WordTrace (prefixWord ++ tailWord_314596) baseStart_314596 baseEnd_314596 := by
    simpa [prefixWord, tailWord_314596, baseEnd_314596] using wordTrace_append hprefix tailTrace_314596
  have hstable : (prefixWord ++ tailWord_314596).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314596).length < 2 ^ (prefixWord ++ tailWord_314596).sum := by decide
  have hdescent : baseEnd_314596 < baseStart_314596 := by decide
  rcases family_descends (prefixWord ++ tailWord_314596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314636 : List Nat := [2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_314636 : Nat := 118140960795 + 314636 * 2 ^ 59
def prefixEnd_314636 : Nat := 4983230072969 + 3 ^ 40 * 314636 * 2
def baseEnd_314636 : Nat := 95738962493710351942531

theorem tailTrace_314636 : CollatzResearch.WordTrace tailWord_314636 prefixEnd_314636 95738962493710351942531 := by
  unfold tailWord_314636
  simp only [CollatzResearch.WordTrace]
  refine ⟨5737858844067491197901881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7650478458756654930535841 5737858844067491197901881)
  ·
    refine ⟨4303394133050618398426411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5737858844067491197901881 4303394133050618398426411)
    ·
      refine ⟨6455091199575927597639617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4303394133050618398426411 6455091199575927597639617)
      ·
        refine ⟨4841318399681945698229713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6455091199575927597639617 4841318399681945698229713)
        ·
          refine ⟨3630988799761459273672285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4841318399681945698229713 3630988799761459273672285)
          ·
            refine ⟨1361620799910547227627107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3630988799761459273672285 1361620799910547227627107)
            ·
              refine ⟨2042431199865820841440661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1361620799910547227627107 2042431199865820841440661)
              ·
                refine ⟨95738962493710351942531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2042431199865820841440661 95738962493710351942531)
                ·
                  rfl

theorem cell19_314636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_314636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314636 prefixEnd_314636 := by exact prefixLift 314636
  have htrace : WordTrace (prefixWord ++ tailWord_314636) baseStart_314636 baseEnd_314636 := by
    simpa [prefixWord, tailWord_314636, baseEnd_314636] using wordTrace_append hprefix tailTrace_314636
  have hstable : (prefixWord ++ tailWord_314636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314636).length < 2 ^ (prefixWord ++ tailWord_314636).sum := by decide
  have hdescent : baseEnd_314636 < baseStart_314636 := by decide
  rcases family_descends (prefixWord ++ tailWord_314636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314653 : List Nat := [1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_314653 : Nat := 118140960795 + 314653 * 2 ^ 59
def prefixEnd_314653 : Nat := 4983230072969 + 3 ^ 40 * 314653 * 2
def baseEnd_314653 : Nat := 95744135335859349564707

theorem tailTrace_314653 : CollatzResearch.WordTrace tailWord_314653 prefixEnd_314653 95744135335859349564707 := by
  unfold tailWord_314653
  simp only [CollatzResearch.WordTrace]
  refine ⟨11476337729073394299172613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7650891819382262866115075 11476337729073394299172613)
  ·
    refine ⟨2151813324201261431094865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11476337729073394299172613 2151813324201261431094865)
    ·
      refine ⟨1613859993150946073321149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2151813324201261431094865 1613859993150946073321149)
      ·
        refine ⟨605197497431604777495431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1613859993150946073321149 605197497431604777495431)
        ·
          refine ⟨907796246147407166243147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605197497431604777495431 907796246147407166243147)
          ·
            refine ⟨1361694369221110749364721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 907796246147407166243147 1361694369221110749364721)
            ·
              refine ⟨1021270776915833062023541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1361694369221110749364721 1021270776915833062023541)
              ·
                refine ⟨95744135335859349564707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021270776915833062023541 95744135335859349564707)
                ·
                  rfl

theorem cell19_314653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_314653 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314653 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314653 prefixEnd_314653 := by exact prefixLift 314653
  have htrace : WordTrace (prefixWord ++ tailWord_314653) baseStart_314653 baseEnd_314653 := by
    simpa [prefixWord, tailWord_314653, baseEnd_314653] using wordTrace_append hprefix tailTrace_314653
  have hstable : (prefixWord ++ tailWord_314653).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314653).length < 2 ^ (prefixWord ++ tailWord_314653).sum := by decide
  have hdescent : baseEnd_314653 < baseStart_314653 := by decide
  rcases family_descends (prefixWord ++ tailWord_314653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314674 : List Nat := [3, 2, 1, 1, 4, 8]
def baseStart_314674 : Nat := 118140960795 + 314674 * 2 ^ 59
def prefixEnd_314674 : Nat := 4983230072969 + 3 ^ 40 * 314674 * 2
def baseEnd_314674 : Nat := 10638947257481947010887

theorem tailTrace_314674 : CollatzResearch.WordTrace tailWord_314674 prefixEnd_314674 10638947257481947010887 := by
  unfold tailWord_314674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2869275915499328721421769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7651402441331543257124717 2869275915499328721421769)
  ·
    refine ⟨2151956936624496541066327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2869275915499328721421769 2151956936624496541066327)
    ·
      refine ⟨3227935404936744811599491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2151956936624496541066327 3227935404936744811599491)
      ·
        refine ⟨4841903107405117217399237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3227935404936744811599491 4841903107405117217399237)
        ·
          refine ⟨907856832638459478262357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4841903107405117217399237 907856832638459478262357)
          ·
            refine ⟨10638947257481947010887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 907856832638459478262357 10638947257481947010887)
            ·
              rfl

theorem cell19_314674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_314674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314674 prefixEnd_314674 := by exact prefixLift 314674
  have htrace : WordTrace (prefixWord ++ tailWord_314674) baseStart_314674 baseEnd_314674 := by
    simpa [prefixWord, tailWord_314674, baseEnd_314674] using wordTrace_append hprefix tailTrace_314674
  have hstable : (prefixWord ++ tailWord_314674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314674).length < 2 ^ (prefixWord ++ tailWord_314674).sum := by decide
  have hdescent : baseEnd_314674 < baseStart_314674 := by decide
  rcases family_descends (prefixWord ++ tailWord_314674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314689 : List Nat := [1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_314689 : Nat := 118140960795 + 314689 * 2 ^ 59
def prefixEnd_314689 : Nat := 4983230072969 + 3 ^ 40 * 314689 * 2
def baseEnd_314689 : Nat := 95755089589821932764609

theorem tailTrace_314689 : CollatzResearch.WordTrace tailWord_314689 prefixEnd_314689 95755089589821932764609 := by
  unfold tailWord_314689
  simp only [CollatzResearch.WordTrace]
  refine ⟨11477650756942972447483121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7651767171295314964988747 11477650756942972447483121)
  ·
    refine ⟨8608238067707229335612341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11477650756942972447483121 8608238067707229335612341)
    ·
      refine ⟨807022318847552750213657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8608238067707229335612341 807022318847552750213657)
      ·
        refine ⟨605266739135664562660243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 807022318847552750213657 605266739135664562660243)
        ·
          refine ⟨907900108703496843990365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 605266739135664562660243 907900108703496843990365)
          ·
            refine ⟨340462540763811316496387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 907900108703496843990365 340462540763811316496387)
            ·
              refine ⟨510693811145716974744581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340462540763811316496387 510693811145716974744581)
              ·
                refine ⟨95755089589821932764609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510693811145716974744581 95755089589821932764609)
                ·
                  rfl

theorem cell19_314689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_314689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314689 prefixEnd_314689 := by exact prefixLift 314689
  have htrace : WordTrace (prefixWord ++ tailWord_314689) baseStart_314689 baseEnd_314689 := by
    simpa [prefixWord, tailWord_314689, baseEnd_314689] using wordTrace_append hprefix tailTrace_314689
  have hstable : (prefixWord ++ tailWord_314689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314689).length < 2 ^ (prefixWord ++ tailWord_314689).sum := by decide
  have hdescent : baseEnd_314689 < baseStart_314689 := by decide
  rcases family_descends (prefixWord ++ tailWord_314689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314782 : List Nat := [4, 3, 1, 2, 3, 1, 5]
def baseStart_314782 : Nat := 118140960795 + 314782 * 2 ^ 59
def prefixEnd_314782 : Nat := 4983230072969 + 3 ^ 40 * 314782 * 2
def baseEnd_314782 : Nat := 31927796026408424232563

theorem tailTrace_314782 : CollatzResearch.WordTrace tailWord_314782 prefixEnd_314782 31927796026408424232563 := by
  unfold tailWord_314782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435130343200756166327325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7654028497070699553745733 1435130343200756166327325)
  ·
    refine ⟨538173878700283562372747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1435130343200756166327325 538173878700283562372747)
    ·
      refine ⟨807260818050425343559121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 538173878700283562372747 807260818050425343559121)
      ·
        refine ⟨605445613537819007669341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 807260818050425343559121 605445613537819007669341)
        ·
          refine ⟨227042105076682127876003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 605445613537819007669341 227042105076682127876003)
          ·
            refine ⟨340563157615023191814005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227042105076682127876003 340563157615023191814005)
            ·
              refine ⟨31927796026408424232563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 340563157615023191814005 31927796026408424232563)
              ·
                rfl

theorem cell19_314782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_314782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314782 prefixEnd_314782 := by exact prefixLift 314782
  have htrace : WordTrace (prefixWord ++ tailWord_314782) baseStart_314782 baseEnd_314782 := by
    simpa [prefixWord, tailWord_314782, baseEnd_314782] using wordTrace_append hprefix tailTrace_314782
  have hstable : (prefixWord ++ tailWord_314782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314782).length < 2 ^ (prefixWord ++ tailWord_314782).sum := by decide
  have hdescent : baseEnd_314782 < baseStart_314782 := by decide
  rcases family_descends (prefixWord ++ tailWord_314782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314786 : List Nat := [3, 3, 1, 2, 1, 4, 5]
def baseStart_314786 : Nat := 118140960795 + 314786 * 2 ^ 59
def prefixEnd_314786 : Nat := 4983230072969 + 3 ^ 40 * 314786 * 2
def baseEnd_314786 : Nat := 31928201739518149536263

theorem tailTrace_314786 : CollatzResearch.WordTrace tailWord_314786 prefixEnd_314786 31928201739518149536263 := by
  unfold tailWord_314786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870297159397889503441053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7654125758394372009176141 2870297159397889503441053)
  ·
    refine ⟨1076361434774208563790395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2870297159397889503441053 1076361434774208563790395)
    ·
      refine ⟨1614542152161312845685593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076361434774208563790395 1614542152161312845685593)
      ·
        refine ⟨1210906614120984634264195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614542152161312845685593 1210906614120984634264195)
        ·
          refine ⟨1816359921181476951396293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210906614120984634264195 1816359921181476951396293)
          ·
            refine ⟨340567485221526928386805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1816359921181476951396293 340567485221526928386805)
            ·
              refine ⟨31928201739518149536263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 340567485221526928386805 31928201739518149536263)
              ·
                rfl

theorem cell19_314786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 5].length) (baseStart_314786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314786 prefixEnd_314786 := by exact prefixLift 314786
  have htrace : WordTrace (prefixWord ++ tailWord_314786) baseStart_314786 baseEnd_314786 := by
    simpa [prefixWord, tailWord_314786, baseEnd_314786] using wordTrace_append hprefix tailTrace_314786
  have hstable : (prefixWord ++ tailWord_314786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314786).length < 2 ^ (prefixWord ++ tailWord_314786).sum := by decide
  have hdescent : baseEnd_314786 < baseStart_314786 := by decide
  rcases family_descends (prefixWord ++ tailWord_314786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314805 : List Nat := [1, 3, 3, 2, 2, 2, 2, 4]
def baseStart_314805 : Nat := 118140960795 + 314805 * 2 ^ 59
def prefixEnd_314805 : Nat := 4983230072969 + 3 ^ 40 * 314805 * 2
def baseEnd_314805 : Nat := 95790386630368034186515

theorem tailTrace_314805 : CollatzResearch.WordTrace tailWord_314805 prefixEnd_314805 95790386630368034186515 := by
  unfold tailWord_314805
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481881624522724258705869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7654587749681816172470579 11481881624522724258705869)
  ·
    refine ⟨4305705609196021597014701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11481881624522724258705869 4305705609196021597014701)
    ·
      refine ⟨1614639603448508098880513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4305705609196021597014701 1614639603448508098880513)
      ·
        refine ⟨1210979702586381074160385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614639603448508098880513 1210979702586381074160385)
        ·
          refine ⟨908234776939785805620289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1210979702586381074160385 908234776939785805620289)
          ·
            refine ⟨681176082704839354215217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908234776939785805620289 681176082704839354215217)
            ·
              refine ⟨510882062028629515661413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 681176082704839354215217 510882062028629515661413)
              ·
                refine ⟨95790386630368034186515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510882062028629515661413 95790386630368034186515)
                ·
                  rfl

theorem cell19_314805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 4].length) (baseStart_314805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314805 prefixEnd_314805 := by exact prefixLift 314805
  have htrace : WordTrace (prefixWord ++ tailWord_314805) baseStart_314805 baseEnd_314805 := by
    simpa [prefixWord, tailWord_314805, baseEnd_314805] using wordTrace_append hprefix tailTrace_314805
  have hstable : (prefixWord ++ tailWord_314805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314805).length < 2 ^ (prefixWord ++ tailWord_314805).sum := by decide
  have hdescent : baseEnd_314805 < baseStart_314805 := by decide
  rcases family_descends (prefixWord ++ tailWord_314805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314807 : List Nat := [1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_314807 : Nat := 118140960795 + 314807 * 2 ^ 59
def prefixEnd_314807 : Nat := 4983230072969 + 3 ^ 40 * 314807 * 2
def baseEnd_314807 : Nat := 95790995200032622142065

theorem tailTrace_314807 : CollatzResearch.WordTrace tailWord_314807 prefixEnd_314807 95790995200032622142065 := by
  unfold tailWord_314807
  simp only [CollatzResearch.WordTrace]
  refine ⟨11481954570515478600278675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7654636380343652400185783 11481954570515478600278675)
  ·
    refine ⟨17222931855773217900418013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11481954570515478600278675 17222931855773217900418013)
    ·
      refine ⟨6458599445914956712656755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17222931855773217900418013 6458599445914956712656755)
      ·
        refine ⟨9687899168872435068985133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6458599445914956712656755 9687899168872435068985133)
        ·
          refine ⟨3632962188327163150869425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9687899168872435068985133 3632962188327163150869425)
          ·
            refine ⟨2724721641245372363152069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3632962188327163150869425 2724721641245372363152069)
            ·
              refine ⟨510885307733507318091013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2724721641245372363152069 510885307733507318091013)
              ·
                refine ⟨95790995200032622142065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510885307733507318091013 95790995200032622142065)
                ·
                  rfl

theorem cell19_314807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_314807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314807 prefixEnd_314807 := by exact prefixLift 314807
  have htrace : WordTrace (prefixWord ++ tailWord_314807) baseStart_314807 baseEnd_314807 := by
    simpa [prefixWord, tailWord_314807, baseEnd_314807] using wordTrace_append hprefix tailTrace_314807
  have hstable : (prefixWord ++ tailWord_314807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314807).length < 2 ^ (prefixWord ++ tailWord_314807).sum := by decide
  have hdescent : baseEnd_314807 < baseStart_314807 := by decide
  rcases family_descends (prefixWord ++ tailWord_314807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314826 : List Nat := [3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_314826 : Nat := 118140960795 + 314826 * 2 ^ 59
def prefixEnd_314826 : Nat := 4983230072969 + 3 ^ 40 * 314826 * 2
def baseEnd_314826 : Nat := 95796776611846207719791

theorem tailTrace_314826 : CollatzResearch.WordTrace tailWord_314826 prefixEnd_314826 95796776611846207719791 := by
  unfold tailWord_314826
  simp only [CollatzResearch.WordTrace]
  refine ⟨2870661889361661211305083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7655098371631096563480221 2870661889361661211305083)
  ·
    refine ⟨4305992834042491816957625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2870661889361661211305083 4305992834042491816957625)
    ·
      refine ⟨3229494625531868862718219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4305992834042491816957625 3229494625531868862718219)
      ·
        refine ⟨4844241938297803294077329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3229494625531868862718219 4844241938297803294077329)
        ·
          refine ⟨3633181453723352470557997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4844241938297803294077329 3633181453723352470557997)
          ·
            refine ⟨1362443045146257176459249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3633181453723352470557997 1362443045146257176459249)
            ·
              refine ⟨1021832283859692882344437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1362443045146257176459249 1021832283859692882344437)
              ·
                refine ⟨95796776611846207719791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1021832283859692882344437 95796776611846207719791)
                ·
                  rfl

theorem cell19_314826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_314826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314826 prefixEnd_314826 := by exact prefixLift 314826
  have htrace : WordTrace (prefixWord ++ tailWord_314826) baseStart_314826 baseEnd_314826 := by
    simpa [prefixWord, tailWord_314826, baseEnd_314826] using wordTrace_append hprefix tailTrace_314826
  have hstable : (prefixWord ++ tailWord_314826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314826).length < 2 ^ (prefixWord ++ tailWord_314826).sum := by decide
  have hdescent : baseEnd_314826 < baseStart_314826 := by decide
  rcases family_descends (prefixWord ++ tailWord_314826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314845 : List Nat := [1, 4, 3, 1, 1, 9]
def baseStart_314845 : Nat := 118140960795 + 314845 * 2 ^ 59
def prefixEnd_314845 : Nat := 4983230072969 + 3 ^ 40 * 314845 * 2
def baseEnd_314845 : Nat := 10644728669295532588613

theorem tailTrace_314845 : CollatzResearch.WordTrace tailWord_314845 prefixEnd_314845 10644728669295532588613 := by
  unfold tailWord_314845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11483340544377811090161989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7655560362918540726774659 11483340544377811090161989)
  ·
    refine ⟨2153126352070839579405373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11483340544377811090161989 2153126352070839579405373)
    ·
      refine ⟨807422382026564842277015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2153126352070839579405373 807422382026564842277015)
      ·
        refine ⟨1211133573039847263415523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807422382026564842277015 1211133573039847263415523)
        ·
          refine ⟨1816700359559770895123285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211133573039847263415523 1816700359559770895123285)
          ·
            refine ⟨10644728669295532588613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1816700359559770895123285 10644728669295532588613)
            ·
              rfl

theorem cell19_314845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_314845 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314845 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314845 prefixEnd_314845 := by exact prefixLift 314845
  have htrace : WordTrace (prefixWord ++ tailWord_314845) baseStart_314845 baseEnd_314845 := by
    simpa [prefixWord, tailWord_314845, baseEnd_314845] using wordTrace_append hprefix tailTrace_314845
  have hstable : (prefixWord ++ tailWord_314845).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314845).length < 2 ^ (prefixWord ++ tailWord_314845).sum := by decide
  have hdescent : baseEnd_314845 < baseStart_314845 := by decide
  rcases family_descends (prefixWord ++ tailWord_314845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314864 : List Nat := [2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_314864 : Nat := 118140960795 + 314864 * 2 ^ 59
def prefixEnd_314864 : Nat := 4983230072969 + 3 ^ 40 * 314864 * 2
def baseEnd_314864 : Nat := 95808339435473378875243

theorem tailTrace_314864 : CollatzResearch.WordTrace tailWord_314864 prefixEnd_314864 95808339435473378875243 := by
  unfold tailWord_314864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5742016765654488667551823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7656022354205984890069097 5742016765654488667551823)
  ·
    refine ⟨8613025148481733001327735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5742016765654488667551823 8613025148481733001327735)
    ·
      refine ⟨12919537722722599501991603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8613025148481733001327735 12919537722722599501991603)
      ·
        refine ⟨19379306584083899252987405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12919537722722599501991603 19379306584083899252987405)
        ·
          refine ⟨7267239969031462219870277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19379306584083899252987405 7267239969031462219870277)
          ·
            refine ⟨1362607494193399166225677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7267239969031462219870277 1362607494193399166225677)
            ·
              refine ⟨510977810322524687334629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362607494193399166225677 510977810322524687334629)
              ·
                refine ⟨95808339435473378875243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510977810322524687334629 95808339435473378875243)
                ·
                  rfl

theorem cell19_314864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_314864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314864 prefixEnd_314864 := by exact prefixLift 314864
  have htrace : WordTrace (prefixWord ++ tailWord_314864) baseStart_314864 baseEnd_314864 := by
    simpa [prefixWord, tailWord_314864, baseEnd_314864] using wordTrace_append hprefix tailTrace_314864
  have hstable : (prefixWord ++ tailWord_314864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314864).length < 2 ^ (prefixWord ++ tailWord_314864).sum := by decide
  have hdescent : baseEnd_314864 < baseStart_314864 := by decide
  rcases family_descends (prefixWord ++ tailWord_314864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_314934 : List Nat := [5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_314934 : Nat := 118140960795 + 314934 * 2 ^ 59
def prefixEnd_314934 : Nat := 4983230072969 + 3 ^ 40 * 314934 * 2
def baseEnd_314934 : Nat := 95829639373733957319497

theorem tailTrace_314934 : CollatzResearch.WordTrace tailWord_314934 prefixEnd_314934 95829639373733957319497 := by
  unfold tailWord_314934
  simp only [CollatzResearch.WordTrace]
  refine ⟨717911665065961205634491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7657724427370252860101237 717911665065961205634491)
  ·
    refine ⟨1076867497598941808451737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717911665065961205634491 1076867497598941808451737)
    ·
      refine ⟨807650623199206356338803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076867497598941808451737 807650623199206356338803)
      ·
        refine ⟨1211475934798809534508205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807650623199206356338803 1211475934798809534508205)
        ·
          refine ⟨454303475549553575440577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1211475934798809534508205 454303475549553575440577)
          ·
            refine ⟨340727606662165181580433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454303475549553575440577 340727606662165181580433)
            ·
              refine ⟨255545704996623886185325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340727606662165181580433 255545704996623886185325)
              ·
                refine ⟨95829639373733957319497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255545704996623886185325 95829639373733957319497)
                ·
                  rfl

theorem cell19_314934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_314934 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_314934 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_314934 prefixEnd_314934 := by exact prefixLift 314934
  have htrace : WordTrace (prefixWord ++ tailWord_314934) baseStart_314934 baseEnd_314934 := by
    simpa [prefixWord, tailWord_314934, baseEnd_314934] using wordTrace_append hprefix tailTrace_314934
  have hstable : (prefixWord ++ tailWord_314934).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_314934).length < 2 ^ (prefixWord ++ tailWord_314934).sum := by decide
  have hdescent : baseEnd_314934 < baseStart_314934 := by decide
  rcases family_descends (prefixWord ++ tailWord_314934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315016 : List Nat := [2, 1, 3, 5, 8]
def baseStart_315016 : Nat := 118140960795 + 315016 * 2 ^ 59
def prefixEnd_315016 : Nat := 4983230072969 + 3 ^ 40 * 315016 * 2
def baseEnd_315016 : Nat := 3550170027036372722113

theorem tailTrace_315016 : CollatzResearch.WordTrace tailWord_315016 prefixEnd_315016 3550170027036372722113 := by
  unfold tailWord_315016
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744788713379153647318451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7659718284505538196424601 5744788713379153647318451)
  ·
    refine ⟨8617183070068730470977677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5744788713379153647318451 8617183070068730470977677)
    ·
      refine ⟨3231443651275773926616629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8617183070068730470977677 3231443651275773926616629)
      ·
        refine ⟨302947842307103805620309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3231443651275773926616629 302947842307103805620309)
        ·
          refine ⟨3550170027036372722113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 302947842307103805620309 3550170027036372722113)
          ·
            rfl

theorem cell19_315016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 8].length) (baseStart_315016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315016 prefixEnd_315016 := by exact prefixLift 315016
  have htrace : WordTrace (prefixWord ++ tailWord_315016) baseStart_315016 baseEnd_315016 := by
    simpa [prefixWord, tailWord_315016, baseEnd_315016] using wordTrace_append hprefix tailTrace_315016
  have hstable : (prefixWord ++ tailWord_315016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315016).length < 2 ^ (prefixWord ++ tailWord_315016).sum := by decide
  have hdescent : baseEnd_315016 < baseStart_315016 := by decide
  rcases family_descends (prefixWord ++ tailWord_315016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315056 : List Nat := [2, 1, 1, 1, 2, 1, 4, 7]
def baseStart_315056 : Nat := 118140960795 + 315056 * 2 ^ 59
def prefixEnd_315056 : Nat := 4983230072969 + 3 ^ 40 * 315056 * 2
def baseEnd_315056 : Nat := 95866762123273822608053

theorem tailTrace_315056 : CollatzResearch.WordTrace tailWord_315056 prefixEnd_315056 95866762123273822608053 := by
  unfold tailWord_315056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745518173306697063046511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7660690897742262750728681 5745518173306697063046511)
  ·
    refine ⟨8618277259960045594569767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5745518173306697063046511 8618277259960045594569767)
    ·
      refine ⟨12927415889940068391854651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618277259960045594569767 12927415889940068391854651)
      ·
        refine ⟨19391123834910102587781977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12927415889940068391854651 19391123834910102587781977)
        ·
          refine ⟨14543342876182576940836483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19391123834910102587781977 14543342876182576940836483)
          ·
            refine ⟨21815014314273865411254725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14543342876182576940836483 21815014314273865411254725)
            ·
              refine ⟨4090315183926349764610261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21815014314273865411254725 4090315183926349764610261)
              ·
                refine ⟨95866762123273822608053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4090315183926349764610261 95866762123273822608053)
                ·
                  rfl

theorem cell19_315056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_315056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315056 prefixEnd_315056 := by exact prefixLift 315056
  have htrace : WordTrace (prefixWord ++ tailWord_315056) baseStart_315056 baseEnd_315056 := by
    simpa [prefixWord, tailWord_315056, baseEnd_315056] using wordTrace_append hprefix tailTrace_315056
  have hstable : (prefixWord ++ tailWord_315056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315056).length < 2 ^ (prefixWord ++ tailWord_315056).sum := by decide
  have hdescent : baseEnd_315056 < baseStart_315056 := by decide
  rcases family_descends (prefixWord ++ tailWord_315056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315107 : List Nat := [1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_315107 : Nat := 118140960795 + 315107 * 2 ^ 59
def prefixEnd_315107 : Nat := 4983230072969 + 3 ^ 40 * 315107 * 2
def baseEnd_315107 : Nat := 95882280649720815474581

theorem tailTrace_315107 : CollatzResearch.WordTrace tailWord_315107 prefixEnd_315107 95882280649720815474581 := by
  unfold tailWord_315107
  simp only [CollatzResearch.WordTrace]
  refine ⟨11492896469428629836199575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7661930979619086557466383 11492896469428629836199575)
  ·
    refine ⟨17239344704142944754299363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11492896469428629836199575 17239344704142944754299363)
    ·
      refine ⟨25859017056214417131449045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17239344704142944754299363 25859017056214417131449045)
      ·
        refine ⟨606070712255025401518337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25859017056214417131449045 606070712255025401518337)
        ·
          refine ⟨454553034191269051138753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606070712255025401518337 454553034191269051138753)
          ·
            refine ⟨340914775643451788354065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454553034191269051138753 340914775643451788354065)
            ·
              refine ⟨255686081732588841265549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340914775643451788354065 255686081732588841265549)
              ·
                refine ⟨95882280649720815474581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255686081732588841265549 95882280649720815474581)
                ·
                  rfl

theorem cell19_315107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_315107 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315107 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315107 prefixEnd_315107 := by exact prefixLift 315107
  have htrace : WordTrace (prefixWord ++ tailWord_315107) baseStart_315107 baseEnd_315107 := by
    simpa [prefixWord, tailWord_315107, baseEnd_315107] using wordTrace_append hprefix tailTrace_315107
  have hstable : (prefixWord ++ tailWord_315107).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315107).length < 2 ^ (prefixWord ++ tailWord_315107).sum := by decide
  have hdescent : baseEnd_315107 < baseStart_315107 := by decide
  rcases family_descends (prefixWord ++ tailWord_315107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315187 : List Nat := [1, 1, 1, 2, 8, 6]
def baseStart_315187 : Nat := 118140960795 + 315187 * 2 ^ 59
def prefixEnd_315187 : Nat := 4983230072969 + 3 ^ 40 * 315187 * 2
def baseEnd_315187 : Nat := 10656291492922703744065

theorem tailTrace_315187 : CollatzResearch.WordTrace tailWord_315187 prefixEnd_315187 10656291492922703744065 := by
  unfold tailWord_315187
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495814309138803499111815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7663876206092535666074543 11495814309138803499111815)
  ·
    refine ⟨17243721463708205248667723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11495814309138803499111815 17243721463708205248667723)
    ·
      refine ⟨25865582195562307873001585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17243721463708205248667723 25865582195562307873001585)
      ·
        refine ⟨19399186646671730904751189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25865582195562307873001585 19399186646671730904751189)
        ·
          refine ⟨227334218515684346540053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 19399186646671730904751189 227334218515684346540053)
          ·
            refine ⟨10656291492922703744065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 227334218515684346540053 10656291492922703744065)
            ·
              rfl

theorem cell19_315187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 6].length) (baseStart_315187 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315187 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315187 prefixEnd_315187 := by exact prefixLift 315187
  have htrace : WordTrace (prefixWord ++ tailWord_315187) baseStart_315187 baseEnd_315187 := by
    simpa [prefixWord, tailWord_315187, baseEnd_315187] using wordTrace_append hprefix tailTrace_315187
  have hstable : (prefixWord ++ tailWord_315187).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315187).length < 2 ^ (prefixWord ++ tailWord_315187).sum := by decide
  have hdescent : baseEnd_315187 < baseStart_315187 := by decide
  rcases family_descends (prefixWord ++ tailWord_315187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315189 : List Nat := [1, 3, 3, 1, 11]
def baseStart_315189 : Nat := 118140960795 + 315189 * 2 ^ 59
def prefixEnd_315189 : Nat := 4983230072969 + 3 ^ 40 * 315189 * 2
def baseEnd_315189 : Nat := 3552119703924774876005

theorem tailTrace_315189 : CollatzResearch.WordTrace tailWord_315189 prefixEnd_315189 3552119703924774876005 := by
  unfold tailWord_315189
  simp only [CollatzResearch.WordTrace]
  refine ⟨11495887255131557840684621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7663924836754371893789747 11495887255131557840684621)
  ·
    refine ⟨4310957720674334190256733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11495887255131557840684621 4310957720674334190256733)
    ·
      refine ⟨1616609145252875321346275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4310957720674334190256733 1616609145252875321346275)
      ·
        refine ⟨2424913717879312982019413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1616609145252875321346275 2424913717879312982019413)
        ·
          refine ⟨3552119703924774876005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2424913717879312982019413 3552119703924774876005)
          ·
            rfl

theorem cell19_315189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 11].length) (baseStart_315189 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315189 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315189 prefixEnd_315189 := by exact prefixLift 315189
  have htrace : WordTrace (prefixWord ++ tailWord_315189) baseStart_315189 baseEnd_315189 := by
    simpa [prefixWord, tailWord_315189, baseEnd_315189] using wordTrace_append hprefix tailTrace_315189
  have hstable : (prefixWord ++ tailWord_315189).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315189).length < 2 ^ (prefixWord ++ tailWord_315189).sum := by decide
  have hdescent : baseEnd_315189 < baseStart_315189 := by decide
  rcases family_descends (prefixWord ++ tailWord_315189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315223 : List Nat := [1, 1, 3, 2, 5, 1, 3, 3]
def baseStart_315223 : Nat := 118140960795 + 315223 * 2 ^ 59
def prefixEnd_315223 : Nat := 4983230072969 + 3 ^ 40 * 315223 * 2
def baseEnd_315223 : Nat := 95917577690266916896487

theorem tailTrace_315223 : CollatzResearch.WordTrace tailWord_315223 prefixEnd_315223 95917577690266916896487 := by
  unfold tailWord_315223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497127337008381647422323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7664751558005587764948215 11497127337008381647422323)
  ·
    refine ⟨17245691005512572471133485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11497127337008381647422323 17245691005512572471133485)
    ·
      refine ⟨6467134127067214676675057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17245691005512572471133485 6467134127067214676675057)
      ·
        refine ⟨4850350595300411007506293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6467134127067214676675057 4850350595300411007506293)
        ·
          refine ⟨454720368309413531953715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4850350595300411007506293 454720368309413531953715)
          ·
            refine ⟨682080552464120297930573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454720368309413531953715 682080552464120297930573)
            ·
              refine ⟨255780207174045111723965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682080552464120297930573 255780207174045111723965)
              ·
                refine ⟨95917577690266916896487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255780207174045111723965 95917577690266916896487)
                ·
                  rfl

theorem cell19_315223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_315223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315223 prefixEnd_315223 := by exact prefixLift 315223
  have htrace : WordTrace (prefixWord ++ tailWord_315223) baseStart_315223 baseEnd_315223 := by
    simpa [prefixWord, tailWord_315223, baseEnd_315223] using wordTrace_append hprefix tailTrace_315223
  have hstable : (prefixWord ++ tailWord_315223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315223).length < 2 ^ (prefixWord ++ tailWord_315223).sum := by decide
  have hdescent : baseEnd_315223 < baseStart_315223 := by decide
  rcases family_descends (prefixWord ++ tailWord_315223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315225 : List Nat := [1, 2, 1, 2, 2, 3, 5, 3]
def baseStart_315225 : Nat := 118140960795 + 315225 * 2 ^ 59
def prefixEnd_315225 : Nat := 4983230072969 + 3 ^ 40 * 315225 * 2
def baseEnd_315225 : Nat := 95918186259931504852037

theorem tailTrace_315225 : CollatzResearch.WordTrace tailWord_315225 prefixEnd_315225 95918186259931504852037 := by
  unfold tailWord_315225
  simp only [CollatzResearch.WordTrace]
  refine ⟨11497200283001135988995129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7664800188667423992663419 11497200283001135988995129)
  ·
    refine ⟨8622900212250851991746347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11497200283001135988995129 8622900212250851991746347)
    ·
      refine ⟨12934350318376277987619521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8622900212250851991746347 12934350318376277987619521)
      ·
        refine ⟨9700762738782208490714641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12934350318376277987619521 9700762738782208490714641)
        ·
          refine ⟨7275572054086656368035981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9700762738782208490714641 7275572054086656368035981)
          ·
            refine ⟨2728339520282496138013493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7275572054086656368035981 2728339520282496138013493)
            ·
              refine ⟨255781830026484012938765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2728339520282496138013493 255781830026484012938765)
              ·
                refine ⟨95918186259931504852037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255781830026484012938765 95918186259931504852037)
                ·
                  rfl

theorem cell19_315225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_315225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315225 prefixEnd_315225 := by exact prefixLift 315225
  have htrace : WordTrace (prefixWord ++ tailWord_315225) baseStart_315225 baseEnd_315225 := by
    simpa [prefixWord, tailWord_315225, baseEnd_315225] using wordTrace_append hprefix tailTrace_315225
  have hstable : (prefixWord ++ tailWord_315225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315225).length < 2 ^ (prefixWord ++ tailWord_315225).sum := by decide
  have hdescent : baseEnd_315225 < baseStart_315225 := by decide
  rcases family_descends (prefixWord ++ tailWord_315225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315242 : List Nat := [3, 1, 3, 4, 1, 1, 6]
def baseStart_315242 : Nat := 118140960795 + 315242 * 2 ^ 59
def prefixEnd_315242 : Nat := 4983230072969 + 3 ^ 40 * 315242 * 2
def baseEnd_315242 : Nat := 31974453034026834158071

theorem tailTrace_315242 : CollatzResearch.WordTrace tailWord_315242 prefixEnd_315242 31974453034026834158071 := by
  unfold tailWord_315242
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874455080984886973090995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7665213549293031928242653 2874455080984886973090995)
  ·
    refine ⟨4311682621477330459636493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874455080984886973090995 4311682621477330459636493)
    ·
      refine ⟨1616880983053998922363685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4311682621477330459636493 1616880983053998922363685)
      ·
        refine ⟨303165184322624797943191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1616880983053998922363685 303165184322624797943191)
        ·
          refine ⟨454747776483937196914787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303165184322624797943191 454747776483937196914787)
          ·
            refine ⟨682121664725905795372181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454747776483937196914787 682121664725905795372181)
            ·
              refine ⟨31974453034026834158071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 682121664725905795372181 31974453034026834158071)
              ·
                rfl

theorem cell19_315242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_315242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315242 prefixEnd_315242 := by exact prefixLift 315242
  have htrace : WordTrace (prefixWord ++ tailWord_315242) baseStart_315242 baseEnd_315242 := by
    simpa [prefixWord, tailWord_315242, baseEnd_315242] using wordTrace_append hprefix tailTrace_315242
  have hstable : (prefixWord ++ tailWord_315242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315242).length < 2 ^ (prefixWord ++ tailWord_315242).sum := by decide
  have hdescent : baseEnd_315242 < baseStart_315242 := by decide
  rcases family_descends (prefixWord ++ tailWord_315242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315316 : List Nat := [2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_315316 : Nat := 118140960795 + 315316 * 2 ^ 59
def prefixEnd_315316 : Nat := 4983230072969 + 3 ^ 40 * 315316 * 2
def baseEnd_315316 : Nat := 95945876179670256829567

theorem tailTrace_315316 : CollatzResearch.WordTrace tailWord_315316 prefixEnd_315316 95945876179670256829567 := by
  unfold tailWord_315316
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750259662835729265278901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7667012883780972353705201 5750259662835729265278901)
  ·
    refine ⟨539086843390849618619897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5750259662835729265278901 539086843390849618619897)
    ·
      refine ⟨404315132543137213964923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 539086843390849618619897 404315132543137213964923)
      ·
        refine ⟨606472698814705820947385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404315132543137213964923 606472698814705820947385)
        ·
          refine ⟨454854524111029365710539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606472698814705820947385 454854524111029365710539)
          ·
            refine ⟨682281786166544048565809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454854524111029365710539 682281786166544048565809)
            ·
              refine ⟨511711339624908036424357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 682281786166544048565809 511711339624908036424357)
              ·
                refine ⟨95945876179670256829567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511711339624908036424357 95945876179670256829567)
                ·
                  rfl

theorem cell19_315316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_315316 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315316 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315316 prefixEnd_315316 := by exact prefixLift 315316
  have htrace : WordTrace (prefixWord ++ tailWord_315316) baseStart_315316 baseEnd_315316 := by
    simpa [prefixWord, tailWord_315316, baseEnd_315316] using wordTrace_append hprefix tailTrace_315316
  have hstable : (prefixWord ++ tailWord_315316).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315316).length < 2 ^ (prefixWord ++ tailWord_315316).sum := by decide
  have hdescent : baseEnd_315316 < baseStart_315316 := by decide
  rcases family_descends (prefixWord ++ tailWord_315316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315356 : List Nat := [2, 2, 6, 1, 8]
def baseStart_315356 : Nat := 118140960795 + 315356 * 2 ^ 59
def prefixEnd_315356 : Nat := 4983230072969 + 3 ^ 40 * 315356 * 2
def baseEnd_315356 : Nat := 3554001761961556145947

theorem tailTrace_315356 : CollatzResearch.WordTrace tailWord_315356 prefixEnd_315356 3554001761961556145947 := by
  unfold tailWord_315356
  simp only [CollatzResearch.WordTrace]
  refine ⟨5750989122763272681006961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7667985497017696908009281 5750989122763272681006961)
  ·
    refine ⟨4313241842072454510755221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5750989122763272681006961 4313241842072454510755221)
    ·
      refine ⟨202183211347146305191651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4313241842072454510755221 202183211347146305191651)
      ·
        refine ⟨303274817020719457787477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202183211347146305191651 303274817020719457787477)
        ·
          refine ⟨3554001761961556145947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 303274817020719457787477 3554001761961556145947)
          ·
            rfl

theorem cell19_315356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 8].length) (baseStart_315356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315356 prefixEnd_315356 := by exact prefixLift 315356
  have htrace : WordTrace (prefixWord ++ tailWord_315356) baseStart_315356 baseEnd_315356 := by
    simpa [prefixWord, tailWord_315356, baseEnd_315356] using wordTrace_append hprefix tailTrace_315356
  have hstable : (prefixWord ++ tailWord_315356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315356).length < 2 ^ (prefixWord ++ tailWord_315356).sum := by decide
  have hdescent : baseEnd_315356 < baseStart_315356 := by decide
  rcases family_descends (prefixWord ++ tailWord_315356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315373 : List Nat := [1, 5, 1, 4, 1, 2, 1, 4]
def baseStart_315373 : Nat := 118140960795 + 315373 * 2 ^ 59
def prefixEnd_315373 : Nat := 4983230072969 + 3 ^ 40 * 315373 * 2
def baseEnd_315373 : Nat := 95963220415111013562745

theorem tailTrace_315373 : CollatzResearch.WordTrace tailWord_315373 prefixEnd_315373 95963220415111013562745 := by
  unfold tailWord_315373
  simp only [CollatzResearch.WordTrace]
  refine ⟨11502598286464957265382773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7668398857643304843588515 11502598286464957265382773)
  ·
    refine ⟨1078368589356089743629635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11502598286464957265382773 1078368589356089743629635)
    ·
      refine ⟨1617552884034134615444453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078368589356089743629635 1617552884034134615444453)
      ·
        refine ⟨303291165756400240395835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1617552884034134615444453 303291165756400240395835)
        ·
          refine ⟨454936748634600360593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303291165756400240395835 454936748634600360593753)
          ·
            refine ⟨341202561475950270445315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454936748634600360593753 341202561475950270445315)
            ·
              refine ⟨511803842213925405667973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341202561475950270445315 511803842213925405667973)
              ·
                refine ⟨95963220415111013562745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 511803842213925405667973 95963220415111013562745)
                ·
                  rfl

theorem cell19_315373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 4].length) (baseStart_315373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315373 prefixEnd_315373 := by exact prefixLift 315373
  have htrace : WordTrace (prefixWord ++ tailWord_315373) baseStart_315373 baseEnd_315373 := by
    simpa [prefixWord, tailWord_315373, baseEnd_315373] using wordTrace_append hprefix tailTrace_315373
  have hstable : (prefixWord ++ tailWord_315373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315373).length < 2 ^ (prefixWord ++ tailWord_315373).sum := by decide
  have hdescent : baseEnd_315373 < baseStart_315373 := by decide
  rcases family_descends (prefixWord ++ tailWord_315373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315415 : List Nat := [1, 1, 3, 5, 2, 1, 6]
def baseStart_315415 : Nat := 118140960795 + 315415 * 2 ^ 59
def prefixEnd_315415 : Nat := 4983230072969 + 3 ^ 40 * 315415 * 2
def baseEnd_315415 : Nat := 31992000126022453543099

theorem tailTrace_315415 : CollatzResearch.WordTrace tailWord_315415 prefixEnd_315415 31992000126022453543099 := by
  unfold tailWord_315415
  simp only [CollatzResearch.WordTrace]
  refine ⟨11504130152312798438411699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7669420101541865625607799 11504130152312798438411699)
  ·
    refine ⟨17256195228469197657617549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11504130152312798438411699 17256195228469197657617549)
    ·
      refine ⟨6471073210675949121606581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17256195228469197657617549 6471073210675949121606581)
      ·
        refine ⟨606663113500870230150617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6471073210675949121606581 606663113500870230150617)
        ·
          refine ⟨454997335125652672612963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606663113500870230150617 454997335125652672612963)
          ·
            refine ⟨682496002688479008919445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454997335125652672612963 682496002688479008919445)
            ·
              refine ⟨31992000126022453543099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 682496002688479008919445 31992000126022453543099)
              ·
                rfl

theorem cell19_315415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_315415 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315415 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315415 prefixEnd_315415 := by exact prefixLift 315415
  have htrace : WordTrace (prefixWord ++ tailWord_315415) baseStart_315415 baseEnd_315415 := by
    simpa [prefixWord, tailWord_315415, baseEnd_315415] using wordTrace_append hprefix tailTrace_315415
  have hstable : (prefixWord ++ tailWord_315415).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315415).length < 2 ^ (prefixWord ++ tailWord_315415).sum := by decide
  have hdescent : baseEnd_315415 < baseStart_315415 := by decide
  rcases family_descends (prefixWord ++ tailWord_315415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315449 : List Nat := [1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_315449 : Nat := 118140960795 + 315449 * 2 ^ 59
def prefixEnd_315449 : Nat := 4983230072969 + 3 ^ 40 * 315449 * 2
def baseEnd_315449 : Nat := 95986346062365355873649

theorem tailTrace_315449 : CollatzResearch.WordTrace tailWord_315449 prefixEnd_315449 95986346062365355873649 := by
  unfold tailWord_315449
  simp only [CollatzResearch.WordTrace]
  refine ⟨11505370234189622245149401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7670246822793081496766267 11505370234189622245149401)
  ·
    refine ⟨8629027675642216683862051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11505370234189622245149401 8629027675642216683862051)
    ·
      refine ⟨12943541513463325025793077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8629027675642216683862051 12943541513463325025793077)
      ·
        refine ⟨1213457016887186721168101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12943541513463325025793077 1213457016887186721168101)
        ·
          refine ⟨227523190666347510219019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1213457016887186721168101 227523190666347510219019)
          ·
            refine ⟨341284785999521265328529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227523190666347510219019 341284785999521265328529)
            ·
              refine ⟨255963589499640948996397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341284785999521265328529 255963589499640948996397)
              ·
                refine ⟨95986346062365355873649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255963589499640948996397 95986346062365355873649)
                ·
                  rfl

theorem cell19_315449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_315449 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315449 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315449 prefixEnd_315449 := by exact prefixLift 315449
  have htrace : WordTrace (prefixWord ++ tailWord_315449) baseStart_315449 baseEnd_315449 := by
    simpa [prefixWord, tailWord_315449, baseEnd_315449] using wordTrace_append hprefix tailTrace_315449
  have hstable : (prefixWord ++ tailWord_315449).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315449).length < 2 ^ (prefixWord ++ tailWord_315449).sum := by decide
  have hdescent : baseEnd_315449 < baseStart_315449 := by decide
  rcases family_descends (prefixWord ++ tailWord_315449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315493 : List Nat := [1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_315493 : Nat := 118140960795 + 315493 * 2 ^ 59
def prefixEnd_315493 : Nat := 4983230072969 + 3 ^ 40 * 315493 * 2
def baseEnd_315493 : Nat := 95999734594986290895751

theorem tailTrace_315493 : CollatzResearch.WordTrace tailWord_315493 prefixEnd_315493 95999734594986290895751 := by
  unfold tailWord_315493
  simp only [CollatzResearch.WordTrace]
  refine ⟨11506975046030217759751133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7671316697353478506500755 11506975046030217759751133)
  ·
    refine ⟨4315115642261331659906675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11506975046030217759751133 4315115642261331659906675)
    ·
      refine ⟨6472673463391997489860013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315115642261331659906675 6472673463391997489860013)
      ·
        refine ⟨2427252548771999058697505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6472673463391997489860013 2427252548771999058697505)
        ·
          refine ⟨1820439411578999294023129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2427252548771999058697505 1820439411578999294023129)
          ·
            refine ⟨1365329558684249470517347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820439411578999294023129 1365329558684249470517347)
            ·
              refine ⟨2047994338026374205776021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1365329558684249470517347 2047994338026374205776021)
              ·
                refine ⟨95999734594986290895751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2047994338026374205776021 95999734594986290895751)
                ·
                  rfl

theorem cell19_315493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_315493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315493 prefixEnd_315493 := by exact prefixLift 315493
  have htrace : WordTrace (prefixWord ++ tailWord_315493) baseStart_315493 baseEnd_315493 := by
    simpa [prefixWord, tailWord_315493, baseEnd_315493] using wordTrace_append hprefix tailTrace_315493
  have hstable : (prefixWord ++ tailWord_315493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315493).length < 2 ^ (prefixWord ++ tailWord_315493).sum := by decide
  have hdescent : baseEnd_315493 < baseStart_315493 := by decide
  rcases family_descends (prefixWord ++ tailWord_315493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315510 : List Nat := [5, 1, 1, 2, 1, 2, 2, 5]
def baseStart_315510 : Nat := 118140960795 + 315510 * 2 ^ 59
def prefixEnd_315510 : Nat := 4983230072969 + 3 ^ 40 * 315510 * 2
def baseEnd_315510 : Nat := 96004907437135288517927

theorem tailTrace_315510 : CollatzResearch.WordTrace tailWord_315510 prefixEnd_315510 96004907437135288517927 := by
  unfold tailWord_315510
  simp only [CollatzResearch.WordTrace]
  refine ⟨719224692935539353944999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7671730057979086442079989 719224692935539353944999)
  ·
    refine ⟨1078837039403309030917499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719224692935539353944999 1078837039403309030917499)
    ·
      refine ⟨1618255559104963546376249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1078837039403309030917499 1618255559104963546376249)
      ·
        refine ⟨1213691669328722659782187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1618255559104963546376249 1213691669328722659782187)
        ·
          refine ⟨1820537503993083989673281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213691669328722659782187 1820537503993083989673281)
          ·
            refine ⟨1365403127994812992254961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1820537503993083989673281 1365403127994812992254961)
            ·
              refine ⟨1024052345996109744191221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1365403127994812992254961 1024052345996109744191221)
              ·
                refine ⟨96004907437135288517927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024052345996109744191221 96004907437135288517927)
                ·
                  rfl

theorem cell19_315510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_315510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315510 prefixEnd_315510 := by exact prefixLift 315510
  have htrace : WordTrace (prefixWord ++ tailWord_315510) baseStart_315510 baseEnd_315510 := by
    simpa [prefixWord, tailWord_315510, baseEnd_315510] using wordTrace_append hprefix tailTrace_315510
  have hstable : (prefixWord ++ tailWord_315510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315510).length < 2 ^ (prefixWord ++ tailWord_315510).sum := by decide
  have hdescent : baseEnd_315510 < baseStart_315510 := by decide
  rcases family_descends (prefixWord ++ tailWord_315510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315546 : List Nat := [3, 1, 1, 5, 2, 2, 1, 4]
def baseStart_315546 : Nat := 118140960795 + 315546 * 2 ^ 59
def prefixEnd_315546 : Nat := 4983230072969 + 3 ^ 40 * 315546 * 2
def baseEnd_315546 : Nat := 96015861691097871717829

theorem tailTrace_315546 : CollatzResearch.WordTrace tailWord_315546 prefixEnd_315546 96015861691097871717829 := by
  unfold tailWord_315546
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877227028709551952857623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7672605409892138540953661 2877227028709551952857623)
  ·
    refine ⟨4315840543064327929286435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877227028709551952857623 4315840543064327929286435)
    ·
      refine ⟨6473760814596491893929653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315840543064327929286435 6473760814596491893929653)
      ·
        refine ⟨606915076368421115055905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6473760814596491893929653 606915076368421115055905)
        ·
          refine ⟨455186307276315836291929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606915076368421115055905 455186307276315836291929)
          ·
            refine ⟨341389730457236877218947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455186307276315836291929 341389730457236877218947)
            ·
              refine ⟨512084595685855315828421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341389730457236877218947 512084595685855315828421)
              ·
                refine ⟨96015861691097871717829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512084595685855315828421 96015861691097871717829)
                ·
                  rfl

theorem cell19_315546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_315546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315546 prefixEnd_315546 := by exact prefixLift 315546
  have htrace : WordTrace (prefixWord ++ tailWord_315546) baseStart_315546 baseEnd_315546 := by
    simpa [prefixWord, tailWord_315546, baseEnd_315546] using wordTrace_append hprefix tailTrace_315546
  have hstable : (prefixWord ++ tailWord_315546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315546).length < 2 ^ (prefixWord ++ tailWord_315546).sum := by decide
  have hdescent : baseEnd_315546 < baseStart_315546 := by decide
  rcases family_descends (prefixWord ++ tailWord_315546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315565 : List Nat := [1, 5, 2, 1, 2, 2, 3, 3]
def baseStart_315565 : Nat := 118140960795 + 315565 * 2 ^ 59
def prefixEnd_315565 : Nat := 4983230072969 + 3 ^ 40 * 315565 * 2
def baseEnd_315565 : Nat := 96021643102911457295555

theorem tailTrace_315565 : CollatzResearch.WordTrace tailWord_315565 prefixEnd_315565 96021643102911457295555 := by
  unfold tailWord_315565
  simp only [CollatzResearch.WordTrace]
  refine ⟨11509601101769374056372149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7673067401179582704248099 11509601101769374056372149)
  ·
    refine ⟨1079025103290878817784889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11509601101769374056372149 1079025103290878817784889)
    ·
      refine ⟨809268827468159113338667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079025103290878817784889 809268827468159113338667)
      ·
        refine ⟨1213903241202238670008001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 809268827468159113338667 1213903241202238670008001)
        ·
          refine ⟨910427430901679002506001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1213903241202238670008001 910427430901679002506001)
          ·
            refine ⟨682820573176259251879501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 910427430901679002506001 682820573176259251879501)
            ·
              refine ⟨256057714941097219454813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 682820573176259251879501 256057714941097219454813)
              ·
                refine ⟨96021643102911457295555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256057714941097219454813 96021643102911457295555)
                ·
                  rfl

theorem cell19_315565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 3].length) (baseStart_315565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315565 prefixEnd_315565 := by exact prefixLift 315565
  have htrace : WordTrace (prefixWord ++ tailWord_315565) baseStart_315565 baseEnd_315565 := by
    simpa [prefixWord, tailWord_315565, baseEnd_315565] using wordTrace_append hprefix tailTrace_315565
  have hstable : (prefixWord ++ tailWord_315565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315565).length < 2 ^ (prefixWord ++ tailWord_315565).sum := by decide
  have hdescent : baseEnd_315565 < baseStart_315565 := by decide
  rcases family_descends (prefixWord ++ tailWord_315565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315624 : List Nat := [2, 1, 4, 1, 2, 2, 4, 3]
def baseStart_315624 : Nat := 118140960795 + 315624 * 2 ^ 59
def prefixEnd_315624 : Nat := 4983230072969 + 3 ^ 40 * 315624 * 2
def baseEnd_315624 : Nat := 96039595908016801984283

theorem tailTrace_315624 : CollatzResearch.WordTrace tailWord_315624 prefixEnd_315624 96039595908016801984283 := by
  unfold tailWord_315624
  simp only [CollatzResearch.WordTrace]
  refine ⟨5755876504277813566384963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7674502005703751421846617 5755876504277813566384963)
  ·
    refine ⟨8633814756416720349577445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5755876504277813566384963 8633814756416720349577445)
    ·
      refine ⟨1618840266828135065545771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8633814756416720349577445 1618840266828135065545771)
      ·
        refine ⟨2428260400242202598318657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618840266828135065545771 2428260400242202598318657)
        ·
          refine ⟨1821195300181651948738993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2428260400242202598318657 1821195300181651948738993)
          ·
            refine ⟨1365896475136238961554245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1821195300181651948738993 1365896475136238961554245)
            ·
              refine ⟨256105589088044805291421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1365896475136238961554245 256105589088044805291421)
              ·
                refine ⟨96039595908016801984283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256105589088044805291421 96039595908016801984283)
                ·
                  rfl

theorem cell19_315624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 3].length) (baseStart_315624 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315624 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315624 prefixEnd_315624 := by exact prefixLift 315624
  have htrace : WordTrace (prefixWord ++ tailWord_315624) baseStart_315624 baseEnd_315624 := by
    simpa [prefixWord, tailWord_315624, baseEnd_315624] using wordTrace_append hprefix tailTrace_315624
  have hstable : (prefixWord ++ tailWord_315624).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315624).length < 2 ^ (prefixWord ++ tailWord_315624).sum := by decide
  have hdescent : baseEnd_315624 < baseStart_315624 := by decide
  rcases family_descends (prefixWord ++ tailWord_315624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315626 : List Nat := [3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_315626 : Nat := 118140960795 + 315626 * 2 ^ 59
def prefixEnd_315626 : Nat := 4983230072969 + 3 ^ 40 * 315626 * 2
def baseEnd_315626 : Nat := 96040204477681389939833

theorem tailTrace_315626 : CollatzResearch.WordTrace tailWord_315626 prefixEnd_315626 96040204477681389939833 := by
  unfold tailWord_315626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877956488637095368585683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7674550636365587649561821 2877956488637095368585683)
  ·
    refine ⟨4316934732955643052878525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877956488637095368585683 4316934732955643052878525)
    ·
      refine ⟨1618850524858366144829447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4316934732955643052878525 1618850524858366144829447)
      ·
        refine ⟨2428275787287549217244171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1618850524858366144829447 2428275787287549217244171)
        ·
          refine ⟨3642413680931323825866257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428275787287549217244171 3642413680931323825866257)
          ·
            refine ⟨2731810260698492869399693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3642413680931323825866257 2731810260698492869399693)
            ·
              refine ⟨1024428847761934826024885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2731810260698492869399693 1024428847761934826024885)
              ·
                refine ⟨96040204477681389939833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1024428847761934826024885 96040204477681389939833)
                ·
                  rfl

theorem cell19_315626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_315626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315626 prefixEnd_315626 := by exact prefixLift 315626
  have htrace : WordTrace (prefixWord ++ tailWord_315626) baseStart_315626 baseEnd_315626 := by
    simpa [prefixWord, tailWord_315626, baseEnd_315626] using wordTrace_append hprefix tailTrace_315626
  have hstable : (prefixWord ++ tailWord_315626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315626).length < 2 ^ (prefixWord ++ tailWord_315626).sum := by decide
  have hdescent : baseEnd_315626 < baseStart_315626 := by decide
  rcases family_descends (prefixWord ++ tailWord_315626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315702 : List Nat := [5, 1, 2, 11]
def baseStart_315702 : Nat := 118140960795 + 315702 * 2 ^ 59
def prefixEnd_315702 : Nat := 4983230072969 + 3 ^ 40 * 315702 * 2
def baseEnd_315702 : Nat := 1185967038579453484577

theorem tailTrace_315702 : CollatzResearch.WordTrace tailWord_315702 prefixEnd_315702 1185967038579453484577 := by
  unfold tailWord_315702
  simp only [CollatzResearch.WordTrace]
  refine ⟨719662368892065403381835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7676398601515364302739573 719662368892065403381835)
  ·
    refine ⟨1079493553338098105072753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 719662368892065403381835 1079493553338098105072753)
    ·
      refine ⟨809620165003573578804565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1079493553338098105072753 809620165003573578804565)
      ·
        refine ⟨1185967038579453484577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 809620165003573578804565 1185967038579453484577)
        ·
          rfl

theorem cell19_315702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 11].length) (baseStart_315702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315702 prefixEnd_315702 := by exact prefixLift 315702
  have htrace : WordTrace (prefixWord ++ tailWord_315702) baseStart_315702 baseEnd_315702 := by
    simpa [prefixWord, tailWord_315702, baseEnd_315702] using wordTrace_append hprefix tailTrace_315702
  have hstable : (prefixWord ++ tailWord_315702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315702).length < 2 ^ (prefixWord ++ tailWord_315702).sum := by decide
  have hdescent : baseEnd_315702 < baseStart_315702 := by decide
  rcases family_descends (prefixWord ++ tailWord_315702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315723 : List Nat := [1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_315723 : Nat := 118140960795 + 315723 * 2 ^ 59
def prefixEnd_315723 : Nat := 4983230072969 + 3 ^ 40 * 315723 * 2
def baseEnd_315723 : Nat := 96069720106413905784013

theorem tailTrace_315723 : CollatzResearch.WordTrace tailWord_315723 prefixEnd_315723 96069720106413905784013 := by
  unfold tailWord_315723
  simp only [CollatzResearch.WordTrace]
  refine ⟨11515363835196967040623823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7676909223464644693749215 11515363835196967040623823)
  ·
    refine ⟨17273045752795450560935735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11515363835196967040623823 17273045752795450560935735)
    ·
      refine ⟨25909568629193175841403603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17273045752795450560935735 25909568629193175841403603)
      ·
        refine ⟨38864352943789763762105405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25909568629193175841403603 38864352943789763762105405)
        ·
          refine ⟨14574132353921161410789527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38864352943789763762105405 14574132353921161410789527)
          ·
            refine ⟨21861198530881742116184291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14574132353921161410789527 21861198530881742116184291)
            ·
              refine ⟨32791797796322613174276437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21861198530881742116184291 32791797796322613174276437)
              ·
                refine ⟨96069720106413905784013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32791797796322613174276437 96069720106413905784013)
                ·
                  rfl

theorem cell19_315723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_315723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315723 prefixEnd_315723 := by exact prefixLift 315723
  have htrace : WordTrace (prefixWord ++ tailWord_315723) baseStart_315723 baseEnd_315723 := by
    simpa [prefixWord, tailWord_315723, baseEnd_315723] using wordTrace_append hprefix tailTrace_315723
  have hstable : (prefixWord ++ tailWord_315723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315723).length < 2 ^ (prefixWord ++ tailWord_315723).sum := by decide
  have hdescent : baseEnd_315723 < baseStart_315723 := by decide
  rcases family_descends (prefixWord ++ tailWord_315723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315875 : List Nat := [1, 1, 1, 6, 10]
def baseStart_315875 : Nat := 118140960795 + 315875 * 2 ^ 59
def prefixEnd_315875 : Nat := 4983230072969 + 3 ^ 40 * 315875 * 2
def baseEnd_315875 : Nat := 3559850792626762607623

theorem tailTrace_315875 : CollatzResearch.WordTrace tailWord_315875 prefixEnd_315875 3559850792626762607623 := by
  unfold tailWord_315875
  simp only [CollatzResearch.WordTrace]
  refine ⟨11520907730646297000157079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7680605153764198000104719 11520907730646297000157079)
  ·
    refine ⟨17281361595969445500235619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11520907730646297000157079 17281361595969445500235619)
    ·
      refine ⟨25922042393954168250353429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17281361595969445500235619 25922042393954168250353429)
      ·
        refine ⟨1215095737216601636735317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25922042393954168250353429 1215095737216601636735317)
        ·
          refine ⟨3559850792626762607623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1215095737216601636735317 3559850792626762607623)
          ·
            rfl

theorem cell19_315875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 10].length) (baseStart_315875 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315875 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315875 prefixEnd_315875 := by exact prefixLift 315875
  have htrace : WordTrace (prefixWord ++ tailWord_315875) baseStart_315875 baseEnd_315875 := by
    simpa [prefixWord, tailWord_315875, baseEnd_315875] using wordTrace_append hprefix tailTrace_315875
  have hstable : (prefixWord ++ tailWord_315875).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315875).length < 2 ^ (prefixWord ++ tailWord_315875).sum := by decide
  have hdescent : baseEnd_315875 < baseStart_315875 := by decide
  rcases family_descends (prefixWord ++ tailWord_315875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315968 : List Nat := [2, 1, 1, 2, 2, 2, 6, 3]
def baseStart_315968 : Nat := 118140960795 + 315968 * 2 ^ 59
def prefixEnd_315968 : Nat := 4983230072969 + 3 ^ 40 * 315968 * 2
def baseEnd_315968 : Nat := 96144269890325930338901

theorem tailTrace_315968 : CollatzResearch.WordTrace tailWord_315968 prefixEnd_315968 96144269890325930338901 := by
  unfold tailWord_315968
  simp only [CollatzResearch.WordTrace]
  refine ⟨5762149859654686941646279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7682866479539582588861705 5762149859654686941646279)
  ·
    refine ⟨8643224789482030412469419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5762149859654686941646279 8643224789482030412469419)
    ·
      refine ⟨12964837184223045618704129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8643224789482030412469419 12964837184223045618704129)
      ·
        refine ⟨9723627888167284214028097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12964837184223045618704129 9723627888167284214028097)
        ·
          refine ⟨7292720916125463160521073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9723627888167284214028097 7292720916125463160521073)
          ·
            refine ⟨5469540687094097370390805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7292720916125463160521073 5469540687094097370390805)
            ·
              refine ⟨256384719707535814237069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5469540687094097370390805 256384719707535814237069)
              ·
                refine ⟨96144269890325930338901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256384719707535814237069 96144269890325930338901)
                ·
                  rfl

theorem cell19_315968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 3].length) (baseStart_315968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315968 prefixEnd_315968 := by exact prefixLift 315968
  have htrace : WordTrace (prefixWord ++ tailWord_315968) baseStart_315968 baseEnd_315968 := by
    simpa [prefixWord, tailWord_315968, baseEnd_315968] using wordTrace_append hprefix tailTrace_315968
  have hstable : (prefixWord ++ tailWord_315968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315968).length < 2 ^ (prefixWord ++ tailWord_315968).sum := by decide
  have hdescent : baseEnd_315968 < baseStart_315968 := by decide
  rcases family_descends (prefixWord ++ tailWord_315968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_315989 : List Nat := [1, 3, 2, 2, 1, 1, 9]
def baseStart_315989 : Nat := 118140960795 + 315989 * 2 ^ 59
def prefixEnd_315989 : Nat := 4983230072969 + 3 ^ 40 * 315989 * 2
def baseEnd_315989 : Nat := 32050219957268034624059

theorem tailTrace_315989 : CollatzResearch.WordTrace tailWord_315989 prefixEnd_315989 32050219957268034624059 := by
  unfold tailWord_315989
  simp only [CollatzResearch.WordTrace]
  refine ⟨11525065652233294469807021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7683377101488862979871347 11525065652233294469807021)
  ·
    refine ⟨4321899619587485426177633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11525065652233294469807021 4321899619587485426177633)
    ·
      refine ⟨3241424714690614069633225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4321899619587485426177633 3241424714690614069633225)
      ·
        refine ⟨2431068536017960552224919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3241424714690614069633225 2431068536017960552224919)
        ·
          refine ⟨3646602804026940828337379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2431068536017960552224919 3646602804026940828337379)
          ·
            refine ⟨5469904206040411242506069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3646602804026940828337379 5469904206040411242506069)
            ·
              refine ⟨32050219957268034624059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5469904206040411242506069 32050219957268034624059)
              ·
                rfl

theorem cell19_315989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_315989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_315989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_315989 prefixEnd_315989 := by exact prefixLift 315989
  have htrace : WordTrace (prefixWord ++ tailWord_315989) baseStart_315989 baseEnd_315989 := by
    simpa [prefixWord, tailWord_315989, baseEnd_315989] using wordTrace_append hprefix tailTrace_315989
  have hstable : (prefixWord ++ tailWord_315989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_315989).length < 2 ^ (prefixWord ++ tailWord_315989).sum := by decide
  have hdescent : baseEnd_315989 < baseStart_315989 := by decide
  rcases family_descends (prefixWord ++ tailWord_315989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316002 : List Nat := [3, 3, 2, 3, 1, 1, 2, 4]
def baseStart_316002 : Nat := 118140960795 + 316002 * 2 ^ 59
def prefixEnd_316002 : Nat := 4983230072969 + 3 ^ 40 * 316002 * 2
def baseEnd_316002 : Nat := 96154615574623925583253

theorem tailTrace_316002 : CollatzResearch.WordTrace tailWord_316002 prefixEnd_316002 96154615574623925583253 := by
  unfold tailWord_316002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2881384950296549422507565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7683693200790798460020173 2881384950296549422507565)
  ·
    refine ⟨1080519356361206033440337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2881384950296549422507565 1080519356361206033440337)
    ·
      refine ⟨810389517270904525080253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1080519356361206033440337 810389517270904525080253)
      ·
        refine ⟨303896068976589196905095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 810389517270904525080253 303896068976589196905095)
        ·
          refine ⟨455844103464883795357643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303896068976589196905095 455844103464883795357643)
          ·
            refine ⟨683766155197325693036465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 455844103464883795357643 683766155197325693036465)
            ·
              refine ⟨512824616397994269777349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 683766155197325693036465 512824616397994269777349)
              ·
                refine ⟨96154615574623925583253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 512824616397994269777349 96154615574623925583253)
                ·
                  rfl

theorem cell19_316002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_316002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316002 prefixEnd_316002 := by exact prefixLift 316002
  have htrace : WordTrace (prefixWord ++ tailWord_316002) baseStart_316002 baseEnd_316002 := by
    simpa [prefixWord, tailWord_316002, baseEnd_316002] using wordTrace_append hprefix tailTrace_316002
  have hstable : (prefixWord ++ tailWord_316002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316002).length < 2 ^ (prefixWord ++ tailWord_316002).sum := by decide
  have hdescent : baseEnd_316002 < baseStart_316002 := by decide
  rcases family_descends (prefixWord ++ tailWord_316002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316078 : List Nat := [4, 1, 4, 1, 1, 2, 3, 3]
def baseStart_316078 : Nat := 118140960795 + 316078 * 2 ^ 59
def prefixEnd_316078 : Nat := 4983230072969 + 3 ^ 40 * 316078 * 2
def baseEnd_316078 : Nat := 96177741221878267894157

theorem tailTrace_316078 : CollatzResearch.WordTrace tailWord_316078 prefixEnd_316078 96177741221878267894157 := by
  unfold tailWord_316078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441038968613857833724611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7685541165940575113197925 1441038968613857833724611)
  ·
    refine ⟨2161558452920786750586917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1441038968613857833724611 2161558452920786750586917)
    ·
      refine ⟨405292209922647515735047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2161558452920786750586917 405292209922647515735047)
      ·
        refine ⟨607938314883971273602571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405292209922647515735047 607938314883971273602571)
        ·
          refine ⟨911907472325956910403857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 607938314883971273602571 911907472325956910403857)
          ·
            refine ⟨683930604244467682802893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 911907472325956910403857 683930604244467682802893)
            ·
              refine ⟨256473976591675381051085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 683930604244467682802893 256473976591675381051085)
              ·
                refine ⟨96177741221878267894157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256473976591675381051085 96177741221878267894157)
                ·
                  rfl

theorem cell19_316078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_316078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316078 prefixEnd_316078 := by exact prefixLift 316078
  have htrace : WordTrace (prefixWord ++ tailWord_316078) baseStart_316078 baseEnd_316078 := by
    simpa [prefixWord, tailWord_316078, baseEnd_316078] using wordTrace_append hprefix tailTrace_316078
  have hstable : (prefixWord ++ tailWord_316078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316078).length < 2 ^ (prefixWord ++ tailWord_316078).sum := by decide
  have hdescent : baseEnd_316078 < baseStart_316078 := by decide
  rcases family_descends (prefixWord ++ tailWord_316078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316122 : List Nat := [3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_316122 : Nat := 118140960795 + 316122 * 2 ^ 59
def prefixEnd_316122 : Nat := 4983230072969 + 3 ^ 40 * 316122 * 2
def baseEnd_316122 : Nat := 96191129754499202916259

theorem tailTrace_316122 : CollatzResearch.WordTrace tailWord_316122 prefixEnd_316122 96191129754499202916259 := by
  unfold tailWord_316122
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882479140187864546099655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7686611040500972122932413 2882479140187864546099655)
  ·
    refine ⟨4323718710281796819149483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2882479140187864546099655 4323718710281796819149483)
    ·
      refine ⟨6485578065422695228724225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4323718710281796819149483 6485578065422695228724225)
      ·
        refine ⟨4864183549067021421543169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6485578065422695228724225 4864183549067021421543169)
        ·
          refine ⟨3648137661800266066157377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4864183549067021421543169 3648137661800266066157377)
          ·
            refine ⟨2736103246350199549618033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3648137661800266066157377 2736103246350199549618033)
            ·
              refine ⟨2052077434762649662213525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2736103246350199549618033 2052077434762649662213525)
              ·
                refine ⟨96191129754499202916259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2052077434762649662213525 96191129754499202916259)
                ·
                  rfl

theorem cell19_316122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_316122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316122 prefixEnd_316122 := by exact prefixLift 316122
  have htrace : WordTrace (prefixWord ++ tailWord_316122) baseStart_316122 baseEnd_316122 := by
    simpa [prefixWord, tailWord_316122, baseEnd_316122] using wordTrace_append hprefix tailTrace_316122
  have hstable : (prefixWord ++ tailWord_316122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316122).length < 2 ^ (prefixWord ++ tailWord_316122).sum := by decide
  have hdescent : baseEnd_316122 < baseStart_316122 := by decide
  rcases family_descends (prefixWord ++ tailWord_316122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316158 : List Nat := [4, 2, 2, 1, 2, 1, 7]
def baseStart_316158 : Nat := 118140960795 + 316158 * 2 ^ 59
def prefixEnd_316158 : Nat := 4983230072969 + 3 ^ 40 * 316158 * 2
def baseEnd_316158 : Nat := 32067361336153928705387

theorem tailTrace_316158 : CollatzResearch.WordTrace tailWord_316158 prefixEnd_316158 32067361336153928705387 := by
  unfold tailWord_316158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1441403698577629541588641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7687486392414024221806085 1441403698577629541588641)
  ·
    refine ⟨1081052773933222156191481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1441403698577629541588641 1081052773933222156191481)
    ·
      refine ⟨810789580449916617143611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1081052773933222156191481 810789580449916617143611)
      ·
        refine ⟨1216184370674874925715417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810789580449916617143611 1216184370674874925715417)
        ·
          refine ⟨912138278006156194286563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1216184370674874925715417 912138278006156194286563)
          ·
            refine ⟨1368207417009234291429845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912138278006156194286563 1368207417009234291429845)
            ·
              refine ⟨32067361336153928705387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1368207417009234291429845 32067361336153928705387)
              ·
                rfl

theorem cell19_316158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 7].length) (baseStart_316158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316158 prefixEnd_316158 := by exact prefixLift 316158
  have htrace : WordTrace (prefixWord ++ tailWord_316158) baseStart_316158 baseEnd_316158 := by
    simpa [prefixWord, tailWord_316158, baseEnd_316158] using wordTrace_append hprefix tailTrace_316158
  have hstable : (prefixWord ++ tailWord_316158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316158).length < 2 ^ (prefixWord ++ tailWord_316158).sum := by decide
  have hdescent : baseEnd_316158 < baseStart_316158 := by decide
  rcases family_descends (prefixWord ++ tailWord_316158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316179 : List Nat := [1, 1, 1, 2, 1, 3, 6, 4]
def baseStart_316179 : Nat := 118140960795 + 316179 * 2 ^ 59
def prefixEnd_316179 : Nat := 4983230072969 + 3 ^ 40 * 316179 * 2
def baseEnd_316179 : Nat := 96208473989939959649437

theorem tailTrace_316179 : CollatzResearch.WordTrace tailWord_316179 prefixEnd_316179 96208473989939959649437 := by
  unfold tailWord_316179
  simp only [CollatzResearch.WordTrace]
  refine ⟨11531995521544956919223591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7687997014363304612815727 11531995521544956919223591)
  ·
    refine ⟨17297993282317435378835387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11531995521544956919223591 17297993282317435378835387)
    ·
      refine ⟨25946989923476153068253081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17297993282317435378835387 25946989923476153068253081)
      ·
        refine ⟨19460242442607114801189811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25946989923476153068253081 19460242442607114801189811)
        ·
          refine ⟨29190363663910672201784717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19460242442607114801189811 29190363663910672201784717)
          ·
            refine ⟨10946386373966502075669269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29190363663910672201784717 10946386373966502075669269)
            ·
              refine ⟨513111861279679784796997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 10946386373966502075669269 513111861279679784796997)
              ·
                refine ⟨96208473989939959649437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513111861279679784796997 96208473989939959649437)
                ·
                  rfl

theorem cell19_316179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_316179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316179 prefixEnd_316179 := by exact prefixLift 316179
  have htrace : WordTrace (prefixWord ++ tailWord_316179) baseStart_316179 baseEnd_316179 := by
    simpa [prefixWord, tailWord_316179, baseEnd_316179] using wordTrace_append hprefix tailTrace_316179
  have hstable : (prefixWord ++ tailWord_316179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316179).length < 2 ^ (prefixWord ++ tailWord_316179).sum := by decide
  have hdescent : baseEnd_316179 < baseStart_316179 := by decide
  rcases family_descends (prefixWord ++ tailWord_316179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316228 : List Nat := [2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_316228 : Nat := 118140960795 + 316228 * 2 ^ 59
def prefixEnd_316228 : Nat := 4983230072969 + 3 ^ 40 * 316228 * 2
def baseEnd_316228 : Nat := 96223383946722364560415

theorem tailTrace_316228 : CollatzResearch.WordTrace tailWord_316228 prefixEnd_316228 96223383946722364560415 := by
  unfold tailWord_316228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766891349183719143878669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7689188465578292191838225 5766891349183719143878669)
  ·
    refine ⟨2162584255943894678954501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5766891349183719143878669 2162584255943894678954501)
    ·
      refine ⟨405484547989480252303969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2162584255943894678954501 405484547989480252303969)
      ·
        refine ⟨304113410992110189227977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405484547989480252303969 304113410992110189227977)
        ·
          refine ⟨228085058244082641920983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304113410992110189227977 228085058244082641920983)
          ·
            refine ⟨342127587366123962881475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228085058244082641920983 342127587366123962881475)
            ·
              refine ⟨513191381049185944322213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342127587366123962881475 513191381049185944322213)
              ·
                refine ⟨96223383946722364560415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513191381049185944322213 96223383946722364560415)
                ·
                  rfl

theorem cell19_316228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_316228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316228 prefixEnd_316228 := by exact prefixLift 316228
  have htrace : WordTrace (prefixWord ++ tailWord_316228) baseStart_316228 baseEnd_316228 := by
    simpa [prefixWord, tailWord_316228, baseEnd_316228] using wordTrace_append hprefix tailTrace_316228
  have hstable : (prefixWord ++ tailWord_316228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316228).length < 2 ^ (prefixWord ++ tailWord_316228).sum := by decide
  have hdescent : baseEnd_316228 < baseStart_316228 := by decide
  rcases family_descends (prefixWord ++ tailWord_316228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316306 : List Nat := [3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_316306 : Nat := 118140960795 + 316306 * 2 ^ 59
def prefixEnd_316306 : Nat := 4983230072969 + 3 ^ 40 * 316306 * 2
def baseEnd_316306 : Nat := 96247118163641294826869

theorem tailTrace_316306 : CollatzResearch.WordTrace tailWord_316306 prefixEnd_316306 96247118163641294826869 := by
  unfold tailWord_316306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884156898021214402274193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7691085061389905072731181 2884156898021214402274193)
  ·
    refine ⟨2163117673515910801705645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2884156898021214402274193 2163117673515910801705645)
    ·
      refine ⟨811169127568466550639617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2163117673515910801705645 811169127568466550639617)
      ·
        refine ⟨608376845676349912979713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 811169127568466550639617 608376845676349912979713)
        ·
          refine ⟨456282634257262434734785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 608376845676349912979713 456282634257262434734785)
          ·
            refine ⟨342211975692946826051089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 456282634257262434734785 342211975692946826051089)
            ·
              refine ⟨256658981769710119538317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342211975692946826051089 256658981769710119538317)
              ·
                refine ⟨96247118163641294826869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256658981769710119538317 96247118163641294826869)
                ·
                  rfl

theorem cell19_316306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_316306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316306 prefixEnd_316306 := by exact prefixLift 316306
  have htrace : WordTrace (prefixWord ++ tailWord_316306) baseStart_316306 baseEnd_316306 := by
    simpa [prefixWord, tailWord_316306, baseEnd_316306] using wordTrace_append hprefix tailTrace_316306
  have hstable : (prefixWord ++ tailWord_316306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316306).length < 2 ^ (prefixWord ++ tailWord_316306).sum := by decide
  have hdescent : baseEnd_316306 < baseStart_316306 := by decide
  rcases family_descends (prefixWord ++ tailWord_316306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316327 : List Nat := [1, 1, 6, 1, 4, 1, 5]
def baseStart_316327 : Nat := 118140960795 + 316327 * 2 ^ 59
def prefixEnd_316327 : Nat := 4983230072969 + 3 ^ 40 * 316327 * 2
def baseEnd_316327 : Nat := 32084502715039822786715

theorem tailTrace_316327 : CollatzResearch.WordTrace tailWord_316327 prefixEnd_316327 32084502715039822786715 := by
  unfold tailWord_316327
  simp only [CollatzResearch.WordTrace]
  refine ⟨11537393525008778195611235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7691595683339185463740823 11537393525008778195611235)
  ·
    refine ⟨17306090287513167293416853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11537393525008778195611235 17306090287513167293416853)
    ·
      refine ⟨811222982227179716878915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17306090287513167293416853 811222982227179716878915)
      ·
        refine ⟨1216834473340769575318373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811222982227179716878915 1216834473340769575318373)
        ·
          refine ⟨228156463751394295372195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1216834473340769575318373 228156463751394295372195)
          ·
            refine ⟨342234695627091443058293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228156463751394295372195 342234695627091443058293)
            ·
              refine ⟨32084502715039822786715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 342234695627091443058293 32084502715039822786715)
              ·
                rfl

theorem cell19_316327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 5].length) (baseStart_316327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316327 prefixEnd_316327 := by exact prefixLift 316327
  have htrace : WordTrace (prefixWord ++ tailWord_316327) baseStart_316327 baseEnd_316327 := by
    simpa [prefixWord, tailWord_316327, baseEnd_316327] using wordTrace_append hprefix tailTrace_316327
  have hstable : (prefixWord ++ tailWord_316327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316327).length < 2 ^ (prefixWord ++ tailWord_316327).sum := by decide
  have hdescent : baseEnd_316327 < baseStart_316327 := by decide
  rcases family_descends (prefixWord ++ tailWord_316327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316342 : List Nat := [5, 1, 4, 1, 1, 1, 2, 4]
def baseStart_316342 : Nat := 118140960795 + 316342 * 2 ^ 59
def prefixEnd_316342 : Nat := 4983230072969 + 3 ^ 40 * 316342 * 2
def baseEnd_316342 : Nat := 96258072417603878026771

theorem tailTrace_316342 : CollatzResearch.WordTrace tailWord_316342 prefixEnd_316342 96258072417603878026771 := by
  unfold tailWord_316342
  simp only [CollatzResearch.WordTrace]
  refine ⟨721121288747152234837955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7691960413302957171604853 721121288747152234837955)
  ·
    refine ⟨1081681933120728352256933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721121288747152234837955 1081681933120728352256933)
    ·
      refine ⟨202815362460136566048175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1081681933120728352256933 202815362460136566048175)
      ·
        refine ⟨304223043690204849072263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202815362460136566048175 304223043690204849072263)
        ·
          refine ⟨456334565535307273608395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 304223043690204849072263 456334565535307273608395)
          ·
            refine ⟨684501848302960910412593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456334565535307273608395 684501848302960910412593)
            ·
              refine ⟨513376386227220682809445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684501848302960910412593 513376386227220682809445)
              ·
                refine ⟨96258072417603878026771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513376386227220682809445 96258072417603878026771)
                ·
                  rfl

theorem cell19_316342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_316342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316342 prefixEnd_316342 := by exact prefixLift 316342
  have htrace : WordTrace (prefixWord ++ tailWord_316342) baseStart_316342 baseEnd_316342 := by
    simpa [prefixWord, tailWord_316342, baseEnd_316342] using wordTrace_append hprefix tailTrace_316342
  have hstable : (prefixWord ++ tailWord_316342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316342).length < 2 ^ (prefixWord ++ tailWord_316342).sum := by decide
  have hdescent : baseEnd_316342 < baseStart_316342 := by decide
  rcases family_descends (prefixWord ++ tailWord_316342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316386 : List Nat := [3, 3, 3, 1, 1, 8]
def baseStart_316386 : Nat := 118140960795 + 316386 * 2 ^ 59
def prefixEnd_316386 : Nat := 4983230072969 + 3 ^ 40 * 316386 * 2
def baseEnd_316386 : Nat := 10696828994469423672097

theorem tailTrace_316386 : CollatzResearch.WordTrace tailWord_316386 prefixEnd_316386 10696828994469423672097 := by
  unfold tailWord_316386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2884886357948757818002253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7693030287863354181339341 2884886357948757818002253)
  ·
    refine ⟨1081832384230784181750845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2884886357948757818002253 1081832384230784181750845)
    ·
      refine ⟨405687144086544068156567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1081832384230784181750845 405687144086544068156567)
      ·
        refine ⟨608530716129816102234851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405687144086544068156567 608530716129816102234851)
        ·
          refine ⟨912796074194724153352277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608530716129816102234851 912796074194724153352277)
          ·
            refine ⟨10696828994469423672097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 912796074194724153352277 10696828994469423672097)
            ·
              rfl

theorem cell19_316386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 8].length) (baseStart_316386 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316386 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316386 prefixEnd_316386 := by exact prefixLift 316386
  have htrace : WordTrace (prefixWord ++ tailWord_316386) baseStart_316386 baseEnd_316386 := by
    simpa [prefixWord, tailWord_316386, baseEnd_316386] using wordTrace_append hprefix tailTrace_316386
  have hstable : (prefixWord ++ tailWord_316386).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316386).length < 2 ^ (prefixWord ++ tailWord_316386).sum := by decide
  have hdescent : baseEnd_316386 < baseStart_316386 := by decide
  rcases family_descends (prefixWord ++ tailWord_316386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316424 : List Nat := [2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_316424 : Nat := 118140960795 + 316424 * 2 ^ 59
def prefixEnd_316424 : Nat := 4983230072969 + 3 ^ 40 * 316424 * 2
def baseEnd_316424 : Nat := 96283023773851984204325

theorem tailTrace_316424 : CollatzResearch.WordTrace tailWord_316424 prefixEnd_316424 96283023773851984204325 := by
  unfold tailWord_316424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5770465702828681880946163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7693954270438242507928217 5770465702828681880946163)
  ·
    refine ⟨8655698554243022821419245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5770465702828681880946163 8655698554243022821419245)
    ·
      refine ⟨3245886957841133558032217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8655698554243022821419245 3245886957841133558032217)
      ·
        refine ⟨2434415218380850168524163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3245886957841133558032217 2434415218380850168524163)
        ·
          refine ⟨3651622827571275252786245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2434415218380850168524163 3651622827571275252786245)
          ·
            refine ⟨684679280169614109897421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3651622827571275252786245 684679280169614109897421)
            ·
              refine ⟨256754730063605291211533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 684679280169614109897421 256754730063605291211533)
              ·
                refine ⟨96283023773851984204325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256754730063605291211533 96283023773851984204325)
                ·
                  rfl

theorem cell19_316424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_316424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316424 prefixEnd_316424 := by exact prefixLift 316424
  have htrace : WordTrace (prefixWord ++ tailWord_316424) baseStart_316424 baseEnd_316424 := by
    simpa [prefixWord, tailWord_316424, baseEnd_316424] using wordTrace_append hprefix tailTrace_316424
  have hstable : (prefixWord ++ tailWord_316424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316424).length < 2 ^ (prefixWord ++ tailWord_316424).sum := by decide
  have hdescent : baseEnd_316424 < baseStart_316424 := by decide
  rcases family_descends (prefixWord ++ tailWord_316424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316481 : List Nat := [1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_316481 : Nat := 118140960795 + 316481 * 2 ^ 59
def prefixEnd_316481 : Nat := 4983230072969 + 3 ^ 40 * 316481 * 2
def baseEnd_316481 : Nat := 96300368009292740937503

theorem tailTrace_316481 : CollatzResearch.WordTrace tailWord_316481 prefixEnd_316481 96300368009292740937503 := by
  unfold tailWord_316481
  simp only [CollatzResearch.WordTrace]
  refine ⟨11543010366450862496717297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7695340244300574997811531 11543010366450862496717297)
  ·
    refine ⟨8657257774838146872537973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11543010366450862496717297 8657257774838146872537973)
    ·
      refine ⟨811617916391076269300435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8657257774838146872537973 811617916391076269300435)
      ·
        refine ⟨1217426874586614403950653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811617916391076269300435 1217426874586614403950653)
        ·
          refine ⟨456535077969980401481495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1217426874586614403950653 456535077969980401481495)
          ·
            refine ⟨684802616954970602222243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456535077969980401481495 684802616954970602222243)
            ·
              refine ⟨1027203925432455903333365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 684802616954970602222243 1027203925432455903333365)
              ·
                refine ⟨96300368009292740937503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1027203925432455903333365 96300368009292740937503)
                ·
                  rfl

theorem cell19_316481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_316481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316481 prefixEnd_316481 := by exact prefixLift 316481
  have htrace : WordTrace (prefixWord ++ tailWord_316481) baseStart_316481 baseEnd_316481 := by
    simpa [prefixWord, tailWord_316481, baseEnd_316481] using wordTrace_append hprefix tailTrace_316481
  have hstable : (prefixWord ++ tailWord_316481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316481).length < 2 ^ (prefixWord ++ tailWord_316481).sum := by decide
  have hdescent : baseEnd_316481 < baseStart_316481 := by decide
  rcases family_descends (prefixWord ++ tailWord_316481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316521 : List Nat := [1, 2, 1, 1, 1, 7, 2, 4]
def baseStart_316521 : Nat := 118140960795 + 316521 * 2 ^ 59
def prefixEnd_316521 : Nat := 4983230072969 + 3 ^ 40 * 316521 * 2
def baseEnd_316521 : Nat := 96312539402584500048505

theorem tailTrace_316521 : CollatzResearch.WordTrace tailWord_316521 prefixEnd_316521 96312539402584500048505 := by
  unfold tailWord_316521
  simp only [CollatzResearch.WordTrace]
  refine ⟨11544469286305949328173417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7696312857537299552115611 11544469286305949328173417)
  ·
    refine ⟨8658351964729461996130063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11544469286305949328173417 8658351964729461996130063)
    ·
      refine ⟨12987527947094192994195095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8658351964729461996130063 12987527947094192994195095)
      ·
        refine ⟨19481291920641289491292643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12987527947094192994195095 19481291920641289491292643)
        ·
          refine ⟨29221937880961934236938965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19481291920641289491292643 29221937880961934236938965)
          ·
            refine ⟨684889169085045333678257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29221937880961934236938965 684889169085045333678257)
            ·
              refine ⟨513666876813784000258693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684889169085045333678257 513666876813784000258693)
              ·
                refine ⟨96312539402584500048505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513666876813784000258693 96312539402584500048505)
                ·
                  rfl

theorem cell19_316521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_316521 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316521 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316521 prefixEnd_316521 := by exact prefixLift 316521
  have htrace : WordTrace (prefixWord ++ tailWord_316521) baseStart_316521 baseEnd_316521 := by
    simpa [prefixWord, tailWord_316521, baseEnd_316521] using wordTrace_append hprefix tailTrace_316521
  have hstable : (prefixWord ++ tailWord_316521).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316521).length < 2 ^ (prefixWord ++ tailWord_316521).sum := by decide
  have hdescent : baseEnd_316521 < baseStart_316521 := by decide
  rcases family_descends (prefixWord ++ tailWord_316521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316574 : List Nat := [4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_316574 : Nat := 118140960795 + 316574 * 2 ^ 59
def prefixEnd_316574 : Nat := 4983230072969 + 3 ^ 40 * 316574 * 2
def baseEnd_316574 : Nat := 96328666498696080870583

theorem tailTrace_316574 : CollatzResearch.WordTrace tailWord_316574 prefixEnd_316574 96328666498696080870583 := by
  unfold tailWord_316574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1443300294389242422481597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7697601570075959586568517 1443300294389242422481597)
  ·
    refine ⟨541237610395965908430599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1443300294389242422481597 541237610395965908430599)
    ·
      refine ⟨811856415593948862645899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541237610395965908430599 811856415593948862645899)
      ·
        refine ⟨1217784623390923293968849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 811856415593948862645899 1217784623390923293968849)
        ·
          refine ⟨913338467543192470476637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1217784623390923293968849 913338467543192470476637)
          ·
            refine ⟨342501925328697176428739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 913338467543192470476637 342501925328697176428739)
            ·
              refine ⟨513752887993045764643109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342501925328697176428739 513752887993045764643109)
              ·
                refine ⟨96328666498696080870583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513752887993045764643109 96328666498696080870583)
                ·
                  rfl

theorem cell19_316574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_316574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316574 prefixEnd_316574 := by exact prefixLift 316574
  have htrace : WordTrace (prefixWord ++ tailWord_316574) baseStart_316574 baseEnd_316574 := by
    simpa [prefixWord, tailWord_316574, baseEnd_316574] using wordTrace_append hprefix tailTrace_316574
  have hstable : (prefixWord ++ tailWord_316574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316574).length < 2 ^ (prefixWord ++ tailWord_316574).sum := by decide
  have hdescent : baseEnd_316574 < baseStart_316574 := by decide
  rcases family_descends (prefixWord ++ tailWord_316574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316652 : List Nat := [2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_316652 : Nat := 118140960795 + 316652 * 2 ^ 59
def prefixEnd_316652 : Nat := 4983230072969 + 3 ^ 40 * 316652 * 2
def baseEnd_316652 : Nat := 96352400715615011137037

theorem tailTrace_316652 : CollatzResearch.WordTrace tailWord_316652 prefixEnd_316652 96352400715615011137037 := by
  unfold tailWord_316652
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774623624415679350596105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7699498165887572467461473 5774623624415679350596105)
  ·
    refine ⟨4330967718311759512947079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5774623624415679350596105 4330967718311759512947079)
    ·
      refine ⟨6496451577467639269420619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4330967718311759512947079 6496451577467639269420619)
      ·
        refine ⟨9744677366201458904130929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6496451577467639269420619 9744677366201458904130929)
        ·
          refine ⟨7308508024651094178098197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9744677366201458904130929 7308508024651094178098197)
          ·
            refine ⟨342586313655520039598353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7308508024651094178098197 342586313655520039598353)
            ·
              refine ⟨256939735241640029698765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342586313655520039598353 256939735241640029698765)
              ·
                refine ⟨96352400715615011137037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256939735241640029698765 96352400715615011137037)
                ·
                  rfl

theorem cell19_316652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_316652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316652 prefixEnd_316652 := by exact prefixLift 316652
  have htrace : WordTrace (prefixWord ++ tailWord_316652) baseStart_316652 baseEnd_316652 := by
    simpa [prefixWord, tailWord_316652, baseEnd_316652] using wordTrace_append hprefix tailTrace_316652
  have hstable : (prefixWord ++ tailWord_316652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316652).length < 2 ^ (prefixWord ++ tailWord_316652).sum := by decide
  have hdescent : baseEnd_316652 < baseStart_316652 := by decide
  rcases family_descends (prefixWord ++ tailWord_316652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316673 : List Nat := [1, 2, 4, 1, 1, 5, 5]
def baseStart_316673 : Nat := 118140960795 + 316673 * 2 ^ 59
def prefixEnd_316673 : Nat := 4983230072969 + 3 ^ 40 * 316673 * 2
def baseEnd_316673 : Nat := 32119596899031061556771

theorem tailTrace_316673 : CollatzResearch.WordTrace tailWord_316673 prefixEnd_316673 32119596899031061556771 := by
  unfold tailWord_316673
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550013181755279287706673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7700008787836852858471115 11550013181755279287706673)
  ·
    refine ⟨8662509886316459465780005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11550013181755279287706673 8662509886316459465780005)
    ·
      refine ⟨1624220603684336149833751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8662509886316459465780005 1624220603684336149833751)
      ·
        refine ⟨2436330905526504224750627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1624220603684336149833751 2436330905526504224750627)
        ·
          refine ⟨3654496358289756337125941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436330905526504224750627 3654496358289756337125941)
          ·
            refine ⟨342609033589664656605557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3654496358289756337125941 342609033589664656605557)
            ·
              refine ⟨32119596899031061556771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 342609033589664656605557 32119596899031061556771)
              ·
                rfl

theorem cell19_316673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_316673 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316673 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316673 prefixEnd_316673 := by exact prefixLift 316673
  have htrace : WordTrace (prefixWord ++ tailWord_316673) baseStart_316673 baseEnd_316673 := by
    simpa [prefixWord, tailWord_316673, baseEnd_316673] using wordTrace_append hprefix tailTrace_316673
  have hstable : (prefixWord ++ tailWord_316673).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316673).length < 2 ^ (prefixWord ++ tailWord_316673).sum := by decide
  have hdescent : baseEnd_316673 < baseStart_316673 := by decide
  rcases family_descends (prefixWord ++ tailWord_316673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316675 : List Nat := [1, 1, 1, 3, 2, 4, 7]
def baseStart_316675 : Nat := 118140960795 + 316675 * 2 ^ 59
def prefixEnd_316675 : Nat := 4983230072969 + 3 ^ 40 * 316675 * 2
def baseEnd_316675 : Nat := 32119799755585924208621

theorem tailTrace_316675 : CollatzResearch.WordTrace tailWord_316675 prefixEnd_316675 32119799755585924208621 := by
  unfold tailWord_316675
  simp only [CollatzResearch.WordTrace]
  refine ⟨11550086127748033629279479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7700057418498689086186319 11550086127748033629279479)
  ·
    refine ⟨17325129191622050443919219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11550086127748033629279479 17325129191622050443919219)
    ·
      refine ⟨25987693787433075665878829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17325129191622050443919219 25987693787433075665878829)
      ·
        refine ⟨9745385170287403374704561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25987693787433075665878829 9745385170287403374704561)
        ·
          refine ⟨7309038877715552531028421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9745385170287403374704561 7309038877715552531028421)
          ·
            refine ⟨1370444789571666099567829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7309038877715552531028421 1370444789571666099567829)
            ·
              refine ⟨32119799755585924208621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1370444789571666099567829 32119799755585924208621)
              ·
                rfl

theorem cell19_316675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_316675 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316675 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316675 prefixEnd_316675 := by exact prefixLift 316675
  have htrace : WordTrace (prefixWord ++ tailWord_316675) baseStart_316675 baseEnd_316675 := by
    simpa [prefixWord, tailWord_316675, baseEnd_316675] using wordTrace_append hprefix tailTrace_316675
  have hstable : (prefixWord ++ tailWord_316675).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316675).length < 2 ^ (prefixWord ++ tailWord_316675).sum := by decide
  have hdescent : baseEnd_316675 < baseStart_316675 := by decide
  rcases family_descends (prefixWord ++ tailWord_316675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316726 : List Nat := [5, 1, 2, 3, 2, 6]
def baseStart_316726 : Nat := 118140960795 + 316726 * 2 ^ 59
def prefixEnd_316726 : Nat := 4983230072969 + 3 ^ 40 * 316726 * 2
def baseEnd_316726 : Nat := 10708324199244973943599

theorem tailTrace_316726 : CollatzResearch.WordTrace tailWord_316726 prefixEnd_316726 10708324199244973943599 := by
  unfold tailWord_316726
  simp only [CollatzResearch.WordTrace]
  refine ⟨721996640660204333711627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7701297500375512892924021 721996640660204333711627)
  ·
    refine ⟨1082994960990306500567441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 721996640660204333711627 1082994960990306500567441)
    ·
      refine ⟨812246220742729875425581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1082994960990306500567441 812246220742729875425581)
      ·
        refine ⟨304592332778523703284593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 812246220742729875425581 304592332778523703284593)
        ·
          refine ⟨228444249583892777463445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304592332778523703284593 228444249583892777463445)
          ·
            refine ⟨10708324199244973943599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 228444249583892777463445 10708324199244973943599)
            ·
              rfl

theorem cell19_316726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 6].length) (baseStart_316726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316726 prefixEnd_316726 := by exact prefixLift 316726
  have htrace : WordTrace (prefixWord ++ tailWord_316726) baseStart_316726 baseEnd_316726 := by
    simpa [prefixWord, tailWord_316726, baseEnd_316726] using wordTrace_append hprefix tailTrace_316726
  have hstable : (prefixWord ++ tailWord_316726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316726).length < 2 ^ (prefixWord ++ tailWord_316726).sum := by decide
  have hdescent : baseEnd_316726 < baseStart_316726 := by decide
  rcases family_descends (prefixWord ++ tailWord_316726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316732 : List Nat := [2, 2, 2, 2, 1, 10]
def baseStart_316732 : Nat := 118140960795 + 316732 * 2 ^ 59
def prefixEnd_316732 : Nat := 4983230072969 + 3 ^ 40 * 316732 * 2
def baseEnd_316732 : Nat := 10708527055799836595449

theorem tailTrace_316732 : CollatzResearch.WordTrace tailWord_316732 prefixEnd_316732 10708527055799836595449 := by
  unfold tailWord_316732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5776082544270766182052225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7701443392361021576069633 5776082544270766182052225)
  ·
    refine ⟨4332061908203074636539169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5776082544270766182052225 4332061908203074636539169)
    ·
      refine ⟨3249046431152305977404377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4332061908203074636539169 3249046431152305977404377)
      ·
        refine ⟨2436784823364229483053283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3249046431152305977404377 2436784823364229483053283)
        ·
          refine ⟨3655177235046344224579925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2436784823364229483053283 3655177235046344224579925)
          ·
            refine ⟨10708527055799836595449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3655177235046344224579925 10708527055799836595449)
            ·
              rfl

theorem cell19_316732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 10].length) (baseStart_316732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316732 prefixEnd_316732 := by exact prefixLift 316732
  have htrace : WordTrace (prefixWord ++ tailWord_316732) baseStart_316732 baseEnd_316732 := by
    simpa [prefixWord, tailWord_316732, baseEnd_316732] using wordTrace_append hprefix tailTrace_316732
  have hstable : (prefixWord ++ tailWord_316732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316732).length < 2 ^ (prefixWord ++ tailWord_316732).sum := by decide
  have hdescent : baseEnd_316732 < baseStart_316732 := by decide
  rcases family_descends (prefixWord ++ tailWord_316732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316825 : List Nat := [1, 2, 1, 2, 1, 5, 4, 3]
def baseStart_316825 : Nat := 118140960795 + 316825 * 2 ^ 59
def prefixEnd_316825 : Nat := 4983230072969 + 3 ^ 40 * 316825 * 2
def baseEnd_316825 : Nat := 96405041991601869292121

theorem tailTrace_316825 : CollatzResearch.WordTrace tailWord_316825 prefixEnd_316825 96405041991601869292121 := by
  unfold tailWord_316825
  simp only [CollatzResearch.WordTrace]
  refine ⟨11555557077204609247239929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7703704718136406164826619 11555557077204609247239929)
  ·
    refine ⟨8666667807903456935429947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11555557077204609247239929 8666667807903456935429947)
    ·
      refine ⟨13000001711855185403144921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8666667807903456935429947 13000001711855185403144921)
      ·
        refine ⟨9750001283891389052358691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13000001711855185403144921 9750001283891389052358691)
        ·
          refine ⟨14625001925837083578538037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9750001283891389052358691 14625001925837083578538037)
          ·
            refine ⟨1371093930547226585487941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14625001925837083578538037 1371093930547226585487941)
            ·
              refine ⟨257080111977604984778989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1371093930547226585487941 257080111977604984778989)
              ·
                refine ⟨96405041991601869292121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257080111977604984778989 96405041991601869292121)
                ·
                  rfl

theorem cell19_316825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 3].length) (baseStart_316825 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316825 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316825 prefixEnd_316825 := by exact prefixLift 316825
  have htrace : WordTrace (prefixWord ++ tailWord_316825) baseStart_316825 baseEnd_316825 := by
    simpa [prefixWord, tailWord_316825, baseEnd_316825] using wordTrace_append hprefix tailTrace_316825
  have hstable : (prefixWord ++ tailWord_316825).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316825).length < 2 ^ (prefixWord ++ tailWord_316825).sum := by decide
  have hdescent : baseEnd_316825 < baseStart_316825 := by decide
  rcases family_descends (prefixWord ++ tailWord_316825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316840 : List Nat := [2, 1, 6, 1, 3, 1, 5]
def baseStart_316840 : Nat := 118140960795 + 316840 * 2 ^ 59
def prefixEnd_316840 : Nat := 4983230072969 + 3 ^ 40 * 316840 * 2
def baseEnd_316840 : Nat := 32136535421362092986249

theorem tailTrace_316840 : CollatzResearch.WordTrace tailWord_316840 prefixEnd_316840 32136535421362092986249 := by
  unfold tailWord_316840
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778052086075133404517987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7704069448100177872690649 5778052086075133404517987)
  ·
    refine ⟨8667078129112700106776981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5778052086075133404517987 8667078129112700106776981)
    ·
      refine ⟨406269287302157817505171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8667078129112700106776981 406269287302157817505171)
      ·
        refine ⟨609403930953236726257757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406269287302157817505171 609403930953236726257757)
        ·
          refine ⟨228526474107463772346659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 609403930953236726257757 228526474107463772346659)
          ·
            refine ⟨342789711161195658519989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228526474107463772346659 342789711161195658519989)
            ·
              refine ⟨32136535421362092986249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 342789711161195658519989 32136535421362092986249)
              ·
                rfl

theorem cell19_316840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 5].length) (baseStart_316840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316840 prefixEnd_316840 := by exact prefixLift 316840
  have htrace : WordTrace (prefixWord ++ tailWord_316840) baseStart_316840 baseEnd_316840 := by
    simpa [prefixWord, tailWord_316840, baseEnd_316840] using wordTrace_append hprefix tailTrace_316840
  have hstable : (prefixWord ++ tailWord_316840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316840).length < 2 ^ (prefixWord ++ tailWord_316840).sum := by decide
  have hdescent : baseEnd_316840 < baseStart_316840 := by decide
  rcases family_descends (prefixWord ++ tailWord_316840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316903 : List Nat := [1, 1, 5, 2, 1, 9]
def baseStart_316903 : Nat := 118140960795 + 316903 * 2 ^ 59
def prefixEnd_316903 : Nat := 4983230072969 + 3 ^ 40 * 316903 * 2
def baseEnd_316903 : Nat := 10714308467613422173175

theorem tailTrace_316903 : CollatzResearch.WordTrace tailWord_316903 prefixEnd_316903 10714308467613422173175 := by
  unfold tailWord_316903
  simp only [CollatzResearch.WordTrace]
  refine ⟨11558401970922028568579363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7705601313948019045719575 11558401970922028568579363)
  ·
    refine ⟨17337602956383042852869045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11558401970922028568579363 17337602956383042852869045)
    ·
      refine ⟨1625400277160910267456473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17337602956383042852869045 1625400277160910267456473)
      ·
        refine ⟨1219050207870682700592355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625400277160910267456473 1219050207870682700592355)
        ·
          refine ⟨1828575311806024050888533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219050207870682700592355 1828575311806024050888533)
          ·
            refine ⟨10714308467613422173175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1828575311806024050888533 10714308467613422173175)
            ·
              rfl

theorem cell19_316903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_316903 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316903 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316903 prefixEnd_316903 := by exact prefixLift 316903
  have htrace : WordTrace (prefixWord ++ tailWord_316903) baseStart_316903 baseEnd_316903 := by
    simpa [prefixWord, tailWord_316903, baseEnd_316903] using wordTrace_append hprefix tailTrace_316903
  have hstable : (prefixWord ++ tailWord_316903).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316903).length < 2 ^ (prefixWord ++ tailWord_316903).sum := by decide
  have hdescent : baseEnd_316903 < baseStart_316903 := by decide
  rcases family_descends (prefixWord ++ tailWord_316903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316918 : List Nat := [5, 1, 1, 1, 2, 4, 1, 4]
def baseStart_316918 : Nat := 118140960795 + 316918 * 2 ^ 59
def prefixEnd_316918 : Nat := 4983230072969 + 3 ^ 40 * 316918 * 2
def baseEnd_316918 : Nat := 96433340481005209225201

theorem tailTrace_316918 : CollatzResearch.WordTrace tailWord_316918 prefixEnd_316918 96433340481005209225201 := by
  unfold tailWord_316918
  simp only [CollatzResearch.WordTrace]
  refine ⟨722434316616730383148463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7705966043911790753583605 722434316616730383148463)
  ·
    refine ⟨1083651474925095574722695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722434316616730383148463 1083651474925095574722695)
    ·
      refine ⟨1625477212387643362084043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1083651474925095574722695 1625477212387643362084043)
      ·
        refine ⟨2438215818581465043126065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1625477212387643362084043 2438215818581465043126065)
        ·
          refine ⟨1828661863936098782344549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2438215818581465043126065 1828661863936098782344549)
          ·
            refine ⟨342874099488018521689603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1828661863936098782344549 342874099488018521689603)
            ·
              refine ⟨514311149232027782534405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342874099488018521689603 514311149232027782534405)
              ·
                refine ⟨96433340481005209225201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514311149232027782534405 96433340481005209225201)
                ·
                  rfl

theorem cell19_316918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_316918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316918 prefixEnd_316918 := by exact prefixLift 316918
  have htrace : WordTrace (prefixWord ++ tailWord_316918) baseStart_316918 baseEnd_316918 := by
    simpa [prefixWord, tailWord_316918, baseEnd_316918] using wordTrace_append hprefix tailTrace_316918
  have hstable : (prefixWord ++ tailWord_316918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316918).length < 2 ^ (prefixWord ++ tailWord_316918).sum := by decide
  have hdescent : baseEnd_316918 < baseStart_316918 := by decide
  rcases family_descends (prefixWord ++ tailWord_316918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_316920 : List Nat := [2, 1, 2, 1, 1, 7, 1, 4]
def baseStart_316920 : Nat := 118140960795 + 316920 * 2 ^ 59
def prefixEnd_316920 : Nat := 4983230072969 + 3 ^ 40 * 316920 * 2
def baseEnd_316920 : Nat := 96433949050669797180751

theorem tailTrace_316920 : CollatzResearch.WordTrace tailWord_316920 prefixEnd_316920 96433949050669797180751 := by
  unfold tailWord_316920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5779511005930220235974107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7706014674573626981298809 5779511005930220235974107)
  ·
    refine ⟨8669266508895330353961161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5779511005930220235974107 8669266508895330353961161)
    ·
      refine ⟨6501949881671497765470871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8669266508895330353961161 6501949881671497765470871)
      ·
        refine ⟨9752924822507246648206307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6501949881671497765470871 9752924822507246648206307)
        ·
          refine ⟨14629387233760869972309461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9752924822507246648206307 14629387233760869972309461)
          ·
            refine ⟨342876263291270389976003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14629387233760869972309461 342876263291270389976003)
            ·
              refine ⟨514314394936905584964005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342876263291270389976003 514314394936905584964005)
              ·
                refine ⟨96433949050669797180751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514314394936905584964005 96433949050669797180751)
                ·
                  rfl

theorem cell19_316920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_316920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_316920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_316920 prefixEnd_316920 := by exact prefixLift 316920
  have htrace : WordTrace (prefixWord ++ tailWord_316920) baseStart_316920 baseEnd_316920 := by
    simpa [prefixWord, tailWord_316920, baseEnd_316920] using wordTrace_append hprefix tailTrace_316920
  have hstable : (prefixWord ++ tailWord_316920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_316920).length < 2 ^ (prefixWord ++ tailWord_316920).sum := by decide
  have hdescent : baseEnd_316920 < baseStart_316920 := by decide
  rcases family_descends (prefixWord ++ tailWord_316920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317034 : List Nat := [3, 1, 3, 2, 1, 3, 2, 4]
def baseStart_317034 : Nat := 118140960795 + 317034 * 2 ^ 59
def prefixEnd_317034 : Nat := 4983230072969 + 3 ^ 40 * 317034 * 2
def baseEnd_317034 : Nat := 96468637521551310647107

theorem tailTrace_317034 : CollatzResearch.WordTrace tailWord_317034 prefixEnd_317034 96468637521551310647107 := by
  unfold tailWord_317034
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890794983361859485399539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7708786622298291961065437 2890794983361859485399539)
  ·
    refine ⟨4336192475042789228099309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2890794983361859485399539 4336192475042789228099309)
    ·
      refine ⟨1626072178141045960537241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4336192475042789228099309 1626072178141045960537241)
      ·
        refine ⟨1219554133605784470402931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626072178141045960537241 1219554133605784470402931)
        ·
          refine ⟨1829331200408676705604397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219554133605784470402931 1829331200408676705604397)
          ·
            refine ⟨685999200153253764601649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1829331200408676705604397 685999200153253764601649)
            ·
              refine ⟨514499400114940323451237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 685999200153253764601649 514499400114940323451237)
              ·
                refine ⟨96468637521551310647107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514499400114940323451237 96468637521551310647107)
                ·
                  rfl

theorem cell19_317034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_317034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317034 prefixEnd_317034 := by exact prefixLift 317034
  have htrace : WordTrace (prefixWord ++ tailWord_317034) baseStart_317034 baseEnd_317034 := by
    simpa [prefixWord, tailWord_317034, baseEnd_317034] using wordTrace_append hprefix tailTrace_317034
  have hstable : (prefixWord ++ tailWord_317034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317034).length < 2 ^ (prefixWord ++ tailWord_317034).sum := by decide
  have hdescent : baseEnd_317034 < baseStart_317034 := by decide
  rcases family_descends (prefixWord ++ tailWord_317034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317074 : List Nat := [3, 2, 3, 1, 10]
def baseStart_317074 : Nat := 118140960795 + 317074 * 2 ^ 59
def prefixEnd_317074 : Nat := 4983230072969 + 3 ^ 40 * 317074 * 2
def baseEnd_317074 : Nat := 3573363293142335916967

theorem tailTrace_317074 : CollatzResearch.WordTrace tailWord_317074 prefixEnd_317074 3573363293142335916967 := by
  unfold tailWord_317074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891159713325631193263569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7709759235535016515369517 2891159713325631193263569)
  ·
    refine ⟨2168369784994223394947677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2891159713325631193263569 2168369784994223394947677)
    ·
      refine ⟨813138669372833773105379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2168369784994223394947677 813138669372833773105379)
      ·
        refine ⟨1219708004059250659658069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 813138669372833773105379 1219708004059250659658069)
        ·
          refine ⟨3573363293142335916967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1219708004059250659658069 3573363293142335916967)
          ·
            rfl

theorem cell19_317074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 10].length) (baseStart_317074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317074 prefixEnd_317074 := by exact prefixLift 317074
  have htrace : WordTrace (prefixWord ++ tailWord_317074) baseStart_317074 baseEnd_317074 := by
    simpa [prefixWord, tailWord_317074, baseEnd_317074] using wordTrace_append hprefix tailTrace_317074
  have hstable : (prefixWord ++ tailWord_317074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317074).length < 2 ^ (prefixWord ++ tailWord_317074).sum := by decide
  have hdescent : baseEnd_317074 < baseStart_317074 := by decide
  rcases family_descends (prefixWord ++ tailWord_317074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317087 : List Nat := [1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_317087 : Nat := 118140960795 + 317087 * 2 ^ 59
def prefixEnd_317087 : Nat := 4983230072969 + 3 ^ 40 * 317087 * 2
def baseEnd_317087 : Nat := 96484764617662891469185

theorem tailTrace_317087 : CollatzResearch.WordTrace tailWord_317087 prefixEnd_317087 96484764617662891469185 := by
  unfold tailWord_317087
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565113002255427993277515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7710075334836951995518343 11565113002255427993277515)
  ·
    refine ⟨17347669503383141989916273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11565113002255427993277515 17347669503383141989916273)
    ·
      refine ⟨13010752127537356492437205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17347669503383141989916273 13010752127537356492437205)
      ·
        refine ⟨304939502989156792791497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 13010752127537356492437205 304939502989156792791497)
        ·
          refine ⟨228704627241867594593623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304939502989156792791497 228704627241867594593623)
          ·
            refine ⟨343056940862801391890435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228704627241867594593623 343056940862801391890435)
            ·
              refine ⟨514585411294202087835653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343056940862801391890435 514585411294202087835653)
              ·
                refine ⟨96484764617662891469185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514585411294202087835653 96484764617662891469185)
                ·
                  rfl

theorem cell19_317087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_317087 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317087 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317087 prefixEnd_317087 := by exact prefixLift 317087
  have htrace : WordTrace (prefixWord ++ tailWord_317087) baseStart_317087 baseEnd_317087 := by
    simpa [prefixWord, tailWord_317087, baseEnd_317087] using wordTrace_append hprefix tailTrace_317087
  have hstable : (prefixWord ++ tailWord_317087).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317087).length < 2 ^ (prefixWord ++ tailWord_317087).sum := by decide
  have hdescent : baseEnd_317087 < baseStart_317087 := by decide
  rcases family_descends (prefixWord ++ tailWord_317087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317093 : List Nat := [1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_317093 : Nat := 118140960795 + 317093 * 2 ^ 59
def prefixEnd_317093 : Nat := 4983230072969 + 3 ^ 40 * 317093 * 2
def baseEnd_317093 : Nat := 96486590326656655335835

theorem tailTrace_317093 : CollatzResearch.WordTrace tailWord_317093 prefixEnd_317093 96486590326656655335835 := by
  unfold tailWord_317093
  simp only [CollatzResearch.WordTrace]
  refine ⟨11565331840233691017995933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7710221226822460678663955 11565331840233691017995933)
  ·
    refine ⟨4336999440087634131748475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11565331840233691017995933 4336999440087634131748475)
    ·
      refine ⟨6505499160131451197622713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336999440087634131748475 6505499160131451197622713)
      ·
        refine ⟨4879124370098588398217035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6505499160131451197622713 4879124370098588398217035)
        ·
          refine ⟨7318686555147882597325553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4879124370098588398217035 7318686555147882597325553)
          ·
            refine ⟨5489014916360911947994165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7318686555147882597325553 5489014916360911947994165)
            ·
              refine ⟨514595148408835495124453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5489014916360911947994165 514595148408835495124453)
              ·
                refine ⟨96486590326656655335835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514595148408835495124453 96486590326656655335835)
                ·
                  rfl

theorem cell19_317093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_317093 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317093 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317093 prefixEnd_317093 := by exact prefixLift 317093
  have htrace : WordTrace (prefixWord ++ tailWord_317093) baseStart_317093 baseEnd_317093 := by
    simpa [prefixWord, tailWord_317093, baseEnd_317093] using wordTrace_append hprefix tailTrace_317093
  have hstable : (prefixWord ++ tailWord_317093).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317093).length < 2 ^ (prefixWord ++ tailWord_317093).sum := by decide
  have hdescent : baseEnd_317093 < baseStart_317093 := by decide
  rcases family_descends (prefixWord ++ tailWord_317093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317165 : List Nat := [1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_317165 : Nat := 118140960795 + 317165 * 2 ^ 59
def prefixEnd_317165 : Nat := 4983230072969 + 3 ^ 40 * 317165 * 2
def baseEnd_317165 : Nat := 96508498834581821735639

theorem tailTrace_317165 : CollatzResearch.WordTrace tailWord_317165 prefixEnd_317165 96508498834581821735639 := by
  unfold tailWord_317165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11567957895972847314616949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7711971930648564876411299 11567957895972847314616949)
  ·
    refine ⟨1084496052747454435745339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11567957895972847314616949 1084496052747454435745339)
    ·
      refine ⟨1626744079121181653618009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084496052747454435745339 1626744079121181653618009)
      ·
        refine ⟨1220058059340886240213507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626744079121181653618009 1220058059340886240213507)
        ·
          refine ⟨1830087089011329360320261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220058059340886240213507 1830087089011329360320261)
          ·
            refine ⟨343141329189624255060049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1830087089011329360320261 343141329189624255060049)
            ·
              refine ⟨257355996892218191295037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343141329189624255060049 257355996892218191295037)
              ·
                refine ⟨96508498834581821735639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257355996892218191295037 96508498834581821735639)
                ·
                  rfl

theorem cell19_317165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_317165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317165 prefixEnd_317165 := by exact prefixLift 317165
  have htrace : WordTrace (prefixWord ++ tailWord_317165) baseStart_317165 baseEnd_317165 := by
    simpa [prefixWord, tailWord_317165, baseEnd_317165] using wordTrace_append hprefix tailTrace_317165
  have hstable : (prefixWord ++ tailWord_317165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317165).length < 2 ^ (prefixWord ++ tailWord_317165).sum := by decide
  have hdescent : baseEnd_317165 < baseStart_317165 := by decide
  rcases family_descends (prefixWord ++ tailWord_317165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317169 : List Nat := [1, 2, 2, 2, 2, 4, 1, 5]
def baseStart_317169 : Nat := 118140960795 + 317169 * 2 ^ 59
def prefixEnd_317169 : Nat := 4983230072969 + 3 ^ 40 * 317169 * 2
def baseEnd_317169 : Nat := 96509715973910997646739

theorem tailTrace_317169 : CollatzResearch.WordTrace tailWord_317169 prefixEnd_317169 96509715973910997646739 := by
  unfold tailWord_317169
  simp only [CollatzResearch.WordTrace]
  refine ⟨11568103787958355997762561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7712069191972237331841707 11568103787958355997762561)
  ·
    refine ⟨8676077840968766998321921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11568103787958355997762561 8676077840968766998321921)
    ·
      refine ⟨6507058380726575248741441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8676077840968766998321921 6507058380726575248741441)
      ·
        refine ⟨4880293785544931436556081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6507058380726575248741441 4880293785544931436556081)
        ·
          refine ⟨3660220339158698577417061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4880293785544931436556081 3660220339158698577417061)
          ·
            refine ⟨686291313592255983265699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3660220339158698577417061 686291313592255983265699)
            ·
              refine ⟨1029436970388383974898549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686291313592255983265699 1029436970388383974898549)
              ·
                refine ⟨96509715973910997646739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1029436970388383974898549 96509715973910997646739)
                ·
                  rfl

theorem cell19_317169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_317169 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317169 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317169 prefixEnd_317169 := by exact prefixLift 317169
  have htrace : WordTrace (prefixWord ++ tailWord_317169) baseStart_317169 baseEnd_317169 := by
    simpa [prefixWord, tailWord_317169, baseEnd_317169] using wordTrace_append hprefix tailTrace_317169
  have hstable : (prefixWord ++ tailWord_317169).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317169).length < 2 ^ (prefixWord ++ tailWord_317169).sum := by decide
  have hdescent : baseEnd_317169 < baseStart_317169 := by decide
  rcases family_descends (prefixWord ++ tailWord_317169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317188 : List Nat := [2, 3, 2, 2, 1, 2, 7]
def baseStart_317188 : Nat := 118140960795 + 317188 * 2 ^ 59
def prefixEnd_317188 : Nat := 4983230072969 + 3 ^ 40 * 317188 * 2
def baseEnd_317188 : Nat := 32171832461908194408155

theorem tailTrace_317188 : CollatzResearch.WordTrace tailWord_317188 prefixEnd_317188 32171832461908194408155 := by
  unfold tailWord_317188
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784398387444761121352109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7712531183259681495136145 5784398387444761121352109)
  ·
    refine ⟨2169149395291785420507041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5784398387444761121352109 2169149395291785420507041)
    ·
      refine ⟨1626862046468839065380281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2169149395291785420507041 1626862046468839065380281)
      ·
        refine ⟨1220146534851629299035211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1626862046468839065380281 1220146534851629299035211)
        ·
          refine ⟨1830219802277443948552817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1220146534851629299035211 1830219802277443948552817)
          ·
            refine ⟨1372664851708082961414613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1830219802277443948552817 1372664851708082961414613)
            ·
              refine ⟨32171832461908194408155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1372664851708082961414613 32171832461908194408155)
              ·
                rfl

theorem cell19_317188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 7].length) (baseStart_317188 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317188 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317188 prefixEnd_317188 := by exact prefixLift 317188
  have htrace : WordTrace (prefixWord ++ tailWord_317188) baseStart_317188 baseEnd_317188 := by
    simpa [prefixWord, tailWord_317188, baseEnd_317188] using wordTrace_append hprefix tailTrace_317188
  have hstable : (prefixWord ++ tailWord_317188).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317188).length < 2 ^ (prefixWord ++ tailWord_317188).sum := by decide
  have hdescent : baseEnd_317188 < baseStart_317188 := by decide
  rcases family_descends (prefixWord ++ tailWord_317188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317207 : List Nat := [1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_317207 : Nat := 118140960795 + 317207 * 2 ^ 59
def prefixEnd_317207 : Nat := 4983230072969 + 3 ^ 40 * 317207 * 2
def baseEnd_317207 : Nat := 96521278797538168802191

theorem tailTrace_317207 : CollatzResearch.WordTrace tailWord_317207 prefixEnd_317207 96521278797538168802191 := by
  unfold tailWord_317207
  simp only [CollatzResearch.WordTrace]
  refine ⟨11569489761820688487645875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7712993174547125658430583 11569489761820688487645875)
  ·
    refine ⟨17354234642731032731468813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11569489761820688487645875 17354234642731032731468813)
    ·
      refine ⟨6507837991024137274300805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17354234642731032731468813 6507837991024137274300805)
      ·
        refine ⟨1220219623317025738931401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6507837991024137274300805 1220219623317025738931401)
        ·
          refine ⟨915164717487769304198551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220219623317025738931401 915164717487769304198551)
          ·
            refine ⟨1372747076231653956297827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915164717487769304198551 1372747076231653956297827)
            ·
              refine ⟨2059120614347480934446741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1372747076231653956297827 2059120614347480934446741)
              ·
                refine ⟨96521278797538168802191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2059120614347480934446741 96521278797538168802191)
                ·
                  rfl

theorem cell19_317207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_317207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317207 prefixEnd_317207 := by exact prefixLift 317207
  have htrace : WordTrace (prefixWord ++ tailWord_317207) baseStart_317207 baseEnd_317207 := by
    simpa [prefixWord, tailWord_317207, baseEnd_317207] using wordTrace_append hprefix tailTrace_317207
  have hstable : (prefixWord ++ tailWord_317207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317207).length < 2 ^ (prefixWord ++ tailWord_317207).sum := by decide
  have hdescent : baseEnd_317207 < baseStart_317207 := by decide
  rcases family_descends (prefixWord ++ tailWord_317207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317245 : List Nat := [1, 4, 1, 4, 1, 8]
def baseStart_317245 : Nat := 118140960795 + 317245 * 2 ^ 59
def prefixEnd_317245 : Nat := 4983230072969 + 3 ^ 40 * 317245 * 2
def baseEnd_317245 : Nat := 10725871291240593328627

theorem tailTrace_317245 : CollatzResearch.WordTrace tailWord_317245 prefixEnd_317245 10725871291240593328627 := by
  unfold tailWord_317245
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570875735683020977529189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7713917157122013985019459 11570875735683020977529189)
  ·
    refine ⟨2169539200440566433286723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11570875735683020977529189 2169539200440566433286723)
    ·
      refine ⟨3254308800660849649930085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2169539200440566433286723 3254308800660849649930085)
      ·
        refine ⟨610182900123909309361891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3254308800660849649930085 610182900123909309361891)
        ·
          refine ⟨915274350185863964042837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610182900123909309361891 915274350185863964042837)
          ·
            refine ⟨10725871291240593328627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 915274350185863964042837 10725871291240593328627)
            ·
              rfl

theorem cell19_317245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 8].length) (baseStart_317245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317245 prefixEnd_317245 := by exact prefixLift 317245
  have htrace : WordTrace (prefixWord ++ tailWord_317245) baseStart_317245 baseEnd_317245 := by
    simpa [prefixWord, tailWord_317245, baseEnd_317245] using wordTrace_append hprefix tailTrace_317245
  have hstable : (prefixWord ++ tailWord_317245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317245).length < 2 ^ (prefixWord ++ tailWord_317245).sum := by decide
  have hdescent : baseEnd_317245 < baseStart_317245 := by decide
  rcases family_descends (prefixWord ++ tailWord_317245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317247 : List Nat := [1, 1, 2, 2, 13]
def baseStart_317247 : Nat := 118140960795 + 317247 * 2 ^ 59
def prefixEnd_317247 : Nat := 4983230072969 + 3 ^ 40 * 317247 * 2
def baseEnd_317247 : Nat := 3575312970030738070859

theorem tailTrace_317247 : CollatzResearch.WordTrace tailWord_317247 prefixEnd_317247 3575312970030738070859 := by
  unfold tailWord_317247
  simp only [CollatzResearch.WordTrace]
  refine ⟨11570948681675775319101995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7713965787783850212734663 11570948681675775319101995)
  ·
    refine ⟨17356423022513662978652993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11570948681675775319101995 17356423022513662978652993)
    ·
      refine ⟨13017317266885247233989745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17356423022513662978652993 13017317266885247233989745)
      ·
        refine ⟨9762987950163935425492309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13017317266885247233989745 9762987950163935425492309)
        ·
          refine ⟨3575312970030738070859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9762987950163935425492309 3575312970030738070859)
          ·
            rfl

theorem cell19_317247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 13].length) (baseStart_317247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317247 prefixEnd_317247 := by exact prefixLift 317247
  have htrace : WordTrace (prefixWord ++ tailWord_317247) baseStart_317247 baseEnd_317247 := by
    simpa [prefixWord, tailWord_317247, baseEnd_317247] using wordTrace_append hprefix tailTrace_317247
  have hstable : (prefixWord ++ tailWord_317247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317247).length < 2 ^ (prefixWord ++ tailWord_317247).sum := by decide
  have hdescent : baseEnd_317247 < baseStart_317247 := by decide
  rcases family_descends (prefixWord ++ tailWord_317247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317260 : List Nat := [2, 2, 1, 3, 5, 1, 1, 4]
def baseStart_317260 : Nat := 118140960795 + 317260 * 2 ^ 59
def prefixEnd_317260 : Nat := 4983230072969 + 3 ^ 40 * 317260 * 2
def baseEnd_317260 : Nat := 96537405893649749624269

theorem tailTrace_317260 : CollatzResearch.WordTrace tailWord_317260 prefixEnd_317260 96537405893649749624269 := by
  unfold tailWord_317260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5785711415314339269662617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7714281887085785692883489 5785711415314339269662617)
  ·
    refine ⟨4339283561485754452246963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5785711415314339269662617 4339283561485754452246963)
    ·
      refine ⟨6508925342228631678370445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4339283561485754452246963 6508925342228631678370445)
      ·
        refine ⟨2440847003335736879388917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6508925342228631678370445 2440847003335736879388917)
        ·
          refine ⟨228829406562725332442711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2440847003335736879388917 228829406562725332442711)
          ·
            refine ⟨343244109844087998664067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228829406562725332442711 343244109844087998664067)
            ·
              refine ⟨514866164766131997996101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343244109844087998664067 514866164766131997996101)
              ·
                refine ⟨96537405893649749624269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 514866164766131997996101 96537405893649749624269)
                ·
                  rfl

theorem cell19_317260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 4].length) (baseStart_317260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317260 prefixEnd_317260 := by exact prefixLift 317260
  have htrace : WordTrace (prefixWord ++ tailWord_317260) baseStart_317260 baseEnd_317260 := by
    simpa [prefixWord, tailWord_317260, baseEnd_317260] using wordTrace_append hprefix tailTrace_317260
  have hstable : (prefixWord ++ tailWord_317260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317260).length < 2 ^ (prefixWord ++ tailWord_317260).sum := by decide
  have hdescent : baseEnd_317260 < baseStart_317260 := by decide
  rcases family_descends (prefixWord ++ tailWord_317260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317323 : List Nat := [1, 1, 1, 1, 4, 2, 1, 8]
def baseStart_317323 : Nat := 118140960795 + 317323 * 2 ^ 59
def prefixEnd_317323 : Nat := 4983230072969 + 3 ^ 40 * 317323 * 2
def baseEnd_317323 : Nat := 96556575838084270224097

theorem tailTrace_317323 : CollatzResearch.WordTrace tailWord_317323 prefixEnd_317323 96556575838084270224097 := by
  unfold tailWord_317323
  simp only [CollatzResearch.WordTrace]
  refine ⟨11573720629400440298868623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7715813752933626865912415 11573720629400440298868623)
  ·
    refine ⟨17360580944100660448302935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11573720629400440298868623 17360580944100660448302935)
    ·
      refine ⟨26040871416150990672454403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17360580944100660448302935 26040871416150990672454403)
      ·
        refine ⟨39061307124226486008681605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26040871416150990672454403 39061307124226486008681605)
        ·
          refine ⟨7323995085792466126627801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39061307124226486008681605 7323995085792466126627801)
          ·
            refine ⟨5492996314344349594970851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7323995085792466126627801 5492996314344349594970851)
            ·
              refine ⟨8239494471516524392456277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5492996314344349594970851 8239494471516524392456277)
              ·
                refine ⟨96556575838084270224097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8239494471516524392456277 96556575838084270224097)
                ·
                  rfl

theorem cell19_317323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_317323 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317323 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317323 prefixEnd_317323 := by exact prefixLift 317323
  have htrace : WordTrace (prefixWord ++ tailWord_317323) baseStart_317323 baseEnd_317323 := by
    simpa [prefixWord, tailWord_317323, baseEnd_317323] using wordTrace_append hprefix tailTrace_317323
  have hstable : (prefixWord ++ tailWord_317323).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317323).length < 2 ^ (prefixWord ++ tailWord_317323).sum := by decide
  have hdescent : baseEnd_317323 < baseStart_317323 := by decide
  rcases family_descends (prefixWord ++ tailWord_317323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317334 : List Nat := [5, 3, 1, 1, 2, 1, 1, 5]
def baseStart_317334 : Nat := 118140960795 + 317334 * 2 ^ 59
def prefixEnd_317334 : Nat := 4983230072969 + 3 ^ 40 * 317334 * 2
def baseEnd_317334 : Nat := 96559922971239503979623

theorem tailTrace_317334 : CollatzResearch.WordTrace tailWord_317334 prefixEnd_317334 96559922971239503979623 := by
  unfold tailWord_317334
  simp only [CollatzResearch.WordTrace]
  refine ⟨723382614522536823594941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7716081221573726118346037 723382614522536823594941)
  ·
    refine ⟨271268480445951308848103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 723382614522536823594941 271268480445951308848103)
    ·
      refine ⟨406902720668926963272155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271268480445951308848103 406902720668926963272155)
      ·
        refine ⟨610354081003390444908233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406902720668926963272155 610354081003390444908233)
        ·
          refine ⟨457765560752542833681175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 610354081003390444908233 457765560752542833681175)
          ·
            refine ⟨686648341128814250521763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457765560752542833681175 686648341128814250521763)
            ·
              refine ⟨1029972511693221375782645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 686648341128814250521763 1029972511693221375782645)
              ·
                refine ⟨96559922971239503979623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1029972511693221375782645 96559922971239503979623)
                ·
                  rfl

theorem cell19_317334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_317334 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317334 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317334 prefixEnd_317334 := by exact prefixLift 317334
  have htrace : WordTrace (prefixWord ++ tailWord_317334) baseStart_317334 baseEnd_317334 := by
    simpa [prefixWord, tailWord_317334, baseEnd_317334] using wordTrace_append hprefix tailTrace_317334
  have hstable : (prefixWord ++ tailWord_317334).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317334).length < 2 ^ (prefixWord ++ tailWord_317334).sum := by decide
  have hdescent : baseEnd_317334 < baseStart_317334 := by decide
  rcases family_descends (prefixWord ++ tailWord_317334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317338 : List Nat := [3, 1, 1, 4, 2, 1, 4, 3]
def baseStart_317338 : Nat := 118140960795 + 317338 * 2 ^ 59
def prefixEnd_317338 : Nat := 4983230072969 + 3 ^ 40 * 317338 * 2
def baseEnd_317338 : Nat := 96561140110568679890723

theorem tailTrace_317338 : CollatzResearch.WordTrace tailWord_317338 prefixEnd_317338 96561140110568679890723 := by
  unfold tailWord_317338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893566931086524465166167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7716178482897398573776445 2893566931086524465166167)
  ·
    refine ⟨4340350396629786697749251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893566931086524465166167 4340350396629786697749251)
    ·
      refine ⟨6510525594944680046623877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4340350396629786697749251 6510525594944680046623877)
      ·
        refine ⟨1220723549052127508741977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6510525594944680046623877 1220723549052127508741977)
        ·
          refine ⟨915542661789095631556483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220723549052127508741977 915542661789095631556483)
          ·
            refine ⟨1373313992683643447334725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915542661789095631556483 1373313992683643447334725)
            ·
              refine ⟨257496373628183146375261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1373313992683643447334725 257496373628183146375261)
              ·
                refine ⟨96561140110568679890723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257496373628183146375261 96561140110568679890723)
                ·
                  rfl

theorem cell19_317338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_317338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317338 prefixEnd_317338 := by exact prefixLift 317338
  have htrace : WordTrace (prefixWord ++ tailWord_317338) baseStart_317338 baseEnd_317338 := by
    simpa [prefixWord, tailWord_317338, baseEnd_317338] using wordTrace_append hprefix tailTrace_317338
  have hstable : (prefixWord ++ tailWord_317338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317338).length < 2 ^ (prefixWord ++ tailWord_317338).sum := by decide
  have hdescent : baseEnd_317338 < baseStart_317338 := by decide
  rcases family_descends (prefixWord ++ tailWord_317338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317397 : List Nat := [1, 3, 2, 3, 2, 1, 2, 5]
def baseStart_317397 : Nat := 118140960795 + 317397 * 2 ^ 59
def prefixEnd_317397 : Nat := 4983230072969 + 3 ^ 40 * 317397 * 2
def baseEnd_317397 : Nat := 96579092915674024579451

theorem tailTrace_317397 : CollatzResearch.WordTrace tailWord_317397 prefixEnd_317397 96579092915674024579451 := by
  unfold tailWord_317397
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576419631132350937062445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7717613087421567291374963 11576419631132350937062445)
  ·
    refine ⟨4341157361674631601398417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11576419631132350937062445 4341157361674631601398417)
    ·
      refine ⟨3255868021255973701048813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4341157361674631601398417 3255868021255973701048813)
      ·
        refine ⟨1220950507970990137893305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3255868021255973701048813 1220950507970990137893305)
        ·
          refine ⟨915712880978242603419979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1220950507970990137893305 915712880978242603419979)
          ·
            refine ⟨1373569321467363905129969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915712880978242603419979 1373569321467363905129969)
            ·
              refine ⟨1030176991100522928847477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1373569321467363905129969 1030176991100522928847477)
              ·
                refine ⟨96579092915674024579451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030176991100522928847477 96579092915674024579451)
                ·
                  rfl

theorem cell19_317397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_317397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317397 prefixEnd_317397 := by exact prefixLift 317397
  have htrace : WordTrace (prefixWord ++ tailWord_317397) baseStart_317397 baseEnd_317397 := by
    simpa [prefixWord, tailWord_317397, baseEnd_317397] using wordTrace_append hprefix tailTrace_317397
  have hstable : (prefixWord ++ tailWord_317397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317397).length < 2 ^ (prefixWord ++ tailWord_317397).sum := by decide
  have hdescent : baseEnd_317397 < baseStart_317397 := by decide
  rcases family_descends (prefixWord ++ tailWord_317397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317399 : List Nat := [1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_317399 : Nat := 118140960795 + 317399 * 2 ^ 59
def prefixEnd_317399 : Nat := 4983230072969 + 3 ^ 40 * 317399 * 2
def baseEnd_317399 : Nat := 96579701485338612535001

theorem tailTrace_317399 : CollatzResearch.WordTrace tailWord_317399 prefixEnd_317399 96579701485338612535001 := by
  unfold tailWord_317399
  simp only [CollatzResearch.WordTrace]
  refine ⟨11576492577125105278635251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7717661718083403519090167 11576492577125105278635251)
  ·
    refine ⟨17364738865687657917952877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11576492577125105278635251 17364738865687657917952877)
    ·
      refine ⟨6511777074632871719232329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17364738865687657917952877 6511777074632871719232329)
      ·
        refine ⟨4883832805974653789424247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6511777074632871719232329 4883832805974653789424247)
        ·
          refine ⟨7325749208961980684136371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4883832805974653789424247 7325749208961980684136371)
          ·
            refine ⟨10988623813442971026204557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7325749208961980684136371 10988623813442971026204557)
            ·
              refine ⟨4120733930041114134826709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10988623813442971026204557 4120733930041114134826709)
              ·
                refine ⟨96579701485338612535001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4120733930041114134826709 96579701485338612535001)
                ·
                  rfl

theorem cell19_317399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_317399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317399 prefixEnd_317399 := by exact prefixLift 317399
  have htrace : WordTrace (prefixWord ++ tailWord_317399) baseStart_317399 baseEnd_317399 := by
    simpa [prefixWord, tailWord_317399, baseEnd_317399] using wordTrace_append hprefix tailTrace_317399
  have hstable : (prefixWord ++ tailWord_317399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317399).length < 2 ^ (prefixWord ++ tailWord_317399).sum := by decide
  have hdescent : baseEnd_317399 < baseStart_317399 := by decide
  rcases family_descends (prefixWord ++ tailWord_317399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317473 : List Nat := [1, 2, 3, 2, 4, 1, 6]
def baseStart_317473 : Nat := 118140960795 + 317473 * 2 ^ 59
def prefixEnd_317473 : Nat := 4983230072969 + 3 ^ 40 * 317473 * 2
def baseEnd_317473 : Nat := 32200739520976122296785

theorem tailTrace_317473 : CollatzResearch.WordTrace tailWord_317473 prefixEnd_317473 32200739520976122296785 := by
  unfold tailWord_317473
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579191578857015916829073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7719461052571343944552715 11579191578857015916829073)
  ·
    refine ⟨8684393684142761937621805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11579191578857015916829073 8684393684142761937621805)
    ·
      refine ⟨3256647631553535726608177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8684393684142761937621805 3256647631553535726608177)
      ·
        refine ⟨2442485723665151794956133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3256647631553535726608177 2442485723665151794956133)
        ·
          refine ⟨457966073187215961554275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2442485723665151794956133 457966073187215961554275)
          ·
            refine ⟨686949109780823942331413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 457966073187215961554275 686949109780823942331413)
            ·
              refine ⟨32200739520976122296785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 686949109780823942331413 32200739520976122296785)
              ·
                rfl

theorem cell19_317473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 6].length) (baseStart_317473 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317473 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317473 prefixEnd_317473 := by exact prefixLift 317473
  have htrace : WordTrace (prefixWord ++ tailWord_317473) baseStart_317473 baseEnd_317473 := by
    simpa [prefixWord, tailWord_317473, baseEnd_317473] using wordTrace_append hprefix tailTrace_317473
  have hstable : (prefixWord ++ tailWord_317473).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317473).length < 2 ^ (prefixWord ++ tailWord_317473).sum := by decide
  have hdescent : baseEnd_317473 < baseStart_317473 := by decide
  rcases family_descends (prefixWord ++ tailWord_317473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317475 : List Nat := [1, 1, 1, 4, 3, 1, 8]
def baseStart_317475 : Nat := 118140960795 + 317475 * 2 ^ 59
def prefixEnd_317475 : Nat := 4983230072969 + 3 ^ 40 * 317475 * 2
def baseEnd_317475 : Nat := 32200942377530984948635

theorem tailTrace_317475 : CollatzResearch.WordTrace tailWord_317475 prefixEnd_317475 32200942377530984948635 := by
  unfold tailWord_317475
  simp only [CollatzResearch.WordTrace]
  refine ⟨11579264524849770258401879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7719509683233180172267919 11579264524849770258401879)
  ·
    refine ⟨17368896787274655387602819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11579264524849770258401879 17368896787274655387602819)
    ·
      refine ⟨26053345180911983081404229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17368896787274655387602819 26053345180911983081404229)
      ·
        refine ⟨4885002221420996827763293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26053345180911983081404229 4885002221420996827763293)
        ·
          refine ⟨1831875833032873810411235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4885002221420996827763293 1831875833032873810411235)
          ·
            refine ⟨2747813749549310715616853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1831875833032873810411235 2747813749549310715616853)
            ·
              refine ⟨32200942377530984948635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2747813749549310715616853 32200942377530984948635)
              ·
                rfl

theorem cell19_317475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_317475 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317475 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317475 prefixEnd_317475 := by exact prefixLift 317475
  have htrace : WordTrace (prefixWord ++ tailWord_317475) baseStart_317475 baseEnd_317475 := by
    simpa [prefixWord, tailWord_317475, baseEnd_317475] using wordTrace_append hprefix tailTrace_317475
  have hstable : (prefixWord ++ tailWord_317475).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317475).length < 2 ^ (prefixWord ++ tailWord_317475).sum := by decide
  have hdescent : baseEnd_317475 < baseStart_317475 := by decide
  rcases family_descends (prefixWord ++ tailWord_317475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317513 : List Nat := [1, 2, 1, 1, 2, 2, 5, 5]
def baseStart_317513 : Nat := 118140960795 + 317513 * 2 ^ 59
def prefixEnd_317513 : Nat := 4983230072969 + 3 ^ 40 * 317513 * 2
def baseEnd_317513 : Nat := 96614389956220126001357

theorem tailTrace_317513 : CollatzResearch.WordTrace tailWord_317513 prefixEnd_317513 96614389956220126001357 := by
  unfold tailWord_317513
  simp only [CollatzResearch.WordTrace]
  refine ⟨11580650498712102748285193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7720433665808068498856795 11580650498712102748285193)
  ·
    refine ⟨8685487874034077061213895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11580650498712102748285193 8685487874034077061213895)
    ·
      refine ⟨13028231811051115591820843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8685487874034077061213895 13028231811051115591820843)
      ·
        refine ⟨19542347716576673387731265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13028231811051115591820843 19542347716576673387731265)
        ·
          refine ⟨14656760787432505040798449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19542347716576673387731265 14656760787432505040798449)
          ·
            refine ⟨10992570590574378780598837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14656760787432505040798449 10992570590574378780598837)
            ·
              refine ⟨1030553492866348010681141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10992570590574378780598837 1030553492866348010681141)
              ·
                refine ⟨96614389956220126001357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1030553492866348010681141 96614389956220126001357)
                ·
                  rfl

theorem cell19_317513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_317513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317513 prefixEnd_317513 := by exact prefixLift 317513
  have htrace : WordTrace (prefixWord ++ tailWord_317513) baseStart_317513 baseEnd_317513 := by
    simpa [prefixWord, tailWord_317513, baseEnd_317513] using wordTrace_append hprefix tailTrace_317513
  have hstable : (prefixWord ++ tailWord_317513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317513).length < 2 ^ (prefixWord ++ tailWord_317513).sum := by decide
  have hdescent : baseEnd_317513 < baseStart_317513 := by decide
  rcases family_descends (prefixWord ++ tailWord_317513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317526 : List Nat := [5, 2, 2, 1, 1, 3, 5]
def baseStart_317526 : Nat := 118140960795 + 317526 * 2 ^ 59
def prefixEnd_317526 : Nat := 4983230072969 + 3 ^ 40 * 317526 * 2
def baseEnd_317526 : Nat := 32206115219679982570811

theorem tailTrace_317526 : CollatzResearch.WordTrace tailWord_317526 prefixEnd_317526 32206115219679982570811 := by
  unfold tailWord_317526
  simp only [CollatzResearch.WordTrace]
  refine ⟨723820290479062873031777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7720749765110003979005621 723820290479062873031777)
  ·
    refine ⟨542865217859297154773833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 723820290479062873031777 542865217859297154773833)
    ·
      refine ⟨407148913394472866080375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542865217859297154773833 407148913394472866080375)
      ·
        refine ⟨610723370091709299120563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407148913394472866080375 610723370091709299120563)
        ·
          refine ⟨916085055137563948680845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610723370091709299120563 916085055137563948680845)
          ·
            refine ⟨343531895676586480755317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 916085055137563948680845 343531895676586480755317)
            ·
              refine ⟨32206115219679982570811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 343531895676586480755317 32206115219679982570811)
              ·
                rfl

theorem cell19_317526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_317526 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317526 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317526 prefixEnd_317526 := by exact prefixLift 317526
  have htrace : WordTrace (prefixWord ++ tailWord_317526) baseStart_317526 baseEnd_317526 := by
    simpa [prefixWord, tailWord_317526, baseEnd_317526] using wordTrace_append hprefix tailTrace_317526
  have hstable : (prefixWord ++ tailWord_317526).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317526).length < 2 ^ (prefixWord ++ tailWord_317526).sum := by decide
  have hdescent : baseEnd_317526 < baseStart_317526 := by decide
  rcases family_descends (prefixWord ++ tailWord_317526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317549 : List Nat := [1, 5, 1, 1, 2, 1, 4, 4]
def baseStart_317549 : Nat := 118140960795 + 317549 * 2 ^ 59
def prefixEnd_317549 : Nat := 4983230072969 + 3 ^ 40 * 317549 * 2
def baseEnd_317549 : Nat := 96625344210182709201259

theorem tailTrace_317549 : CollatzResearch.WordTrace tailWord_317549 prefixEnd_317549 96625344210182709201259 := by
  unfold tailWord_317549
  simp only [CollatzResearch.WordTrace]
  refine ⟨11581963526581680896595701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7721309017721120597730467 11581963526581680896595701)
  ·
    refine ⟨1085809080617032584055847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11581963526581680896595701 1085809080617032584055847)
    ·
      refine ⟨1628713620925548876083771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085809080617032584055847 1628713620925548876083771)
      ·
        refine ⟨2443070431388323314125657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628713620925548876083771 2443070431388323314125657)
        ·
          refine ⟨1832302823541242485594243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2443070431388323314125657 1832302823541242485594243)
          ·
            refine ⟨2748454235311863728391365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832302823541242485594243 2748454235311863728391365)
            ·
              refine ⟨515335169120974449073381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2748454235311863728391365 515335169120974449073381)
              ·
                refine ⟨96625344210182709201259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515335169120974449073381 96625344210182709201259)
                ·
                  rfl

theorem cell19_317549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_317549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317549 prefixEnd_317549 := by exact prefixLift 317549
  have htrace : WordTrace (prefixWord ++ tailWord_317549) baseStart_317549 baseEnd_317549 := by
    simpa [prefixWord, tailWord_317549, baseEnd_317549] using wordTrace_append hprefix tailTrace_317549
  have hstable : (prefixWord ++ tailWord_317549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317549).length < 2 ^ (prefixWord ++ tailWord_317549).sum := by decide
  have hdescent : baseEnd_317549 < baseStart_317549 := by decide
  rcases family_descends (prefixWord ++ tailWord_317549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317551 : List Nat := [1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_317551 : Nat := 118140960795 + 317551 * 2 ^ 59
def prefixEnd_317551 : Nat := 4983230072969 + 3 ^ 40 * 317551 * 2
def baseEnd_317551 : Nat := 96625952779847297156809

theorem tailTrace_317551 : CollatzResearch.WordTrace tailWord_317551 prefixEnd_317551 96625952779847297156809 := by
  unfold tailWord_317551
  simp only [CollatzResearch.WordTrace]
  refine ⟨11582036472574435238168507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7721357648382956825445671 11582036472574435238168507)
  ·
    refine ⟨17373054708861652857252761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11582036472574435238168507 17373054708861652857252761)
    ·
      refine ⟨13029791031646239642939571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17373054708861652857252761 13029791031646239642939571)
      ·
        refine ⟨19544686547469359464409357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13029791031646239642939571 19544686547469359464409357)
        ·
          refine ⟨7329257455301009799153509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19544686547469359464409357 7329257455301009799153509)
          ·
            refine ⟨1374235772868939337341283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7329257455301009799153509 1374235772868939337341283)
            ·
              refine ⟨2061353659303409006011925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374235772868939337341283 2061353659303409006011925)
              ·
                refine ⟨96625952779847297156809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2061353659303409006011925 96625952779847297156809)
                ·
                  rfl

theorem cell19_317551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_317551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317551 prefixEnd_317551 := by exact prefixLift 317551
  have htrace : WordTrace (prefixWord ++ tailWord_317551) baseStart_317551 baseEnd_317551 := by
    simpa [prefixWord, tailWord_317551, baseEnd_317551] using wordTrace_append hprefix tailTrace_317551
  have hstable : (prefixWord ++ tailWord_317551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317551).length < 2 ^ (prefixWord ++ tailWord_317551).sum := by decide
  have hdescent : baseEnd_317551 < baseStart_317551 := by decide
  rcases family_descends (prefixWord ++ tailWord_317551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317604 : List Nat := [2, 3, 1, 2, 4, 2, 1, 4]
def baseStart_317604 : Nat := 118140960795 + 317604 * 2 ^ 59
def prefixEnd_317604 : Nat := 4983230072969 + 3 ^ 40 * 317604 * 2
def baseEnd_317604 : Nat := 96642079875958877978887

theorem tailTrace_317604 : CollatzResearch.WordTrace tailWord_317604 prefixEnd_317604 96642079875958877978887 := by
  unfold tailWord_317604
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791984770691212644923933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7722646360921616859898577 5791984770691212644923933)
  ·
    refine ⟨2171994289009204741846475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5791984770691212644923933 2171994289009204741846475)
    ·
      refine ⟨3257991433513807112769713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2171994289009204741846475 3257991433513807112769713)
      ·
        refine ⟨2443493575135355334577285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3257991433513807112769713 2443493575135355334577285)
        ·
          refine ⟨458155045337879125233241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2443493575135355334577285 458155045337879125233241)
          ·
            refine ⟨343616284003409343924931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458155045337879125233241 343616284003409343924931)
            ·
              refine ⟨515424426005114015887397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343616284003409343924931 515424426005114015887397)
              ·
                refine ⟨96642079875958877978887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515424426005114015887397 96642079875958877978887)
                ·
                  rfl

theorem cell19_317604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_317604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317604 prefixEnd_317604 := by exact prefixLift 317604
  have htrace : WordTrace (prefixWord ++ tailWord_317604) baseStart_317604 baseEnd_317604 := by
    simpa [prefixWord, tailWord_317604, baseEnd_317604] using wordTrace_append hprefix tailTrace_317604
  have hstable : (prefixWord ++ tailWord_317604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317604).length < 2 ^ (prefixWord ++ tailWord_317604).sum := by decide
  have hdescent : baseEnd_317604 < baseStart_317604 := by decide
  rcases family_descends (prefixWord ++ tailWord_317604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317621 : List Nat := [1, 3, 3, 4, 1, 1, 3, 3]
def baseStart_317621 : Nat := 118140960795 + 317621 * 2 ^ 59
def prefixEnd_317621 : Nat := 4983230072969 + 3 ^ 40 * 317621 * 2
def baseEnd_317621 : Nat := 96647252718107875601063

theorem tailTrace_317621 : CollatzResearch.WordTrace tailWord_317621 prefixEnd_317621 96647252718107875601063 := by
  unfold tailWord_317621
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584589582320837193216717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7723059721547224795477811 11584589582320837193216717)
  ·
    refine ⟨4344221093370313947456269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11584589582320837193216717 4344221093370313947456269)
    ·
      refine ⟨1629082910013867730296101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4344221093370313947456269 1629082910013867730296101)
      ·
        refine ⟨305453045627600199430519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1629082910013867730296101 305453045627600199430519)
        ·
          refine ⟨458179568441400299145779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305453045627600199430519 458179568441400299145779)
          ·
            refine ⟨687269352662100448718669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458179568441400299145779 687269352662100448718669)
            ·
              refine ⟨257726007248287668269501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687269352662100448718669 257726007248287668269501)
              ·
                refine ⟨96647252718107875601063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257726007248287668269501 96647252718107875601063)
                ·
                  rfl

theorem cell19_317621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_317621 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317621 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317621 prefixEnd_317621 := by exact prefixLift 317621
  have htrace : WordTrace (prefixWord ++ tailWord_317621) baseStart_317621 baseEnd_317621 := by
    simpa [prefixWord, tailWord_317621, baseEnd_317621] using wordTrace_append hprefix tailTrace_317621
  have hstable : (prefixWord ++ tailWord_317621).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317621).length < 2 ^ (prefixWord ++ tailWord_317621).sum := by decide
  have hdescent : baseEnd_317621 < baseStart_317621 := by decide
  rcases family_descends (prefixWord ++ tailWord_317621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317625 : List Nat := [1, 2, 1, 4, 1, 2, 5, 3]
def baseStart_317625 : Nat := 118140960795 + 317625 * 2 ^ 59
def prefixEnd_317625 : Nat := 4983230072969 + 3 ^ 40 * 317625 * 2
def baseEnd_317625 : Nat := 96648469857437051512163

theorem tailTrace_317625 : CollatzResearch.WordTrace tailWord_317625 prefixEnd_317625 96648469857437051512163 := by
  unfold tailWord_317625
  simp only [CollatzResearch.WordTrace]
  refine ⟨11584735474306345876362329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7723156982870897250908219 11584735474306345876362329)
  ·
    refine ⟨8688551605729759407271747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11584735474306345876362329 8688551605729759407271747)
    ·
      refine ⟨13032827408594639110907621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688551605729759407271747 13032827408594639110907621)
      ·
        refine ⟨2443655139111494833295179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13032827408594639110907621 2443655139111494833295179)
        ·
          refine ⟨3665482708667242249942769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2443655139111494833295179 3665482708667242249942769)
          ·
            refine ⟨2749112031500431687457077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3665482708667242249942769 2749112031500431687457077)
            ·
              refine ⟨257729252953165470699101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2749112031500431687457077 257729252953165470699101)
              ·
                refine ⟨96648469857437051512163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257729252953165470699101 96648469857437051512163)
                ·
                  rfl

theorem cell19_317625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 3].length) (baseStart_317625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317625 prefixEnd_317625 := by exact prefixLift 317625
  have htrace : WordTrace (prefixWord ++ tailWord_317625) baseStart_317625 baseEnd_317625 := by
    simpa [prefixWord, tailWord_317625, baseEnd_317625] using wordTrace_append hprefix tailTrace_317625
  have hstable : (prefixWord ++ tailWord_317625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317625).length < 2 ^ (prefixWord ++ tailWord_317625).sum := by decide
  have hdescent : baseEnd_317625 < baseStart_317625 := by decide
  rcases family_descends (prefixWord ++ tailWord_317625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317665 : List Nat := [1, 2, 3, 1, 3, 1, 2, 6]
def baseStart_317665 : Nat := 118140960795 + 317665 * 2 ^ 59
def prefixEnd_317665 : Nat := 4983230072969 + 3 ^ 40 * 317665 * 2
def baseEnd_317665 : Nat := 96660641250728810623165

theorem tailTrace_317665 : CollatzResearch.WordTrace tailWord_317665 prefixEnd_317665 96660641250728810623165 := by
  unfold tailWord_317665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11586194394161432707818449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7724129596107621805212299 11586194394161432707818449)
  ·
    refine ⟨8689645795621074530863837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11586194394161432707818449 8689645795621074530863837)
    ·
      refine ⟨3258617173357902949073939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8689645795621074530863837 3258617173357902949073939)
      ·
        refine ⟨4887925760036854423610909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3258617173357902949073939 4887925760036854423610909)
        ·
          refine ⟨1832972160013820408854091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4887925760036854423610909 1832972160013820408854091)
          ·
            refine ⟨2749458240020730613281137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832972160013820408854091 2749458240020730613281137)
            ·
              refine ⟨2062093680015547959960853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2749458240020730613281137 2062093680015547959960853)
              ·
                refine ⟨96660641250728810623165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2062093680015547959960853 96660641250728810623165)
                ·
                  rfl

theorem cell19_317665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_317665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317665 prefixEnd_317665 := by exact prefixLift 317665
  have htrace : WordTrace (prefixWord ++ tailWord_317665) baseStart_317665 baseEnd_317665 := by
    simpa [prefixWord, tailWord_317665, baseEnd_317665] using wordTrace_append hprefix tailTrace_317665
  have hstable : (prefixWord ++ tailWord_317665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317665).length < 2 ^ (prefixWord ++ tailWord_317665).sum := by decide
  have hdescent : baseEnd_317665 < baseStart_317665 := by decide
  rcases family_descends (prefixWord ++ tailWord_317665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317682 : List Nat := [3, 2, 1, 3, 2, 2, 1, 5]
def baseStart_317682 : Nat := 118140960795 + 317682 * 2 ^ 59
def prefixEnd_317682 : Nat := 4983230072969 + 3 ^ 40 * 317682 * 2
def baseEnd_317682 : Nat := 96665814092877808245341

theorem tailTrace_317682 : CollatzResearch.WordTrace tailWord_317682 prefixEnd_317682 96665814092877808245341 := by
  unfold tailWord_317682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896703608774961152796825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7724542956733229740791533 2896703608774961152796825)
  ·
    refine ⟨2172527706581220864597619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2896703608774961152796825 2172527706581220864597619)
    ·
      refine ⟨3258791559871831296896429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172527706581220864597619 3258791559871831296896429)
      ·
        refine ⟨1222046834951936736336161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3258791559871831296896429 1222046834951936736336161)
        ·
          refine ⟨916535126213952552252121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1222046834951936736336161 916535126213952552252121)
          ·
            refine ⟨687401344660464414189091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 916535126213952552252121 687401344660464414189091)
            ·
              refine ⟨1031102016990696621283637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687401344660464414189091 1031102016990696621283637)
              ·
                refine ⟨96665814092877808245341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031102016990696621283637 96665814092877808245341)
                ·
                  rfl

theorem cell19_317682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_317682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317682 prefixEnd_317682 := by exact prefixLift 317682
  have htrace : WordTrace (prefixWord ++ tailWord_317682) baseStart_317682 baseEnd_317682 := by
    simpa [prefixWord, tailWord_317682, baseEnd_317682] using wordTrace_append hprefix tailTrace_317682
  have hstable : (prefixWord ++ tailWord_317682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317682).length < 2 ^ (prefixWord ++ tailWord_317682).sum := by decide
  have hdescent : baseEnd_317682 < baseStart_317682 := by decide
  rcases family_descends (prefixWord ++ tailWord_317682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317777 : List Nat := [1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_317777 : Nat := 118140960795 + 317777 * 2 ^ 59
def prefixEnd_317777 : Nat := 4983230072969 + 3 ^ 40 * 317777 * 2
def baseEnd_317777 : Nat := 96694721151945736133971

theorem tailTrace_317777 : CollatzResearch.WordTrace tailWord_317777 prefixEnd_317777 96694721151945736133971 := by
  unfold tailWord_317777
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590279369755675835895585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7726852913170450557263723 11590279369755675835895585)
  ·
    refine ⟨8692709527316756876921689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11590279369755675835895585 8692709527316756876921689)
    ·
      refine ⟨6519532145487567657691267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8692709527316756876921689 6519532145487567657691267)
      ·
        refine ⟨9779298218231351486536901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519532145487567657691267 9779298218231351486536901)
        ·
          refine ⟨1833618415918378403725669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9779298218231351486536901 1833618415918378403725669)
          ·
            refine ⟨343803452984695950698563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1833618415918378403725669 343803452984695950698563)
            ·
              refine ⟨515705179477043926047845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343803452984695950698563 515705179477043926047845)
              ·
                refine ⟨96694721151945736133971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515705179477043926047845 96694721151945736133971)
                ·
                  rfl

theorem cell19_317777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_317777 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317777 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317777 prefixEnd_317777 := by exact prefixLift 317777
  have htrace : WordTrace (prefixWord ++ tailWord_317777) baseStart_317777 baseEnd_317777 := by
    simpa [prefixWord, tailWord_317777, baseEnd_317777] using wordTrace_append hprefix tailTrace_317777
  have hstable : (prefixWord ++ tailWord_317777).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317777).length < 2 ^ (prefixWord ++ tailWord_317777).sum := by decide
  have hdescent : baseEnd_317777 < baseStart_317777 := by decide
  rcases family_descends (prefixWord ++ tailWord_317777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317794 : List Nat := [3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_317794 : Nat := 118140960795 + 317794 * 2 ^ 59
def prefixEnd_317794 : Nat := 4983230072969 + 3 ^ 40 * 317794 * 2
def baseEnd_317794 : Nat := 96699893994094733756147

theorem tailTrace_317794 : CollatzResearch.WordTrace tailWord_317794 prefixEnd_317794 96699893994094733756147 := by
  unfold tailWord_317794
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897724852673521934816109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7727266273796058492842957 2897724852673521934816109)
  ·
    refine ⟨1086646819752570725556041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2897724852673521934816109 1086646819752570725556041)
    ·
      refine ⟨814985114814428044167031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1086646819752570725556041 814985114814428044167031)
      ·
        refine ⟨1222477672221642066250547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814985114814428044167031 1222477672221642066250547)
        ·
          refine ⟨1833716508332463099375821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222477672221642066250547 1833716508332463099375821)
          ·
            refine ⟨687643690624673662265933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1833716508332463099375821 687643690624673662265933)
            ·
              refine ⟨257866383984252623349725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687643690624673662265933 257866383984252623349725)
              ·
                refine ⟨96699893994094733756147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257866383984252623349725 96699893994094733756147)
                ·
                  rfl

theorem cell19_317794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_317794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317794 prefixEnd_317794 := by exact prefixLift 317794
  have htrace : WordTrace (prefixWord ++ tailWord_317794) baseStart_317794 baseEnd_317794 := by
    simpa [prefixWord, tailWord_317794, baseEnd_317794] using wordTrace_append hprefix tailTrace_317794
  have hstable : (prefixWord ++ tailWord_317794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317794).length < 2 ^ (prefixWord ++ tailWord_317794).sum := by decide
  have hdescent : baseEnd_317794 < baseStart_317794 := by decide
  rcases family_descends (prefixWord ++ tailWord_317794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317796 : List Nat := [2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_317796 : Nat := 118140960795 + 317796 * 2 ^ 59
def prefixEnd_317796 : Nat := 4983230072969 + 3 ^ 40 * 317796 * 2
def baseEnd_317796 : Nat := 96700502563759321711697

theorem tailTrace_317796 : CollatzResearch.WordTrace tailWord_317796 prefixEnd_317796 96700502563759321711697 := by
  unfold tailWord_317796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795486178343421040418621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7727314904457894720558161 5795486178343421040418621)
  ·
    refine ⟨2173307316878782890156983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5795486178343421040418621 2173307316878782890156983)
    ·
      refine ⟨3259960975318174335235475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173307316878782890156983 3259960975318174335235475)
      ·
        refine ⟨4889941462977261502853213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3259960975318174335235475 4889941462977261502853213)
        ·
          refine ⟨1833728048616473063569955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4889941462977261502853213 1833728048616473063569955)
          ·
            refine ⟨2750592072924709595354933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833728048616473063569955 2750592072924709595354933)
            ·
              refine ⟨257868006836691524564525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2750592072924709595354933 257868006836691524564525)
              ·
                refine ⟨96700502563759321711697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257868006836691524564525 96700502563759321711697)
                ·
                  rfl

theorem cell19_317796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_317796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317796 prefixEnd_317796 := by exact prefixLift 317796
  have htrace : WordTrace (prefixWord ++ tailWord_317796) baseStart_317796 baseEnd_317796 := by
    simpa [prefixWord, tailWord_317796, baseEnd_317796] using wordTrace_append hprefix tailTrace_317796
  have hstable : (prefixWord ++ tailWord_317796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317796).length < 2 ^ (prefixWord ++ tailWord_317796).sum := by decide
  have hdescent : baseEnd_317796 < baseStart_317796 := by decide
  rcases family_descends (prefixWord ++ tailWord_317796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317853 : List Nat := [1, 4, 2, 1, 4, 1, 1, 5]
def baseStart_317853 : Nat := 118140960795 + 317853 * 2 ^ 59
def prefixEnd_317853 : Nat := 4983230072969 + 3 ^ 40 * 317853 * 2
def baseEnd_317853 : Nat := 96717846799200078444875

theorem tailTrace_317853 : CollatzResearch.WordTrace tailWord_317853 prefixEnd_317853 96717846799200078444875 := by
  unfold tailWord_317853
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593051317480340815662213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7728700878320227210441475 11593051317480340815662213)
  ·
    refine ⟨2173697122027563902936665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11593051317480340815662213 2173697122027563902936665)
    ·
      refine ⟨1630272841520672927202499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173697122027563902936665 1630272841520672927202499)
      ·
        refine ⟨2445409262281009390803749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1630272841520672927202499 2445409262281009390803749)
        ·
          refine ⟨458514236677689260775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2445409262281009390803749 458514236677689260775703)
          ·
            refine ⟨687771355016533891163555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458514236677689260775703 687771355016533891163555)
            ·
              refine ⟨1031657032524800836745333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687771355016533891163555 1031657032524800836745333)
              ·
                refine ⟨96717846799200078444875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031657032524800836745333 96717846799200078444875)
                ·
                  rfl

theorem cell19_317853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_317853 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317853 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317853 prefixEnd_317853 := by exact prefixLift 317853
  have htrace : WordTrace (prefixWord ++ tailWord_317853) baseStart_317853 baseEnd_317853 := by
    simpa [prefixWord, tailWord_317853, baseEnd_317853] using wordTrace_append hprefix tailTrace_317853
  have hstable : (prefixWord ++ tailWord_317853).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317853).length < 2 ^ (prefixWord ++ tailWord_317853).sum := by decide
  have hdescent : baseEnd_317853 < baseStart_317853 := by decide
  rcases family_descends (prefixWord ++ tailWord_317853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317855 : List Nat := [1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_317855 : Nat := 118140960795 + 317855 * 2 ^ 59
def prefixEnd_317855 : Nat := 4983230072969 + 3 ^ 40 * 317855 * 2
def baseEnd_317855 : Nat := 96718455368864666400425

theorem tailTrace_317855 : CollatzResearch.WordTrace tailWord_317855 prefixEnd_317855 96718455368864666400425 := by
  unfold tailWord_317855
  simp only [CollatzResearch.WordTrace]
  refine ⟨11593124263473095157235019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7728749508982063438156679 11593124263473095157235019)
  ·
    refine ⟨17389686395209642735852529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11593124263473095157235019 17389686395209642735852529)
    ·
      refine ⟨13042264796407232051889397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17389686395209642735852529 13042264796407232051889397)
      ·
        refine ⟨1222712324663178004864631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13042264796407232051889397 1222712324663178004864631)
        ·
          refine ⟨1834068486994767007296947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222712324663178004864631 1834068486994767007296947)
          ·
            refine ⟨2751102730492150510945421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834068486994767007296947 2751102730492150510945421)
            ·
              refine ⟨1031663523934556441604533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2751102730492150510945421 1031663523934556441604533)
              ·
                refine ⟨96718455368864666400425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031663523934556441604533 96718455368864666400425)
                ·
                  rfl

theorem cell19_317855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_317855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317855 prefixEnd_317855 := by exact prefixLift 317855
  have htrace : WordTrace (prefixWord ++ tailWord_317855) baseStart_317855 baseEnd_317855 := by
    simpa [prefixWord, tailWord_317855, baseEnd_317855] using wordTrace_append hprefix tailTrace_317855
  have hstable : (prefixWord ++ tailWord_317855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317855).length < 2 ^ (prefixWord ++ tailWord_317855).sum := by decide
  have hdescent : baseEnd_317855 < baseStart_317855 := by decide
  rcases family_descends (prefixWord ++ tailWord_317855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317866 : List Nat := [3, 1, 6, 1, 2, 1, 5]
def baseStart_317866 : Nat := 118140960795 + 317866 * 2 ^ 59
def prefixEnd_317866 : Nat := 4983230072969 + 3 ^ 40 * 317866 * 2
def baseEnd_317866 : Nat := 32240600834006633385317

theorem tailTrace_317866 : CollatzResearch.WordTrace tailWord_317866 prefixEnd_317866 32240600834006633385317 := by
  unfold tailWord_317866
  simp only [CollatzResearch.WordTrace]
  refine ⟨2898381366608311008971363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7729016977622162690590301 2898381366608311008971363)
  ·
    refine ⟨4347572049912466513457045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2898381366608311008971363 4347572049912466513457045)
    ·
      refine ⟨203792439839646867818299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4347572049912466513457045 203792439839646867818299)
      ·
        refine ⟨305688659759470301727449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203792439839646867818299 305688659759470301727449)
        ·
          refine ⟨229266494819602726295587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305688659759470301727449 229266494819602726295587)
          ·
            refine ⟨343899742229404089443381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229266494819602726295587 343899742229404089443381)
            ·
              refine ⟨32240600834006633385317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 343899742229404089443381 32240600834006633385317)
              ·
                rfl

theorem cell19_317866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 5].length) (baseStart_317866 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317866 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317866 prefixEnd_317866 := by exact prefixLift 317866
  have htrace : WordTrace (prefixWord ++ tailWord_317866) baseStart_317866 baseEnd_317866 := by
    simpa [prefixWord, tailWord_317866, baseEnd_317866] using wordTrace_append hprefix tailTrace_317866
  have hstable : (prefixWord ++ tailWord_317866).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317866).length < 2 ^ (prefixWord ++ tailWord_317866).sum := by decide
  have hdescent : baseEnd_317866 < baseStart_317866 := by decide
  rcases family_descends (prefixWord ++ tailWord_317866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_317910 : List Nat := [5, 2, 1, 1, 1, 1, 1, 7]
def baseStart_317910 : Nat := 118140960795 + 317910 * 2 ^ 59
def prefixEnd_317910 : Nat := 4983230072969 + 3 ^ 40 * 317910 * 2
def baseEnd_317910 : Nat := 96735191034640835178053

theorem tailTrace_317910 : CollatzResearch.WordTrace tailWord_317910 prefixEnd_317910 96735191034640835178053 := by
  unfold tailWord_317910
  simp only [CollatzResearch.WordTrace]
  refine ⟨724695642392114971905449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7730086852182559700324789 724695642392114971905449)
  ·
    refine ⟨543521731794086228929087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 724695642392114971905449 543521731794086228929087)
    ·
      refine ⟨815282597691129343393631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543521731794086228929087 815282597691129343393631)
      ·
        refine ⟨1222923896536694015090447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815282597691129343393631 1222923896536694015090447)
        ·
          refine ⟨1834385844805041022635671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222923896536694015090447 1834385844805041022635671)
          ·
            refine ⟨2751578767207561533953507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834385844805041022635671 2751578767207561533953507)
            ·
              refine ⟨4127368150811342300930261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751578767207561533953507 4127368150811342300930261)
              ·
                refine ⟨96735191034640835178053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4127368150811342300930261 96735191034640835178053)
                ·
                  rfl

theorem cell19_317910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_317910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_317910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_317910 prefixEnd_317910 := by exact prefixLift 317910
  have htrace : WordTrace (prefixWord ++ tailWord_317910) baseStart_317910 baseEnd_317910 := by
    simpa [prefixWord, tailWord_317910, baseEnd_317910] using wordTrace_append hprefix tailTrace_317910
  have hstable : (prefixWord ++ tailWord_317910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_317910).length < 2 ^ (prefixWord ++ tailWord_317910).sum := by decide
  have hdescent : baseEnd_317910 < baseStart_317910 := by decide
  rcases family_descends (prefixWord ++ tailWord_317910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318020 : List Nat := [2, 3, 5, 1, 1, 1, 1, 5]
def baseStart_318020 : Nat := 118140960795 + 318020 * 2 ^ 59
def prefixEnd_318020 : Nat := 4983230072969 + 3 ^ 40 * 318020 * 2
def baseEnd_318020 : Nat := 96768662366193172733309

theorem tailTrace_318020 : CollatzResearch.WordTrace tailWord_318020 prefixEnd_318020 96768662366193172733309 := by
  unfold tailWord_318020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799571153937664168495757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7732761538583552224661009 5799571153937664168495757)
  ·
    refine ⟨2174839182726624063185909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5799571153937664168495757 2174839182726624063185909)
    ·
      refine ⟨203891173380621005923679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2174839182726624063185909 203891173380621005923679)
      ·
        refine ⟨305836760070931508885519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203891173380621005923679 305836760070931508885519)
        ·
          refine ⟨458755140106397263328279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305836760070931508885519 458755140106397263328279)
          ·
            refine ⟨688132710159595894992419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458755140106397263328279 688132710159595894992419)
            ·
              refine ⟨1032199065239393842488629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688132710159595894992419 1032199065239393842488629)
              ·
                refine ⟨96768662366193172733309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1032199065239393842488629 96768662366193172733309)
                ·
                  rfl

theorem cell19_318020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_318020 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318020 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318020 prefixEnd_318020 := by exact prefixLift 318020
  have htrace : WordTrace (prefixWord ++ tailWord_318020) baseStart_318020 baseEnd_318020 := by
    simpa [prefixWord, tailWord_318020, baseEnd_318020] using wordTrace_append hprefix tailTrace_318020
  have hstable : (prefixWord ++ tailWord_318020).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318020).length < 2 ^ (prefixWord ++ tailWord_318020).sum := by decide
  have hdescent : baseEnd_318020 < baseStart_318020 := by decide
  rcases family_descends (prefixWord ++ tailWord_318020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318022 : List Nat := [6, 1, 1, 1, 2, 2, 1, 5]
def baseStart_318022 : Nat := 118140960795 + 318022 * 2 ^ 59
def prefixEnd_318022 : Nat := 4983230072969 + 3 ^ 40 * 318022 * 2
def baseEnd_318022 : Nat := 96769270935857760688859

theorem tailTrace_318022 : CollatzResearch.WordTrace tailWord_318022 prefixEnd_318022 96769270935857760688859 := by
  unfold tailWord_318022
  simp only [CollatzResearch.WordTrace]
  refine ⟨362475476683377583705135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7732810169245388452376213 362475476683377583705135)
  ·
    refine ⟨543713215025066375557703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 362475476683377583705135 543713215025066375557703)
    ·
      refine ⟨815569822537599563336555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 543713215025066375557703 815569822537599563336555)
      ·
        refine ⟨1223354733806399345004833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815569822537599563336555 1223354733806399345004833)
        ·
          refine ⟨917516050354799508753625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1223354733806399345004833 917516050354799508753625)
          ·
            refine ⟨688137037766099631565219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917516050354799508753625 688137037766099631565219)
            ·
              refine ⟨1032205556649149447347829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688137037766099631565219 1032205556649149447347829)
              ·
                refine ⟨96769270935857760688859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1032205556649149447347829 96769270935857760688859)
                ·
                  rfl

theorem cell19_318022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_318022 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318022 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318022 prefixEnd_318022 := by exact prefixLift 318022
  have htrace : WordTrace (prefixWord ++ tailWord_318022) baseStart_318022 baseEnd_318022 := by
    simpa [prefixWord, tailWord_318022, baseEnd_318022] using wordTrace_append hprefix tailTrace_318022
  have hstable : (prefixWord ++ tailWord_318022).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318022).length < 2 ^ (prefixWord ++ tailWord_318022).sum := by decide
  have hdescent : baseEnd_318022 < baseStart_318022 := by decide
  rcases family_descends (prefixWord ++ tailWord_318022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318026 : List Nat := [3, 1, 2, 1, 1, 5, 1, 5]
def baseStart_318026 : Nat := 118140960795 + 318026 * 2 ^ 59
def prefixEnd_318026 : Nat := 4983230072969 + 3 ^ 40 * 318026 * 2
def baseEnd_318026 : Nat := 96770488075186936599959

theorem tailTrace_318026 : CollatzResearch.WordTrace tailWord_318026 prefixEnd_318026 96770488075186936599959 := by
  unfold tailWord_318026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899840286463397840427483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7732907430569060907806621 2899840286463397840427483)
  ·
    refine ⟨4349760429695096760641225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899840286463397840427483 4349760429695096760641225)
    ·
      refine ⟨3262320322271322570480919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4349760429695096760641225 3262320322271322570480919)
      ·
        refine ⟨4893480483406983855721379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262320322271322570480919 4893480483406983855721379)
        ·
          refine ⟨7340220725110475783582069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893480483406983855721379 7340220725110475783582069)
          ·
            refine ⟨688145692979107104710819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7340220725110475783582069 688145692979107104710819)
            ·
              refine ⟨1032218539468660657066229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688145692979107104710819 1032218539468660657066229)
              ·
                refine ⟨96770488075186936599959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1032218539468660657066229 96770488075186936599959)
                ·
                  rfl

theorem cell19_318026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_318026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318026 prefixEnd_318026 := by exact prefixLift 318026
  have htrace : WordTrace (prefixWord ++ tailWord_318026) baseStart_318026 baseEnd_318026 := by
    simpa [prefixWord, tailWord_318026, baseEnd_318026] using wordTrace_append hprefix tailTrace_318026
  have hstable : (prefixWord ++ tailWord_318026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318026).length < 2 ^ (prefixWord ++ tailWord_318026).sum := by decide
  have hdescent : baseEnd_318026 < baseStart_318026 := by decide
  rcases family_descends (prefixWord ++ tailWord_318026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318062 : List Nat := [4, 1, 2, 2, 2, 2, 2, 4]
def baseStart_318062 : Nat := 118140960795 + 318062 * 2 ^ 59
def prefixEnd_318062 : Nat := 4983230072969 + 3 ^ 40 * 318062 * 2
def baseEnd_318062 : Nat := 96781442329149519799861

theorem tailTrace_318062 : CollatzResearch.WordTrace tailWord_318062 prefixEnd_318062 96781442329149519799861 := by
  unfold tailWord_318062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1450084271715396188752555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7733782782482113006680293 1450084271715396188752555)
  ·
    refine ⟨2175126407573094283128833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1450084271715396188752555 2175126407573094283128833)
    ·
      refine ⟨1631344805679820712346625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2175126407573094283128833 1631344805679820712346625)
      ·
        refine ⟨1223508604259865534259969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1631344805679820712346625 1223508604259865534259969)
        ·
          refine ⟨917631453194899150694977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1223508604259865534259969 917631453194899150694977)
          ·
            refine ⟨688223589896174363021233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 917631453194899150694977 688223589896174363021233)
            ·
              refine ⟨516167692422130772265925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688223589896174363021233 516167692422130772265925)
              ·
                refine ⟨96781442329149519799861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 516167692422130772265925 96781442329149519799861)
                ·
                  rfl

theorem cell19_318062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_318062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318062 prefixEnd_318062 := by exact prefixLift 318062
  have htrace : WordTrace (prefixWord ++ tailWord_318062) baseStart_318062 baseEnd_318062 := by
    simpa [prefixWord, tailWord_318062, baseEnd_318062] using wordTrace_append hprefix tailTrace_318062
  have hstable : (prefixWord ++ tailWord_318062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318062).length < 2 ^ (prefixWord ++ tailWord_318062).sum := by decide
  have hdescent : baseEnd_318062 < baseStart_318062 := by decide
  rcases family_descends (prefixWord ++ tailWord_318062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318134 : List Nat := [5, 1, 3, 1, 2, 1, 3, 3]
def baseStart_318134 : Nat := 118140960795 + 318134 * 2 ^ 59
def prefixEnd_318134 : Nat := 4983230072969 + 3 ^ 40 * 318134 * 2
def baseEnd_318134 : Nat := 96803350837074686199665

theorem tailTrace_318134 : CollatzResearch.WordTrace tailWord_318134 prefixEnd_318134 96803350837074686199665 := by
  unfold tailWord_318134
  simp only [CollatzResearch.WordTrace]
  refine ⟨725206264341395362915091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7735533486308217204427637 725206264341395362915091)
  ·
    refine ⟨1087809396512093044372637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 725206264341395362915091 1087809396512093044372637)
    ·
      refine ⟨407928523692034891639739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1087809396512093044372637 407928523692034891639739)
      ·
        refine ⟨611892785538052337459609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407928523692034891639739 611892785538052337459609)
        ·
          refine ⟨458919589153539253094707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611892785538052337459609 458919589153539253094707)
          ·
            refine ⟨688379383730308879642061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458919589153539253094707 688379383730308879642061)
            ·
              refine ⟨258142268898865829865773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688379383730308879642061 258142268898865829865773)
              ·
                refine ⟨96803350837074686199665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258142268898865829865773 96803350837074686199665)
                ·
                  rfl

theorem cell19_318134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_318134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318134 prefixEnd_318134 := by exact prefixLift 318134
  have htrace : WordTrace (prefixWord ++ tailWord_318134) baseStart_318134 baseEnd_318134 := by
    simpa [prefixWord, tailWord_318134, baseEnd_318134] using wordTrace_append hprefix tailTrace_318134
  have hstable : (prefixWord ++ tailWord_318134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318134).length < 2 ^ (prefixWord ++ tailWord_318134).sum := by decide
  have hdescent : baseEnd_318134 < baseStart_318134 := by decide
  rcases family_descends (prefixWord ++ tailWord_318134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318161 : List Nat := [1, 2, 2, 1, 2, 3, 8]
def baseStart_318161 : Nat := 118140960795 + 318161 * 2 ^ 59
def prefixEnd_318161 : Nat := 4983230072969 + 3 ^ 40 * 318161 * 2
def baseEnd_318161 : Nat := 32270522175848874533197

theorem tailTrace_318161 : CollatzResearch.WordTrace tailWord_318161 prefixEnd_318161 32270522175848874533197 := by
  unfold tailWord_318161
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604285000364509417874337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7736190000243006278582891 11604285000364509417874337)
  ·
    refine ⟨8703213750273382063405753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11604285000364509417874337 8703213750273382063405753)
    ·
      refine ⟨6527410312705036547554315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8703213750273382063405753 6527410312705036547554315)
      ·
        refine ⟨9791115469057554821331473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527410312705036547554315 9791115469057554821331473)
        ·
          refine ⟨7343336601793166115998605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791115469057554821331473 7343336601793166115998605)
          ·
            refine ⟨2753751225672437293499477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7343336601793166115998605 2753751225672437293499477)
            ·
              refine ⟨32270522175848874533197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2753751225672437293499477 32270522175848874533197)
              ·
                rfl

theorem cell19_318161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 8].length) (baseStart_318161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318161 prefixEnd_318161 := by exact prefixLift 318161
  have htrace : WordTrace (prefixWord ++ tailWord_318161) baseStart_318161 baseEnd_318161 := by
    simpa [prefixWord, tailWord_318161, baseEnd_318161] using wordTrace_append hprefix tailTrace_318161
  have hstable : (prefixWord ++ tailWord_318161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318161).length < 2 ^ (prefixWord ++ tailWord_318161).sum := by decide
  have hdescent : baseEnd_318161 < baseStart_318161 := by decide
  rcases family_descends (prefixWord ++ tailWord_318161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318216 : List Nat := [2, 1, 3, 2, 2, 4, 5]
def baseStart_318216 : Nat := 118140960795 + 318216 * 2 ^ 59
def prefixEnd_318216 : Nat := 4983230072969 + 3 ^ 40 * 318216 * 2
def baseEnd_318216 : Nat := 32276100731107597459073

theorem tailTrace_318216 : CollatzResearch.WordTrace tailWord_318216 prefixEnd_318216 32276100731107597459073 := by
  unfold tailWord_318216
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803145507582626905563251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7737527343443502540751001 5803145507582626905563251)
  ·
    refine ⟨8704718261373940358344877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803145507582626905563251 8704718261373940358344877)
    ·
      refine ⟨3264269348015227634379329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8704718261373940358344877 3264269348015227634379329)
      ·
        refine ⟨2448202011011420725784497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3264269348015227634379329 2448202011011420725784497)
        ·
          refine ⟨1836151508258565544338373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448202011011420725784497 1836151508258565544338373)
          ·
            refine ⟨344278407798481039563445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1836151508258565544338373 344278407798481039563445)
            ·
              refine ⟨32276100731107597459073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344278407798481039563445 32276100731107597459073)
              ·
                rfl

theorem cell19_318216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_318216 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318216 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318216 prefixEnd_318216 := by exact prefixLift 318216
  have htrace : WordTrace (prefixWord ++ tailWord_318216) baseStart_318216 baseEnd_318216 := by
    simpa [prefixWord, tailWord_318216, baseEnd_318216] using wordTrace_append hprefix tailTrace_318216
  have hstable : (prefixWord ++ tailWord_318216).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318216).length < 2 ^ (prefixWord ++ tailWord_318216).sum := by decide
  have hdescent : baseEnd_318216 < baseStart_318216 := by decide
  rcases family_descends (prefixWord ++ tailWord_318216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318273 : List Nat := [1, 2, 5, 3, 8]
def baseStart_318273 : Nat := 118140960795 + 318273 * 2 ^ 59
def prefixEnd_318273 : Nat := 4983230072969 + 3 ^ 40 * 318273 * 2
def baseEnd_318273 : Nat := 3586875793657909226311

theorem tailTrace_318273 : CollatzResearch.WordTrace tailWord_318273 prefixEnd_318273 3586875793657909226311 := by
  unfold tailWord_318273
  simp only [CollatzResearch.WordTrace]
  refine ⟨11608369975958752545951473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7738913317305835030634315 11608369975958752545951473)
  ·
    refine ⟨8706277481969064409463605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11608369975958752545951473 8706277481969064409463605)
    ·
      refine ⟨816213513934599788387213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8706277481969064409463605 816213513934599788387213)
      ·
        refine ⟨306080067725474920645205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 816213513934599788387213 306080067725474920645205)
        ·
          refine ⟨3586875793657909226311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 306080067725474920645205 3586875793657909226311)
          ·
            rfl

theorem cell19_318273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 8].length) (baseStart_318273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318273 prefixEnd_318273 := by exact prefixLift 318273
  have htrace : WordTrace (prefixWord ++ tailWord_318273) baseStart_318273 baseEnd_318273 := by
    simpa [prefixWord, tailWord_318273, baseEnd_318273] using wordTrace_append hprefix tailTrace_318273
  have hstable : (prefixWord ++ tailWord_318273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318273).length < 2 ^ (prefixWord ++ tailWord_318273).sum := by decide
  have hdescent : baseEnd_318273 < baseStart_318273 := by decide
  rcases family_descends (prefixWord ++ tailWord_318273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318364 : List Nat := [2, 2, 3, 3, 2, 2, 2, 3]
def baseStart_318364 : Nat := 118140960795 + 318364 * 2 ^ 59
def prefixEnd_318364 : Nat := 4983230072969 + 3 ^ 40 * 318364 * 2
def baseEnd_318364 : Nat := 96873336348502301087927

theorem tailTrace_318364 : CollatzResearch.WordTrace tailWord_318364 prefixEnd_318364 96873336348502301087927 := by
  unfold tailWord_318364
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805844509314537543757073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7741126012419383391676097 5805844509314537543757073)
  ·
    refine ⟨4354383381985903157817805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5805844509314537543757073 4354383381985903157817805)
    ·
      refine ⟨1632893768244713684181677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4354383381985903157817805 1632893768244713684181677)
      ·
        refine ⟨612335163091767631568129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1632893768244713684181677 612335163091767631568129)
        ·
          refine ⟨459251372318825723676097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612335163091767631568129 459251372318825723676097)
          ·
            refine ⟨344438529239119292757073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459251372318825723676097 344438529239119292757073)
            ·
              refine ⟨258328896929339469567805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344438529239119292757073 258328896929339469567805)
              ·
                refine ⟨96873336348502301087927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258328896929339469567805 96873336348502301087927)
                ·
                  rfl

theorem cell19_318364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 2, 3].length) (baseStart_318364 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318364 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318364 prefixEnd_318364 := by exact prefixLift 318364
  have htrace : WordTrace (prefixWord ++ tailWord_318364) baseStart_318364 baseEnd_318364 := by
    simpa [prefixWord, tailWord_318364, baseEnd_318364] using wordTrace_append hprefix tailTrace_318364
  have hstable : (prefixWord ++ tailWord_318364).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318364).length < 2 ^ (prefixWord ++ tailWord_318364).sum := by decide
  have hdescent : baseEnd_318364 < baseStart_318364 := by decide
  rcases family_descends (prefixWord ++ tailWord_318364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318368 : List Nat := [2, 1, 1, 4, 1, 1, 6, 3]
def baseStart_318368 : Nat := 118140960795 + 318368 * 2 ^ 59
def prefixEnd_318368 : Nat := 4983230072969 + 3 ^ 40 * 318368 * 2
def baseEnd_318368 : Nat := 96874553487831476999027

theorem tailTrace_318368 : CollatzResearch.WordTrace tailWord_318368 prefixEnd_318368 96874553487831476999027 := by
  unfold tailWord_318368
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805917455307291885329879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7741223273743055847106505 5805917455307291885329879)
  ·
    refine ⟨8708876182960937827994819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805917455307291885329879 8708876182960937827994819)
    ·
      refine ⟨13063314274441406741992229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8708876182960937827994819 13063314274441406741992229)
      ·
        refine ⟨2449371426457763764123543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13063314274441406741992229 2449371426457763764123543)
        ·
          refine ⟨3674057139686645646185315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449371426457763764123543 3674057139686645646185315)
          ·
            refine ⟨5511085709529968469277973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674057139686645646185315 5511085709529968469277973)
            ·
              refine ⟨258332142634217271997405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5511085709529968469277973 258332142634217271997405)
              ·
                refine ⟨96874553487831476999027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258332142634217271997405 96874553487831476999027)
                ·
                  rfl

theorem cell19_318368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_318368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318368 prefixEnd_318368 := by exact prefixLift 318368
  have htrace : WordTrace (prefixWord ++ tailWord_318368) baseStart_318368 baseEnd_318368 := by
    simpa [prefixWord, tailWord_318368, baseEnd_318368] using wordTrace_append hprefix tailTrace_318368
  have hstable : (prefixWord ++ tailWord_318368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318368).length < 2 ^ (prefixWord ++ tailWord_318368).sum := by decide
  have hdescent : baseEnd_318368 < baseStart_318368 := by decide
  rcases family_descends (prefixWord ++ tailWord_318368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318385 : List Nat := [1, 2, 2, 4, 4, 1, 5]
def baseStart_318385 : Nat := 118140960795 + 318385 * 2 ^ 59
def prefixEnd_318385 : Nat := 4983230072969 + 3 ^ 40 * 318385 * 2
def baseEnd_318385 : Nat := 32293242109993491540401

theorem tailTrace_318385 : CollatzResearch.WordTrace tailWord_318385 prefixEnd_318385 32293242109993491540401 := by
  unfold tailWord_318385
  simp only [CollatzResearch.WordTrace]
  refine ⟨11612454951552995674028609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7741636634368663782685739 11612454951552995674028609)
  ·
    refine ⟨8709341213664746755521457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11612454951552995674028609 8709341213664746755521457)
    ·
      refine ⟨6532005910248560066641093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8709341213664746755521457 6532005910248560066641093)
      ·
        refine ⟨1224751108171605012495205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6532005910248560066641093 1224751108171605012495205)
        ·
          refine ⟨229640832782175939842851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1224751108171605012495205 229640832782175939842851)
          ·
            refine ⟨344461249173263909764277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229640832782175939842851 344461249173263909764277)
            ·
              refine ⟨32293242109993491540401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344461249173263909764277 32293242109993491540401)
              ·
                rfl

theorem cell19_318385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_318385 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318385 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318385 prefixEnd_318385 := by exact prefixLift 318385
  have htrace : WordTrace (prefixWord ++ tailWord_318385) baseStart_318385 baseEnd_318385 := by
    simpa [prefixWord, tailWord_318385, baseEnd_318385] using wordTrace_append hprefix tailTrace_318385
  have hstable : (prefixWord ++ tailWord_318385).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318385).length < 2 ^ (prefixWord ++ tailWord_318385).sum := by decide
  have hdescent : baseEnd_318385 < baseStart_318385 := by decide
  rcases family_descends (prefixWord ++ tailWord_318385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318446 : List Nat := [4, 1, 2, 1, 11]
def baseStart_318446 : Nat := 118140960795 + 318446 * 2 ^ 59
def prefixEnd_318446 : Nat := 4983230072969 + 3 ^ 40 * 318446 * 2
def baseEnd_318446 : Nat := 3588825470546311380203

theorem tailTrace_318446 : CollatzResearch.WordTrace tailWord_318446 prefixEnd_318446 3588825470546311380203 := by
  unfold tailWord_318446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451834975541500386499899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7743119869554668727999461 1451834975541500386499899)
  ·
    refine ⟨2177752463312250579749849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1451834975541500386499899 2177752463312250579749849)
    ·
      refine ⟨1633314347484187934812387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2177752463312250579749849 1633314347484187934812387)
      ·
        refine ⟨2449971521226281902218581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1633314347484187934812387 2449971521226281902218581)
        ·
          refine ⟨3588825470546311380203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2449971521226281902218581 3588825470546311380203)
          ·
            rfl

theorem cell19_318446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 11].length) (baseStart_318446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318446 prefixEnd_318446 := by exact prefixLift 318446
  have htrace : WordTrace (prefixWord ++ tailWord_318446) baseStart_318446 baseEnd_318446 := by
    simpa [prefixWord, tailWord_318446, baseEnd_318446] using wordTrace_append hprefix tailTrace_318446
  have hstable : (prefixWord ++ tailWord_318446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318446).length < 2 ^ (prefixWord ++ tailWord_318446).sum := by decide
  have hdescent : baseEnd_318446 < baseStart_318446 := by decide
  rcases family_descends (prefixWord ++ tailWord_318446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318674 : List Nat := [3, 2, 2, 2, 1, 1, 8]
def baseStart_318674 : Nat := 118140960795 + 318674 * 2 ^ 59
def prefixEnd_318674 : Nat := 4983230072969 + 3 ^ 40 * 318674 * 2
def baseEnd_318674 : Nat := 32322554882171144732731

theorem tailTrace_318674 : CollatzResearch.WordTrace tailWord_318674 prefixEnd_318674 32322554882171144732731 := by
  unfold tailWord_318674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905748911876499507824769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7748663765003998687532717 2905748911876499507824769)
  ·
    refine ⟨2179311683907374630868577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2905748911876499507824769 2179311683907374630868577)
    ·
      refine ⟨1634483762930530973151433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2179311683907374630868577 1634483762930530973151433)
      ·
        refine ⟨1225862822197898229863575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1634483762930530973151433 1225862822197898229863575)
        ·
          refine ⟨1838794233296847344795363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225862822197898229863575 1838794233296847344795363)
          ·
            refine ⟨2758191349945271017193045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838794233296847344795363 2758191349945271017193045)
            ·
              refine ⟨32322554882171144732731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2758191349945271017193045 32322554882171144732731)
              ·
                rfl

theorem cell19_318674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 8].length) (baseStart_318674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318674 prefixEnd_318674 := by exact prefixLift 318674
  have htrace : WordTrace (prefixWord ++ tailWord_318674) baseStart_318674 baseEnd_318674 := by
    simpa [prefixWord, tailWord_318674, baseEnd_318674] using wordTrace_append hprefix tailTrace_318674
  have hstable : (prefixWord ++ tailWord_318674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318674).length < 2 ^ (prefixWord ++ tailWord_318674).sum := by decide
  have hdescent : baseEnd_318674 < baseStart_318674 := by decide
  rcases family_descends (prefixWord ++ tailWord_318674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318706 : List Nat := [3, 2, 1, 3, 4, 1, 2, 3]
def baseStart_318706 : Nat := 118140960795 + 318706 * 2 ^ 59
def prefixEnd_318706 : Nat := 4983230072969 + 3 ^ 40 * 318706 * 2
def baseEnd_318706 : Nat := 96977401761146841486995

theorem tailTrace_318706 : CollatzResearch.WordTrace tailWord_318706 prefixEnd_318706 96977401761146841486995 := by
  unfold tailWord_318706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2906040695847516874115993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7749441855593378330975981 2906040695847516874115993)
  ·
    refine ⟨2179530521885637655586995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2906040695847516874115993 2179530521885637655586995)
    ·
      refine ⟨3269295782828456483380493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2179530521885637655586995 3269295782828456483380493)
      ·
        refine ⟨1225985918560671181267685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3269295782828456483380493 1225985918560671181267685)
        ·
          refine ⟨229872359730125846487691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1225985918560671181267685 229872359730125846487691)
          ·
            refine ⟨344808539595188769731537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229872359730125846487691 344808539595188769731537)
            ·
              refine ⟨258606404696391577298653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344808539595188769731537 258606404696391577298653)
              ·
                refine ⟨96977401761146841486995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258606404696391577298653 96977401761146841486995)
                ·
                  rfl

theorem cell19_318706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_318706 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318706 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318706 prefixEnd_318706 := by exact prefixLift 318706
  have htrace : WordTrace (prefixWord ++ tailWord_318706) baseStart_318706 baseEnd_318706 := by
    simpa [prefixWord, tailWord_318706, baseEnd_318706] using wordTrace_append hprefix tailTrace_318706
  have hstable : (prefixWord ++ tailWord_318706).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318706).length < 2 ^ (prefixWord ++ tailWord_318706).sum := by decide
  have hdescent : baseEnd_318706 < baseStart_318706 := by decide
  rcases family_descends (prefixWord ++ tailWord_318706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318731 : List Nat := [1, 1, 1, 1, 5, 5, 5]
def baseStart_318731 : Nat := 118140960795 + 318731 * 2 ^ 59
def prefixEnd_318731 : Nat := 4983230072969 + 3 ^ 40 * 318731 * 2
def baseEnd_318731 : Nat := 32328336293984730310457

theorem tailTrace_318731 : CollatzResearch.WordTrace tailWord_318731 prefixEnd_318731 32328336293984730310457 := by
  unfold tailWord_318731
  simp only [CollatzResearch.WordTrace]
  refine ⟨11625074608299496766124047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7750049738866331177416031 11625074608299496766124047)
  ·
    refine ⟨17437611912449245149186071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11625074608299496766124047 17437611912449245149186071)
    ·
      refine ⟨26156417868673867723779107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17437611912449245149186071 26156417868673867723779107)
      ·
        refine ⟨39234626803010801585668661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26156417868673867723779107 39234626803010801585668661)
        ·
          refine ⟨3678246262782262648656437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39234626803010801585668661 3678246262782262648656437)
          ·
            refine ⟨344835587135837123311541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3678246262782262648656437 344835587135837123311541)
            ·
              refine ⟨32328336293984730310457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 344835587135837123311541 32328336293984730310457)
              ·
                rfl

theorem cell19_318731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_318731 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318731 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318731 prefixEnd_318731 := by exact prefixLift 318731
  have htrace : WordTrace (prefixWord ++ tailWord_318731) baseStart_318731 baseEnd_318731 := by
    simpa [prefixWord, tailWord_318731, baseEnd_318731] using wordTrace_append hprefix tailTrace_318731
  have hstable : (prefixWord ++ tailWord_318731).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318731).length < 2 ^ (prefixWord ++ tailWord_318731).sum := by decide
  have hdescent : baseEnd_318731 < baseStart_318731 := by decide
  rcases family_descends (prefixWord ++ tailWord_318731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318769 : List Nat := [1, 2, 2, 3, 3, 1, 2, 5]
def baseStart_318769 : Nat := 118140960795 + 318769 * 2 ^ 59
def prefixEnd_318769 : Nat := 4983230072969 + 3 ^ 40 * 318769 * 2
def baseEnd_318769 : Nat := 96996571705581362086823

theorem tailTrace_318769 : CollatzResearch.WordTrace tailWord_318769 prefixEnd_318769 96996571705581362086823 := by
  unfold tailWord_318769
  simp only [CollatzResearch.WordTrace]
  refine ⟨11626460582161829256007361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7750973721441219504004907 11626460582161829256007361)
  ·
    refine ⟨8719845436621371942005521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11626460582161829256007361 8719845436621371942005521)
    ·
      refine ⟨6539884077466028956504141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8719845436621371942005521 6539884077466028956504141)
      ·
        refine ⟨2452456529049760858689053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6539884077466028956504141 2452456529049760858689053)
        ·
          refine ⟨919671198393660322008395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2452456529049760858689053 919671198393660322008395)
          ·
            refine ⟨1379506797590490483012593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919671198393660322008395 1379506797590490483012593)
            ·
              refine ⟨1034630098192867862259445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1379506797590490483012593 1034630098192867862259445)
              ·
                refine ⟨96996571705581362086823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1034630098192867862259445 96996571705581362086823)
                ·
                  rfl

theorem cell19_318769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_318769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318769 prefixEnd_318769 := by exact prefixLift 318769
  have htrace : WordTrace (prefixWord ++ tailWord_318769) baseStart_318769 baseEnd_318769 := by
    simpa [prefixWord, tailWord_318769, baseEnd_318769] using wordTrace_append hprefix tailTrace_318769
  have hstable : (prefixWord ++ tailWord_318769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318769).length < 2 ^ (prefixWord ++ tailWord_318769).sum := by decide
  have hdescent : baseEnd_318769 < baseStart_318769 := by decide
  rcases family_descends (prefixWord ++ tailWord_318769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318805 : List Nat := [1, 3, 2, 2, 3, 3, 1, 4]
def baseStart_318805 : Nat := 118140960795 + 318805 * 2 ^ 59
def prefixEnd_318805 : Nat := 4983230072969 + 3 ^ 40 * 318805 * 2
def baseEnd_318805 : Nat := 97007525959543945286725

theorem tailTrace_318805 : CollatzResearch.WordTrace tailWord_318805 prefixEnd_318805 97007525959543945286725 := by
  unfold tailWord_318805
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627773610031407404317869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7751849073354271602878579 11627773610031407404317869)
  ·
    refine ⟨4360415103761777776619201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11627773610031407404317869 4360415103761777776619201)
    ·
      refine ⟨3270311327821333332464401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4360415103761777776619201 3270311327821333332464401)
      ·
        refine ⟨2452733495865999999348301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3270311327821333332464401 2452733495865999999348301)
        ·
          refine ⟨919775060949749999755613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2452733495865999999348301 919775060949749999755613)
          ·
            refine ⟨344915647856156249908355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 919775060949749999755613 344915647856156249908355)
            ·
              refine ⟨517373471784234374862533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344915647856156249908355 517373471784234374862533)
              ·
                refine ⟨97007525959543945286725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517373471784234374862533 97007525959543945286725)
                ·
                  rfl

theorem cell19_318805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 4].length) (baseStart_318805 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318805 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318805 prefixEnd_318805 := by exact prefixLift 318805
  have htrace : WordTrace (prefixWord ++ tailWord_318805) baseStart_318805 baseEnd_318805 := by
    simpa [prefixWord, tailWord_318805, baseEnd_318805] using wordTrace_append hprefix tailTrace_318805
  have hstable : (prefixWord ++ tailWord_318805).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318805).length < 2 ^ (prefixWord ++ tailWord_318805).sum := by decide
  have hdescent : baseEnd_318805 < baseStart_318805 := by decide
  rcases family_descends (prefixWord ++ tailWord_318805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318807 : List Nat := [1, 1, 3, 2, 3, 2, 3, 4]
def baseStart_318807 : Nat := 118140960795 + 318807 * 2 ^ 59
def prefixEnd_318807 : Nat := 4983230072969 + 3 ^ 40 * 318807 * 2
def baseEnd_318807 : Nat := 97008134529208533242275

theorem tailTrace_318807 : CollatzResearch.WordTrace tailWord_318807 prefixEnd_318807 97008134529208533242275 := by
  unfold tailWord_318807
  simp only [CollatzResearch.WordTrace]
  refine ⟨11627846556024161745890675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7751897704016107830593783 11627846556024161745890675)
  ·
    refine ⟨17441769834036242618836013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11627846556024161745890675 17441769834036242618836013)
    ·
      refine ⟨6540663687763590982063505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17441769834036242618836013 6540663687763590982063505)
      ·
        refine ⟨4905497765822693236547629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6540663687763590982063505 4905497765822693236547629)
        ·
          refine ⟨1839561662183509963705361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4905497765822693236547629 1839561662183509963705361)
          ·
            refine ⟨1379671246637632472779021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1839561662183509963705361 1379671246637632472779021)
            ·
              refine ⟨517376717489112177292133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1379671246637632472779021 517376717489112177292133)
              ·
                refine ⟨97008134529208533242275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517376717489112177292133 97008134529208533242275)
                ·
                  rfl

theorem cell19_318807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_318807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318807 prefixEnd_318807 := by exact prefixLift 318807
  have htrace : WordTrace (prefixWord ++ tailWord_318807) baseStart_318807 baseEnd_318807 := by
    simpa [prefixWord, tailWord_318807, baseEnd_318807] using wordTrace_append hprefix tailTrace_318807
  have hstable : (prefixWord ++ tailWord_318807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318807).length < 2 ^ (prefixWord ++ tailWord_318807).sum := by decide
  have hdescent : baseEnd_318807 < baseStart_318807 := by decide
  rcases family_descends (prefixWord ++ tailWord_318807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318904 : List Nat := [2, 1, 2, 1, 2, 2, 9]
def baseStart_318904 : Nat := 118140960795 + 318904 * 2 ^ 59
def prefixEnd_318904 : Nat := 4983230072969 + 3 ^ 40 * 318904 * 2
def baseEnd_318904 : Nat := 32345883385980349695485

theorem tailTrace_318904 : CollatzResearch.WordTrace tailWord_318904 prefixEnd_318904 32345883385980349695485 := by
  unfold tailWord_318904
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815692218336373656085883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7754256291115164874781177 5815692218336373656085883)
  ·
    refine ⟨8723538327504560484128825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815692218336373656085883 8723538327504560484128825)
    ·
      refine ⟨6542653745628420363096619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8723538327504560484128825 6542653745628420363096619)
      ·
        refine ⟨9813980618442630544644929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6542653745628420363096619 9813980618442630544644929)
        ·
          refine ⟨7360485463831972908483697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9813980618442630544644929 7360485463831972908483697)
          ·
            refine ⟨5520364097873979681362773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7360485463831972908483697 5520364097873979681362773)
            ·
              refine ⟨32345883385980349695485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5520364097873979681362773 32345883385980349695485)
              ·
                rfl

theorem cell19_318904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_318904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318904 prefixEnd_318904 := by exact prefixLift 318904
  have htrace : WordTrace (prefixWord ++ tailWord_318904) baseStart_318904 baseEnd_318904 := by
    simpa [prefixWord, tailWord_318904, baseEnd_318904] using wordTrace_append hprefix tailTrace_318904
  have hstable : (prefixWord ++ tailWord_318904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318904).length < 2 ^ (prefixWord ++ tailWord_318904).sum := by decide
  have hdescent : baseEnd_318904 < baseStart_318904 := by decide
  rcases family_descends (prefixWord ++ tailWord_318904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318923 : List Nat := [1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_318923 : Nat := 118140960795 + 318923 * 2 ^ 59
def prefixEnd_318923 : Nat := 4983230072969 + 3 ^ 40 * 318923 * 2
def baseEnd_318923 : Nat := 97043431569754634664181

theorem tailTrace_318923 : CollatzResearch.WordTrace tailWord_318923 prefixEnd_318923 97043431569754634664181 := by
  unfold tailWord_318923
  simp only [CollatzResearch.WordTrace]
  refine ⟨11632077423603913557113423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7754718282402609038075615 11632077423603913557113423)
  ·
    refine ⟨17448116135405870335670135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11632077423603913557113423 17448116135405870335670135)
    ·
      refine ⟨26172174203108805503505203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17448116135405870335670135 26172174203108805503505203)
      ·
        refine ⟨39258261304663208255257805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26172174203108805503505203 39258261304663208255257805)
        ·
          refine ⟨14721847989248703095721677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39258261304663208255257805 14721847989248703095721677)
          ·
            refine ⟨5520692995968263660895629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14721847989248703095721677 5520692995968263660895629)
            ·
              refine ⟨2070259873488098872835861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5520692995968263660895629 2070259873488098872835861)
              ·
                refine ⟨97043431569754634664181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070259873488098872835861 97043431569754634664181)
                ·
                  rfl

theorem cell19_318923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_318923 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318923 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318923 prefixEnd_318923 := by exact prefixLift 318923
  have htrace : WordTrace (prefixWord ++ tailWord_318923) baseStart_318923 baseEnd_318923 := by
    simpa [prefixWord, tailWord_318923, baseEnd_318923] using wordTrace_append hprefix tailTrace_318923
  have hstable : (prefixWord ++ tailWord_318923).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318923).length < 2 ^ (prefixWord ++ tailWord_318923).sum := by decide
  have hdescent : baseEnd_318923 < baseStart_318923 := by decide
  rcases family_descends (prefixWord ++ tailWord_318923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318957 : List Nat := [1, 5, 1, 3, 3, 6]
def baseStart_318957 : Nat := 118140960795 + 318957 * 2 ^ 59
def prefixEnd_318957 : Nat := 4983230072969 + 3 ^ 40 * 318957 * 2
def baseEnd_318957 : Nat := 10783753028228069989837

theorem tailTrace_318957 : CollatzResearch.WordTrace tailWord_318957 prefixEnd_318957 10783753028228069989837 := by
  unfold tailWord_318957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633317505480737363851125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7755545003653824909234083 11633317505480737363851125)
  ·
    refine ⟨1090623516138819127861043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11633317505480737363851125 1090623516138819127861043)
    ·
      refine ⟨1635935274208228691791565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1090623516138819127861043 1635935274208228691791565)
      ·
        refine ⟨613475727828085759421837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1635935274208228691791565 613475727828085759421837)
        ·
          refine ⟨230053397935532159783189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 613475727828085759421837 230053397935532159783189)
          ·
            refine ⟨10783753028228069989837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 230053397935532159783189 10783753028228069989837)
            ·
              rfl

theorem cell19_318957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_318957 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318957 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318957 prefixEnd_318957 := by exact prefixLift 318957
  have htrace : WordTrace (prefixWord ++ tailWord_318957) baseStart_318957 baseEnd_318957 := by
    simpa [prefixWord, tailWord_318957, baseEnd_318957] using wordTrace_append hprefix tailTrace_318957
  have hstable : (prefixWord ++ tailWord_318957).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318957).length < 2 ^ (prefixWord ++ tailWord_318957).sum := by decide
  have hdescent : baseEnd_318957 < baseStart_318957 := by decide
  rcases family_descends (prefixWord ++ tailWord_318957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_318961 : List Nat := [1, 2, 2, 2, 3, 9]
def baseStart_318961 : Nat := 118140960795 + 318961 * 2 ^ 59
def prefixEnd_318961 : Nat := 4983230072969 + 3 ^ 40 * 318961 * 2
def baseEnd_318961 : Nat := 10783888265931311757737

theorem tailTrace_318961 : CollatzResearch.WordTrace tailWord_318961 prefixEnd_318961 10783888265931311757737 := by
  unfold tailWord_318961
  simp only [CollatzResearch.WordTrace]
  refine ⟨11633463397466246046996737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7755642264977497364664491 11633463397466246046996737)
  ·
    refine ⟨8725097548099684535247553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11633463397466246046996737 8725097548099684535247553)
    ·
      refine ⟨6543823161074763401435665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8725097548099684535247553 6543823161074763401435665)
      ·
        refine ⟨4907867370806072551076749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6543823161074763401435665 4907867370806072551076749)
        ·
          refine ⟨1840450264052277206653781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4907867370806072551076749 1840450264052277206653781)
          ·
            refine ⟨10783888265931311757737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1840450264052277206653781 10783888265931311757737)
            ·
              rfl

theorem cell19_318961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 9].length) (baseStart_318961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_318961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_318961 prefixEnd_318961 := by exact prefixLift 318961
  have htrace : WordTrace (prefixWord ++ tailWord_318961) baseStart_318961 baseEnd_318961 := by
    simpa [prefixWord, tailWord_318961, baseEnd_318961] using wordTrace_append hprefix tailTrace_318961
  have hstable : (prefixWord ++ tailWord_318961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_318961).length < 2 ^ (prefixWord ++ tailWord_318961).sum := by decide
  have hdescent : baseEnd_318961 < baseStart_318961 := by decide
  rcases family_descends (prefixWord ++ tailWord_318961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319046 : List Nat := [6, 1, 1, 1, 4, 1, 2, 3]
def baseStart_319046 : Nat := 118140960795 + 319046 * 2 ^ 59
def prefixEnd_319046 : Nat := 4983230072969 + 3 ^ 40 * 319046 * 2
def baseEnd_319046 : Nat := 97080858604126793930513

theorem tailTrace_319046 : CollatzResearch.WordTrace tailWord_319046 prefixEnd_319046 97080858604126793930513 := by
  unfold tailWord_319046
  simp only [CollatzResearch.WordTrace]
  refine ⟨363642612567447048870031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7757709068105537042560661 363642612567447048870031)
  ·
    refine ⟨545463918851170573305047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 363642612567447048870031 545463918851170573305047)
    ·
      refine ⟨818195878276755859957571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545463918851170573305047 818195878276755859957571)
      ·
        refine ⟨1227293817415133789936357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818195878276755859957571 1227293817415133789936357)
        ·
          refine ⟨230117590765337585613067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1227293817415133789936357 230117590765337585613067)
          ·
            refine ⟨345176386148006378419601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230117590765337585613067 345176386148006378419601)
            ·
              refine ⟨258882289611004783814701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345176386148006378419601 258882289611004783814701)
              ·
                refine ⟨97080858604126793930513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258882289611004783814701 97080858604126793930513)
                ·
                  rfl

theorem cell19_319046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_319046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319046 prefixEnd_319046 := by exact prefixLift 319046
  have htrace : WordTrace (prefixWord ++ tailWord_319046) baseStart_319046 baseEnd_319046 := by
    simpa [prefixWord, tailWord_319046, baseEnd_319046] using wordTrace_append hprefix tailTrace_319046
  have hstable : (prefixWord ++ tailWord_319046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319046).length < 2 ^ (prefixWord ++ tailWord_319046).sum := by decide
  have hdescent : baseEnd_319046 < baseStart_319046 := by decide
  rcases family_descends (prefixWord ++ tailWord_319046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319052 : List Nat := [2, 2, 1, 3, 1, 5, 2, 3]
def baseStart_319052 : Nat := 118140960795 + 319052 * 2 ^ 59
def prefixEnd_319052 : Nat := 4983230072969 + 3 ^ 40 * 319052 * 2
def baseEnd_319052 : Nat := 97082684313120557797163

theorem tailTrace_319052 : CollatzResearch.WordTrace tailWord_319052 prefixEnd_319052 97082684313120557797163 := by
  unfold tailWord_319052
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818391220068284294279705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7757854960091045725706273 5818391220068284294279705)
  ·
    refine ⟨4363793415051213220709779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5818391220068284294279705 4363793415051213220709779)
    ·
      refine ⟨6545690122576819831064669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4363793415051213220709779 6545690122576819831064669)
      ·
        refine ⟨2454633795966307436649251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6545690122576819831064669 2454633795966307436649251)
        ·
          refine ⟨3681950693949461154973877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454633795966307436649251 3681950693949461154973877)
          ·
            refine ⟨345182877557761983278801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3681950693949461154973877 345182877557761983278801)
            ·
              refine ⟨258887158168321487459101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345182877557761983278801 258887158168321487459101)
              ·
                refine ⟨97082684313120557797163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258887158168321487459101 97082684313120557797163)
                ·
                  rfl

theorem cell19_319052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_319052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319052 prefixEnd_319052 := by exact prefixLift 319052
  have htrace : WordTrace (prefixWord ++ tailWord_319052) baseStart_319052 baseEnd_319052 := by
    simpa [prefixWord, tailWord_319052, baseEnd_319052] using wordTrace_append hprefix tailTrace_319052
  have hstable : (prefixWord ++ tailWord_319052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319052).length < 2 ^ (prefixWord ++ tailWord_319052).sum := by decide
  have hdescent : baseEnd_319052 < baseStart_319052 := by decide
  rcases family_descends (prefixWord ++ tailWord_319052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319056 : List Nat := [2, 1, 1, 1, 1, 3, 5, 5]
def baseStart_319056 : Nat := 118140960795 + 319056 * 2 ^ 59
def prefixEnd_319056 : Nat := 4983230072969 + 3 ^ 40 * 319056 * 2
def baseEnd_319056 : Nat := 97083901452449733708263

theorem tailTrace_319056 : CollatzResearch.WordTrace tailWord_319056 prefixEnd_319056 97083901452449733708263 := by
  unfold tailWord_319056
  simp only [CollatzResearch.WordTrace]
  refine ⟨5818464166061038635852511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7757952221414718181136681 5818464166061038635852511)
  ·
    refine ⟨8727696249091557953778767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5818464166061038635852511 8727696249091557953778767)
    ·
      refine ⟨13091544373637336930668151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8727696249091557953778767 13091544373637336930668151)
      ·
        refine ⟨19637316560456005396002227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13091544373637336930668151 19637316560456005396002227)
        ·
          refine ⟨29455974840684008094003341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19637316560456005396002227 29455974840684008094003341)
          ·
            refine ⟨11045990565256503035251253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29455974840684008094003341 11045990565256503035251253)
            ·
              refine ⟨1035561615492797159554805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11045990565256503035251253 1035561615492797159554805)
              ·
                refine ⟨97083901452449733708263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1035561615492797159554805 97083901452449733708263)
                ·
                  rfl

theorem cell19_319056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_319056 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319056 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319056 prefixEnd_319056 := by exact prefixLift 319056
  have htrace : WordTrace (prefixWord ++ tailWord_319056) baseStart_319056 baseEnd_319056 := by
    simpa [prefixWord, tailWord_319056, baseEnd_319056] using wordTrace_append hprefix tailTrace_319056
  have hstable : (prefixWord ++ tailWord_319056).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319056).length < 2 ^ (prefixWord ++ tailWord_319056).sum := by decide
  have hdescent : baseEnd_319056 < baseStart_319056 := by decide
  rcases family_descends (prefixWord ++ tailWord_319056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319069 : List Nat := [1, 4, 4, 2, 1, 2, 5]
def baseStart_319069 : Nat := 118140960795 + 319069 * 2 ^ 59
def prefixEnd_319069 : Nat := 4983230072969 + 3 ^ 40 * 319069 * 2
def baseEnd_319069 : Nat := 32362619051756518473113

theorem tailTrace_319069 : CollatzResearch.WordTrace tailWord_319069 prefixEnd_319069 32362619051756518473113 := by
  unfold tailWord_319069
  simp only [CollatzResearch.WordTrace]
  refine ⟨11637402481074980491928261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7758268320716653661285507 11637402481074980491928261)
  ·
    refine ⟨2182012965201558842236549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11637402481074980491928261 2182012965201558842236549)
    ·
      refine ⟨409127430975292282919353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2182012965201558842236549 409127430975292282919353)
      ·
        refine ⟨306845573231469212189515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409127430975292282919353 306845573231469212189515)
        ·
          refine ⟨460268359847203818284273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306845573231469212189515 460268359847203818284273)
          ·
            refine ⟨345201269885402863713205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460268359847203818284273 345201269885402863713205)
            ·
              refine ⟨32362619051756518473113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 345201269885402863713205 32362619051756518473113)
              ·
                rfl

theorem cell19_319069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 5].length) (baseStart_319069 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319069 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319069 prefixEnd_319069 := by exact prefixLift 319069
  have htrace : WordTrace (prefixWord ++ tailWord_319069) baseStart_319069 baseEnd_319069 := by
    simpa [prefixWord, tailWord_319069, baseEnd_319069] using wordTrace_append hprefix tailTrace_319069
  have hstable : (prefixWord ++ tailWord_319069).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319069).length < 2 ^ (prefixWord ++ tailWord_319069).sum := by decide
  have hdescent : baseEnd_319069 < baseStart_319069 := by decide
  rcases family_descends (prefixWord ++ tailWord_319069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319075 : List Nat := [1, 1, 1, 5, 1, 3, 7]
def baseStart_319075 : Nat := 118140960795 + 319075 * 2 ^ 59
def prefixEnd_319075 : Nat := 4983230072969 + 3 ^ 40 * 319075 * 2
def baseEnd_319075 : Nat := 32363227621421106428663

theorem tailTrace_319075 : CollatzResearch.WordTrace tailWord_319075 prefixEnd_319075 32363227621421106428663 := by
  unfold tailWord_319075
  simp only [CollatzResearch.WordTrace]
  refine ⟨11637621319053243516646679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7758414212702162344431119 11637621319053243516646679)
  ·
    refine ⟨17456431978579865274970019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11637621319053243516646679 17456431978579865274970019)
    ·
      refine ⟨26184647967869797912455029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17456431978579865274970019 26184647967869797912455029)
      ·
        refine ⟨2454810746987793554292659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26184647967869797912455029 2454810746987793554292659)
        ·
          refine ⟨3682216120481690331438989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2454810746987793554292659 3682216120481690331438989)
          ·
            refine ⟨1380831045180633874289621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3682216120481690331438989 1380831045180633874289621)
            ·
              refine ⟨32363227621421106428663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1380831045180633874289621 32363227621421106428663)
              ·
                rfl

theorem cell19_319075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_319075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319075 prefixEnd_319075 := by exact prefixLift 319075
  have htrace : WordTrace (prefixWord ++ tailWord_319075) baseStart_319075 baseEnd_319075 := by
    simpa [prefixWord, tailWord_319075, baseEnd_319075] using wordTrace_append hprefix tailTrace_319075
  have hstable : (prefixWord ++ tailWord_319075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319075).length < 2 ^ (prefixWord ++ tailWord_319075).sum := by decide
  have hdescent : baseEnd_319075 < baseStart_319075 := by decide
  rcases family_descends (prefixWord ++ tailWord_319075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319113 : List Nat := [1, 2, 1, 1, 4, 1, 4, 5]
def baseStart_319113 : Nat := 118140960795 + 319113 * 2 ^ 59
def prefixEnd_319113 : Nat := 4983230072969 + 3 ^ 40 * 319113 * 2
def baseEnd_319113 : Nat := 97101245687890490441441

theorem tailTrace_319113 : CollatzResearch.WordTrace tailWord_319113 prefixEnd_319113 97101245687890490441441 := by
  unfold tailWord_319113
  simp only [CollatzResearch.WordTrace]
  refine ⟨11639007292915576006529993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7759338195277050671019995 11639007292915576006529993)
  ·
    refine ⟨8729255469686682004897495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11639007292915576006529993 8729255469686682004897495)
    ·
      refine ⟨13093883204530023007346243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8729255469686682004897495 13093883204530023007346243)
      ·
        refine ⟨19640824806795034511019365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13093883204530023007346243 19640824806795034511019365)
        ·
          refine ⟨3682654651274068970816131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19640824806795034511019365 3682654651274068970816131)
          ·
            refine ⟨5523981976911103456224197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3682654651274068970816131 5523981976911103456224197)
            ·
              refine ⟨1035746620670831898042037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5523981976911103456224197 1035746620670831898042037)
              ·
                refine ⟨97101245687890490441441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1035746620670831898042037 97101245687890490441441)
                ·
                  rfl

theorem cell19_319113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_319113 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319113 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319113 prefixEnd_319113 := by exact prefixLift 319113
  have htrace : WordTrace (prefixWord ++ tailWord_319113) baseStart_319113 baseEnd_319113 := by
    simpa [prefixWord, tailWord_319113, baseEnd_319113] using wordTrace_append hprefix tailTrace_319113
  have hstable : (prefixWord ++ tailWord_319113).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319113).length < 2 ^ (prefixWord ++ tailWord_319113).sum := by decide
  have hdescent : baseEnd_319113 < baseStart_319113 := by decide
  rcases family_descends (prefixWord ++ tailWord_319113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319132 : List Nat := [2, 2, 3, 2, 10]
def baseStart_319132 : Nat := 118140960795 + 319132 * 2 ^ 59
def prefixEnd_319132 : Nat := 4983230072969 + 3 ^ 40 * 319132 * 2
def baseEnd_319132 : Nat := 3596556559248299111821

theorem tailTrace_319132 : CollatzResearch.WordTrace tailWord_319132 prefixEnd_319132 3596556559248299111821 := by
  unfold tailWord_319132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819850139923371125735825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7759800186564494834314433 5819850139923371125735825)
  ·
    refine ⟨4364887604942528344301869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5819850139923371125735825 4364887604942528344301869)
    ·
      refine ⟨1636832851853448129113201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4364887604942528344301869 1636832851853448129113201)
      ·
        refine ⟨1227624638890086096834901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1636832851853448129113201 1227624638890086096834901)
        ·
          refine ⟨3596556559248299111821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1227624638890086096834901 3596556559248299111821)
          ·
            rfl

theorem cell19_319132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 10].length) (baseStart_319132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319132 prefixEnd_319132 := by exact prefixLift 319132
  have htrace : WordTrace (prefixWord ++ tailWord_319132) baseStart_319132 baseEnd_319132 := by
    simpa [prefixWord, tailWord_319132, baseEnd_319132] using wordTrace_append hprefix tailTrace_319132
  have hstable : (prefixWord ++ tailWord_319132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319132).length < 2 ^ (prefixWord ++ tailWord_319132).sum := by decide
  have hdescent : baseEnd_319132 < baseStart_319132 := by decide
  rcases family_descends (prefixWord ++ tailWord_319132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319166 : List Nat := [4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_319166 : Nat := 118140960795 + 319166 * 2 ^ 59
def prefixEnd_319166 : Nat := 4983230072969 + 3 ^ 40 * 319166 * 2
def baseEnd_319166 : Nat := 97117372784002071263519

theorem tailTrace_319166 : CollatzResearch.WordTrace tailWord_319166 prefixEnd_319166 97117372784002071263519 := by
  unfold tailWord_319166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455117545215445757276169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7760626907815710705472901 1455117545215445757276169)
  ·
    refine ⟨1091338158911584317957127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1455117545215445757276169 1091338158911584317957127)
    ·
      refine ⟨1637007238367376476935691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091338158911584317957127 1637007238367376476935691)
      ·
        refine ⟨2455510857551064715403537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637007238367376476935691 2455510857551064715403537)
        ·
          refine ⟨1841633143163298536552653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2455510857551064715403537 1841633143163298536552653)
          ·
            refine ⟨690612428686236951207245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1841633143163298536552653 690612428686236951207245)
            ·
              refine ⟨258979660757338856702717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690612428686236951207245 258979660757338856702717)
              ·
                refine ⟨97117372784002071263519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258979660757338856702717 97117372784002071263519)
                ·
                  rfl

theorem cell19_319166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_319166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319166 prefixEnd_319166 := by exact prefixLift 319166
  have htrace : WordTrace (prefixWord ++ tailWord_319166) baseStart_319166 baseEnd_319166 := by
    simpa [prefixWord, tailWord_319166, baseEnd_319166] using wordTrace_append hprefix tailTrace_319166
  have hstable : (prefixWord ++ tailWord_319166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319166).length < 2 ^ (prefixWord ++ tailWord_319166).sum := by decide
  have hdescent : baseEnd_319166 < baseStart_319166 := by decide
  rcases family_descends (prefixWord ++ tailWord_319166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319168 : List Nat := [2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_319168 : Nat := 118140960795 + 319168 * 2 ^ 59
def prefixEnd_319168 : Nat := 4983230072969 + 3 ^ 40 * 319168 * 2
def baseEnd_319168 : Nat := 97117981353666659219069

theorem tailTrace_319168 : CollatzResearch.WordTrace tailWord_319168 prefixEnd_319168 97117981353666659219069 := by
  unfold tailWord_319168
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820506653858160199891079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7760675538477546933188105 5820506653858160199891079)
  ·
    refine ⟨8730759980787240299836619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5820506653858160199891079 8730759980787240299836619)
    ·
      refine ⟨13096139971180860449754929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8730759980787240299836619 13096139971180860449754929)
      ·
        refine ⟨9822104978385645337316197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13096139971180860449754929 9822104978385645337316197)
        ·
          refine ⟨1841644683447308500746787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9822104978385645337316197 1841644683447308500746787)
          ·
            refine ⟨2762467025170962751120181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1841644683447308500746787 2762467025170962751120181)
            ·
              refine ⟨258981283609777757917517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2762467025170962751120181 258981283609777757917517)
              ·
                refine ⟨97117981353666659219069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258981283609777757917517 97117981353666659219069)
                ·
                  rfl

theorem cell19_319168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_319168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319168 prefixEnd_319168 := by exact prefixLift 319168
  have htrace : WordTrace (prefixWord ++ tailWord_319168) baseStart_319168 baseEnd_319168 := by
    simpa [prefixWord, tailWord_319168, baseEnd_319168] using wordTrace_append hprefix tailTrace_319168
  have hstable : (prefixWord ++ tailWord_319168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319168).length < 2 ^ (prefixWord ++ tailWord_319168).sum := by decide
  have hdescent : baseEnd_319168 < baseStart_319168 := by decide
  rcases family_descends (prefixWord ++ tailWord_319168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319246 : List Nat := [4, 1, 1, 2, 1, 1, 9]
def baseStart_319246 : Nat := 118140960795 + 319246 * 2 ^ 59
def prefixEnd_319246 : Nat := 4983230072969 + 3 ^ 40 * 319246 * 2
def baseEnd_319246 : Nat := 32380571856861863161841

theorem tailTrace_319246 : CollatzResearch.WordTrace tailWord_319246 prefixEnd_319246 32380571856861863161841 := by
  unfold tailWord_319246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455482275179217465140199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7762572134289159814081061 1455482275179217465140199)
  ·
    refine ⟨2183223412768826197710299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1455482275179217465140199 2183223412768826197710299)
    ·
      refine ⟨3274835119153239296565449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2183223412768826197710299 3274835119153239296565449)
      ·
        refine ⟨2456126339364929472424087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3274835119153239296565449 2456126339364929472424087)
        ·
          refine ⟨3684189509047394208636131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456126339364929472424087 3684189509047394208636131)
          ·
            refine ⟨5526284263571091312954197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3684189509047394208636131 5526284263571091312954197)
            ·
              refine ⟨32380571856861863161841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5526284263571091312954197 32380571856861863161841)
              ·
                rfl

theorem cell19_319246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_319246 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319246 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319246 prefixEnd_319246 := by exact prefixLift 319246
  have htrace : WordTrace (prefixWord ++ tailWord_319246) baseStart_319246 baseEnd_319246 := by
    simpa [prefixWord, tailWord_319246, baseEnd_319246] using wordTrace_append hprefix tailTrace_319246
  have hstable : (prefixWord ++ tailWord_319246).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319246).length < 2 ^ (prefixWord ++ tailWord_319246).sum := by decide
  have hdescent : baseEnd_319246 < baseStart_319246 := by decide
  rcases family_descends (prefixWord ++ tailWord_319246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319265 : List Nat := [1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_319265 : Nat := 118140960795 + 319265 * 2 ^ 59
def prefixEnd_319265 : Nat := 4983230072969 + 3 ^ 40 * 319265 * 2
def baseEnd_319265 : Nat := 97147496982399175063249

theorem tailTrace_319265 : CollatzResearch.WordTrace tailWord_319265 prefixEnd_319265 97147496982399175063249 := by
  unfold tailWord_319265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11644551188364905966063249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7763034125576603977375499 11644551188364905966063249)
  ·
    refine ⟨8733413391273679474547437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11644551188364905966063249 8733413391273679474547437)
    ·
      refine ⟨3275030021727629802955289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8733413391273679474547437 3275030021727629802955289)
      ·
        refine ⟨2456272516295722352216467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3275030021727629802955289 2456272516295722352216467)
        ·
          refine ⟨3684408774443583528324701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456272516295722352216467 3684408774443583528324701)
          ·
            refine ⟨1381653290416343823121763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3684408774443583528324701 1381653290416343823121763)
            ·
              refine ⟨2072479935624515734682645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1381653290416343823121763 2072479935624515734682645)
              ·
                refine ⟨97147496982399175063249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2072479935624515734682645 97147496982399175063249)
                ·
                  rfl

theorem cell19_319265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_319265 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319265 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319265 prefixEnd_319265 := by exact prefixLift 319265
  have htrace : WordTrace (prefixWord ++ tailWord_319265) baseStart_319265 baseEnd_319265 := by
    simpa [prefixWord, tailWord_319265, baseEnd_319265] using wordTrace_append hprefix tailTrace_319265
  have hstable : (prefixWord ++ tailWord_319265).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319265).length < 2 ^ (prefixWord ++ tailWord_319265).sum := by decide
  have hdescent : baseEnd_319265 < baseStart_319265 := by decide
  rcases family_descends (prefixWord ++ tailWord_319265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319341 : List Nat := [1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_319341 : Nat := 118140960795 + 319341 * 2 ^ 59
def prefixEnd_319341 : Nat := 4983230072969 + 3 ^ 40 * 319341 * 2
def baseEnd_319341 : Nat := 97170622629653517374153

theorem tailTrace_319341 : CollatzResearch.WordTrace tailWord_319341 prefixEnd_319341 97170622629653517374153 := by
  unfold tailWord_319341
  simp only [CollatzResearch.WordTrace]
  refine ⟨11647323136089570945829877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7764882090726380630553251 11647323136089570945829877)
  ·
    refine ⟨1091936544008397276171551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11647323136089570945829877 1091936544008397276171551)
    ·
      refine ⟨1637904816012595914257327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091936544008397276171551 1637904816012595914257327)
      ·
        refine ⟨2456857224018893871385991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1637904816012595914257327 2456857224018893871385991)
        ·
          refine ⟨3685285836028340807078987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2456857224018893871385991 3685285836028340807078987)
          ·
            refine ⟨5527928754042511210618481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3685285836028340807078987 5527928754042511210618481)
            ·
              refine ⟨4145946565531883407963861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5527928754042511210618481 4145946565531883407963861)
              ·
                refine ⟨97170622629653517374153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4145946565531883407963861 97170622629653517374153)
                ·
                  rfl

theorem cell19_319341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_319341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319341 prefixEnd_319341 := by exact prefixLift 319341
  have htrace : WordTrace (prefixWord ++ tailWord_319341) baseStart_319341 baseEnd_319341 := by
    simpa [prefixWord, tailWord_319341, baseEnd_319341] using wordTrace_append hprefix tailTrace_319341
  have hstable : (prefixWord ++ tailWord_319341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319341).length < 2 ^ (prefixWord ++ tailWord_319341).sum := by decide
  have hdescent : baseEnd_319341 < baseStart_319341 := by decide
  rcases family_descends (prefixWord ++ tailWord_319341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319390 : List Nat := [4, 3, 1, 3, 1, 2, 2, 3]
def baseStart_319390 : Nat := 118140960795 + 319390 * 2 ^ 59
def prefixEnd_319390 : Nat := 4983230072969 + 3 ^ 40 * 319390 * 2
def baseEnd_319390 : Nat := 97185532586435922285131

theorem tailTrace_319390 : CollatzResearch.WordTrace tailWord_319390 prefixEnd_319390 97185532586435922285131 := by
  unfold tailWord_319390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456138789114006539295453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7766073541941368209575749 1456138789114006539295453)
  ·
    refine ⟨546052045917752452235795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1456138789114006539295453 546052045917752452235795)
    ·
      refine ⟨819078068876628678353693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546052045917752452235795 819078068876628678353693)
      ·
        refine ⟨307154275828735754382635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 819078068876628678353693 307154275828735754382635)
        ·
          refine ⟨460731413743103631573953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307154275828735754382635 460731413743103631573953)
          ·
            refine ⟨345548560307327723680465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460731413743103631573953 345548560307327723680465)
            ·
              refine ⟨259161420230495792760349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345548560307327723680465 259161420230495792760349)
              ·
                refine ⟨97185532586435922285131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259161420230495792760349 97185532586435922285131)
                ·
                  rfl

theorem cell19_319390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_319390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319390 prefixEnd_319390 := by exact prefixLift 319390
  have htrace : WordTrace (prefixWord ++ tailWord_319390) baseStart_319390 baseEnd_319390 := by
    simpa [prefixWord, tailWord_319390, baseEnd_319390] using wordTrace_append hprefix tailTrace_319390
  have hstable : (prefixWord ++ tailWord_319390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319390).length < 2 ^ (prefixWord ++ tailWord_319390).sum := by decide
  have hdescent : baseEnd_319390 < baseStart_319390 := by decide
  rcases family_descends (prefixWord ++ tailWord_319390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319396 : List Nat := [2, 3, 1, 2, 1, 3, 4, 3]
def baseStart_319396 : Nat := 118140960795 + 319396 * 2 ^ 59
def prefixEnd_319396 : Nat := 4983230072969 + 3 ^ 40 * 319396 * 2
def baseEnd_319396 : Nat := 97187358295429686151781

theorem tailTrace_319396 : CollatzResearch.WordTrace tailWord_319396 prefixEnd_319396 97187358295429686151781 := by
  unfold tailWord_319396
  simp only [CollatzResearch.WordTrace]
  refine ⟨5824664575445157669541021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7766219433926876892721361 5824664575445157669541021)
  ·
    refine ⟨2184249215791934126077883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5824664575445157669541021 2184249215791934126077883)
    ·
      refine ⟨3276373823687901189116825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2184249215791934126077883 3276373823687901189116825)
      ·
        refine ⟨2457280367765925891837619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3276373823687901189116825 2457280367765925891837619)
        ·
          refine ⟨3685920551648888837756429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2457280367765925891837619 3685920551648888837756429)
          ·
            refine ⟨1382220206868333314158661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3685920551648888837756429 1382220206868333314158661)
            ·
              refine ⟨259166288787812496404749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1382220206868333314158661 259166288787812496404749)
              ·
                refine ⟨97187358295429686151781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259166288787812496404749 97187358295429686151781)
                ·
                  rfl

theorem cell19_319396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 3].length) (baseStart_319396 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319396 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319396 prefixEnd_319396 := by exact prefixLift 319396
  have htrace : WordTrace (prefixWord ++ tailWord_319396) baseStart_319396 baseEnd_319396 := by
    simpa [prefixWord, tailWord_319396, baseEnd_319396] using wordTrace_append hprefix tailTrace_319396
  have hstable : (prefixWord ++ tailWord_319396).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319396).length < 2 ^ (prefixWord ++ tailWord_319396).sum := by decide
  have hdescent : baseEnd_319396 < baseStart_319396 := by decide
  rcases family_descends (prefixWord ++ tailWord_319396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319436 : List Nat := [2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_319436 : Nat := 118140960795 + 319436 * 2 ^ 59
def prefixEnd_319436 : Nat := 4983230072969 + 3 ^ 40 * 319436 * 2
def baseEnd_319436 : Nat := 97199529688721445262783

theorem tailTrace_319436 : CollatzResearch.WordTrace tailWord_319436 prefixEnd_319436 97199529688721445262783 := by
  unfold tailWord_319436
  simp only [CollatzResearch.WordTrace]
  refine ⟨5825394035372701085269081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7767192047163601447025441 5825394035372701085269081)
  ·
    refine ⟨4369045526529525813951811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5825394035372701085269081 4369045526529525813951811)
    ·
      refine ⟨6553568289794288720927717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369045526529525813951811 6553568289794288720927717)
      ·
        refine ⟨1228794054336429135173947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6553568289794288720927717 1228794054336429135173947)
        ·
          refine ⟨1843191081504643702760921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1228794054336429135173947 1843191081504643702760921)
          ·
            refine ⟨1382393311128482777070691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843191081504643702760921 1382393311128482777070691)
            ·
              refine ⟨2073589966692724165606037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382393311128482777070691 2073589966692724165606037)
              ·
                refine ⟨97199529688721445262783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2073589966692724165606037 97199529688721445262783)
                ·
                  rfl

theorem cell19_319436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_319436 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319436 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319436 prefixEnd_319436 := by exact prefixLift 319436
  have htrace : WordTrace (prefixWord ++ tailWord_319436) baseStart_319436 baseEnd_319436 := by
    simpa [prefixWord, tailWord_319436, baseEnd_319436] using wordTrace_append hprefix tailTrace_319436
  have hstable : (prefixWord ++ tailWord_319436).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319436).length < 2 ^ (prefixWord ++ tailWord_319436).sum := by decide
  have hdescent : baseEnd_319436 < baseStart_319436 := by decide
  rcases family_descends (prefixWord ++ tailWord_319436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319455 : List Nat := [1, 1, 2, 3, 4, 1, 2, 5]
def baseStart_319455 : Nat := 118140960795 + 319455 * 2 ^ 59
def prefixEnd_319455 : Nat := 4983230072969 + 3 ^ 40 * 319455 * 2
def baseEnd_319455 : Nat := 97205311100535030840509

theorem tailTrace_319455 : CollatzResearch.WordTrace tailWord_319455 prefixEnd_319455 97205311100535030840509 := by
  unfold tailWord_319455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11651481057676568415479819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7767654038451045610319879 11651481057676568415479819)
  ·
    refine ⟨17477221586514852623219729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11651481057676568415479819 17477221586514852623219729)
    ·
      refine ⟨13107916189886139467414797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17477221586514852623219729 13107916189886139467414797)
      ·
        refine ⟨4915468571207302300280549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13107916189886139467414797 4915468571207302300280549)
        ·
          refine ⟨921650357101369181302603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4915468571207302300280549 921650357101369181302603)
          ·
            refine ⟨1382475535652053771953905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 921650357101369181302603 1382475535652053771953905)
            ·
              refine ⟨1036856651739040328965429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1382475535652053771953905 1036856651739040328965429)
              ·
                refine ⟨97205311100535030840509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1036856651739040328965429 97205311100535030840509)
                ·
                  rfl

theorem cell19_319455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_319455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319455 prefixEnd_319455 := by exact prefixLift 319455
  have htrace : WordTrace (prefixWord ++ tailWord_319455) baseStart_319455 baseEnd_319455 := by
    simpa [prefixWord, tailWord_319455, baseEnd_319455] using wordTrace_append hprefix tailTrace_319455
  have hstable : (prefixWord ++ tailWord_319455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319455).length < 2 ^ (prefixWord ++ tailWord_319455).sum := by decide
  have hdescent : baseEnd_319455 < baseStart_319455 := by decide
  rcases family_descends (prefixWord ++ tailWord_319455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319493 : List Nat := [1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_319493 : Nat := 118140960795 + 319493 * 2 ^ 59
def prefixEnd_319493 : Nat := 4983230072969 + 3 ^ 40 * 319493 * 2
def baseEnd_319493 : Nat := 97216873924162201995961

theorem tailTrace_319493 : CollatzResearch.WordTrace tailWord_319493 prefixEnd_319493 97216873924162201995961 := by
  unfold tailWord_319493
  simp only [CollatzResearch.WordTrace]
  refine ⟨11652867031538900905363133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7768578021025933936908755 11652867031538900905363133)
  ·
    refine ⟨4369825136827087839511175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11652867031538900905363133 4369825136827087839511175)
    ·
      refine ⟨6554737705240631759266763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4369825136827087839511175 6554737705240631759266763)
      ·
        refine ⟨9832106557860947638900145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6554737705240631759266763 9832106557860947638900145)
        ·
          refine ⟨7374079918395710729175109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9832106557860947638900145 7374079918395710729175109)
          ·
            refine ⟨1382639984699195761720333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7374079918395710729175109 1382639984699195761720333)
            ·
              refine ⟨518489994262198410645125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1382639984699195761720333 518489994262198410645125)
              ·
                refine ⟨97216873924162201995961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518489994262198410645125 97216873924162201995961)
                ·
                  rfl

theorem cell19_319493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_319493 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319493 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319493 prefixEnd_319493 := by exact prefixLift 319493
  have htrace : WordTrace (prefixWord ++ tailWord_319493) baseStart_319493 baseEnd_319493 := by
    simpa [prefixWord, tailWord_319493, baseEnd_319493] using wordTrace_append hprefix tailTrace_319493
  have hstable : (prefixWord ++ tailWord_319493).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319493).length < 2 ^ (prefixWord ++ tailWord_319493).sum := by decide
  have hdescent : baseEnd_319493 < baseStart_319493 := by decide
  rcases family_descends (prefixWord ++ tailWord_319493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319582 : List Nat := [4, 4, 1, 1, 2, 2, 5]
def baseStart_319582 : Nat := 118140960795 + 319582 * 2 ^ 59
def prefixEnd_319582 : Nat := 4983230072969 + 3 ^ 40 * 319582 * 2
def baseEnd_319582 : Nat := 32414651758078788672647

theorem tailTrace_319582 : CollatzResearch.WordTrace tailWord_319582 prefixEnd_319582 32414651758078788672647 := by
  unfold tailWord_319582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1457014141027058638169125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7770742085477646070235333 1457014141027058638169125)
  ·
    refine ⟨273190151442573494656711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1457014141027058638169125 273190151442573494656711)
    ·
      refine ⟨409785227163860241985067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273190151442573494656711 409785227163860241985067)
      ·
        refine ⟨614677840745790362977601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409785227163860241985067 614677840745790362977601)
        ·
          refine ⟨461008380559342772233201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614677840745790362977601 461008380559342772233201)
          ·
            refine ⟨345756285419507079174901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461008380559342772233201 345756285419507079174901)
            ·
              refine ⟨32414651758078788672647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 345756285419507079174901 32414651758078788672647)
              ·
                rfl

theorem cell19_319582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 5].length) (baseStart_319582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319582 prefixEnd_319582 := by exact prefixLift 319582
  have htrace : WordTrace (prefixWord ++ tailWord_319582) baseStart_319582 baseEnd_319582 := by
    simpa [prefixWord, tailWord_319582, baseEnd_319582] using wordTrace_append hprefix tailTrace_319582
  have hstable : (prefixWord ++ tailWord_319582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319582).length < 2 ^ (prefixWord ++ tailWord_319582).sum := by decide
  have hdescent : baseEnd_319582 < baseStart_319582 := by decide
  rcases family_descends (prefixWord ++ tailWord_319582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319607 : List Nat := [1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_319607 : Nat := 118140960795 + 319607 * 2 ^ 59
def prefixEnd_319607 : Nat := 4983230072969 + 3 ^ 40 * 319607 * 2
def baseEnd_319607 : Nat := 97251562395043715462317

theorem tailTrace_319607 : CollatzResearch.WordTrace tailWord_319607 prefixEnd_319607 97251562395043715462317 := by
  unfold tailWord_319607
  simp only [CollatzResearch.WordTrace]
  refine ⟨11657024953125898375013075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7771349968750598916675383 11657024953125898375013075)
  ·
    refine ⟨17485537429688847562519613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11657024953125898375013075 17485537429688847562519613)
    ·
      refine ⟨6557076536133317835944855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17485537429688847562519613 6557076536133317835944855)
      ·
        refine ⟨9835614804199976753917283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6557076536133317835944855 9835614804199976753917283)
        ·
          refine ⟨14753422206299965130875925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9835614804199976753917283 14753422206299965130875925)
          ·
            refine ⟨691566665920310865509809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 14753422206299965130875925 691566665920310865509809)
            ·
              refine ⟨518674999440233149132357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691566665920310865509809 518674999440233149132357)
              ·
                refine ⟨97251562395043715462317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518674999440233149132357 97251562395043715462317)
                ·
                  rfl

theorem cell19_319607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_319607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319607 prefixEnd_319607 := by exact prefixLift 319607
  have htrace : WordTrace (prefixWord ++ tailWord_319607) baseStart_319607 baseEnd_319607 := by
    simpa [prefixWord, tailWord_319607, baseEnd_319607] using wordTrace_append hprefix tailTrace_319607
  have hstable : (prefixWord ++ tailWord_319607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319607).length < 2 ^ (prefixWord ++ tailWord_319607).sum := by decide
  have hdescent : baseEnd_319607 < baseStart_319607 := by decide
  rcases family_descends (prefixWord ++ tailWord_319607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319626 : List Nat := [3, 1, 2, 3, 1, 2, 2, 5]
def baseStart_319626 : Nat := 118140960795 + 319626 * 2 ^ 59
def prefixEnd_319626 : Nat := 4983230072969 + 3 ^ 40 * 319626 * 2
def baseEnd_319626 : Nat := 97257343806857301040043

theorem tailTrace_319626 : CollatzResearch.WordTrace tailWord_319626 prefixEnd_319626 97257343806857301040043 := by
  unfold tailWord_319626
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914429485014266154988683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7771811960038043079969821 2914429485014266154988683)
  ·
    refine ⟨4371644227521399232483025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2914429485014266154988683 4371644227521399232483025)
    ·
      refine ⟨3278733170641049424362269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4371644227521399232483025 3278733170641049424362269)
      ·
        refine ⟨1229524938990393534135851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3278733170641049424362269 1229524938990393534135851)
        ·
          refine ⟨1844287408485590301203777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229524938990393534135851 1844287408485590301203777)
          ·
            refine ⟨1383215556364192725902833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844287408485590301203777 1383215556364192725902833)
            ·
              refine ⟨1037411667273144544427125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383215556364192725902833 1037411667273144544427125)
              ·
                refine ⟨97257343806857301040043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1037411667273144544427125 97257343806857301040043)
                ·
                  rfl

theorem cell19_319626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_319626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319626 prefixEnd_319626 := by exact prefixLift 319626
  have htrace : WordTrace (prefixWord ++ tailWord_319626) baseStart_319626 baseEnd_319626 := by
    simpa [prefixWord, tailWord_319626, baseEnd_319626] using wordTrace_append hprefix tailTrace_319626
  have hstable : (prefixWord ++ tailWord_319626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319626).length < 2 ^ (prefixWord ++ tailWord_319626).sum := by decide
  have hdescent : baseEnd_319626 < baseStart_319626 := by decide
  rcases family_descends (prefixWord ++ tailWord_319626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319658 : List Nat := [3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_319658 : Nat := 118140960795 + 319658 * 2 ^ 59
def prefixEnd_319658 : Nat := 4983230072969 + 3 ^ 40 * 319658 * 2
def baseEnd_319658 : Nat := 97267080921490708328845

theorem tailTrace_319658 : CollatzResearch.WordTrace tailWord_319658 prefixEnd_319658 97267080921490708328845 := by
  unfold tailWord_319658
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914721268985283521279907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7772590050627422723413085 2914721268985283521279907)
  ·
    refine ⟨4372081903477925281919861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2914721268985283521279907 4372081903477925281919861)
    ·
      refine ⟨409882678451055495179987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4372081903477925281919861 409882678451055495179987)
      ·
        refine ⟨614824017676583242769981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409882678451055495179987 614824017676583242769981)
        ·
          refine ⟨230559006628718716038743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 614824017676583242769981 230559006628718716038743)
          ·
            refine ⟨345838509943078074058115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230559006628718716038743 345838509943078074058115)
            ·
              refine ⟨518757764914617111087173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345838509943078074058115 518757764914617111087173)
              ·
                refine ⟨97267080921490708328845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518757764914617111087173 97267080921490708328845)
                ·
                  rfl

theorem cell19_319658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_319658 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319658 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319658 prefixEnd_319658 := by exact prefixLift 319658
  have htrace : WordTrace (prefixWord ++ tailWord_319658) baseStart_319658 baseEnd_319658 := by
    simpa [prefixWord, tailWord_319658, baseEnd_319658] using wordTrace_append hprefix tailTrace_319658
  have hstable : (prefixWord ++ tailWord_319658).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319658).length < 2 ^ (prefixWord ++ tailWord_319658).sum := by decide
  have hdescent : baseEnd_319658 < baseStart_319658 := by decide
  rcases family_descends (prefixWord ++ tailWord_319658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319685 : List Nat := [1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_319685 : Nat := 118140960795 + 319685 * 2 ^ 59
def prefixEnd_319685 : Nat := 4983230072969 + 3 ^ 40 * 319685 * 2
def baseEnd_319685 : Nat := 97275296611962645728771

theorem tailTrace_319685 : CollatzResearch.WordTrace tailWord_319685 prefixEnd_319685 97275296611962645728771 := by
  unfold tailWord_319685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11659869846843317696352509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7773246564562211797568339 11659869846843317696352509)
  ·
    refine ⟨4372451192566244136132191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11659869846843317696352509 4372451192566244136132191)
    ·
      refine ⟨6558676788849366204198287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4372451192566244136132191 6558676788849366204198287)
      ·
        refine ⟨9838015183274049306297431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6558676788849366204198287 9838015183274049306297431)
        ·
          refine ⟨14757022774911073959446147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9838015183274049306297431 14757022774911073959446147)
          ·
            refine ⟨22135534162366610939169221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14757022774911073959446147 22135534162366610939169221)
            ·
              refine ⟨4150412655443739551094229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22135534162366610939169221 4150412655443739551094229)
              ·
                refine ⟨97275296611962645728771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4150412655443739551094229 97275296611962645728771)
                ·
                  rfl

theorem cell19_319685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_319685 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319685 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319685 prefixEnd_319685 := by exact prefixLift 319685
  have htrace : WordTrace (prefixWord ++ tailWord_319685) baseStart_319685 baseEnd_319685 := by
    simpa [prefixWord, tailWord_319685, baseEnd_319685] using wordTrace_append hprefix tailTrace_319685
  have hstable : (prefixWord ++ tailWord_319685).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319685).length < 2 ^ (prefixWord ++ tailWord_319685).sum := by decide
  have hdescent : baseEnd_319685 < baseStart_319685 := by decide
  rcases family_descends (prefixWord ++ tailWord_319685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319723 : List Nat := [1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_319723 : Nat := 118140960795 + 319723 * 2 ^ 59
def prefixEnd_319723 : Nat := 4983230072969 + 3 ^ 40 * 319723 * 2
def baseEnd_319723 : Nat := 97286859435589816884223

theorem tailTrace_319723 : CollatzResearch.WordTrace tailWord_319723 prefixEnd_319723 97286859435589816884223 := by
  unfold tailWord_319723
  simp only [CollatzResearch.WordTrace]
  refine ⟨11661255820705650186235823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7774170547137100124157215 11661255820705650186235823)
  ·
    refine ⟨17491883731058475279353735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11661255820705650186235823 17491883731058475279353735)
    ·
      refine ⟨26237825596587712919030603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17491883731058475279353735 26237825596587712919030603)
      ·
        refine ⟨39356738394881569378545905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26237825596587712919030603 39356738394881569378545905)
        ·
          refine ⟨29517553796161177033909429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39356738394881569378545905 29517553796161177033909429)
          ·
            refine ⟨2767270668390110346929009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29517553796161177033909429 2767270668390110346929009)
            ·
              refine ⟨2075453001292582760196757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2767270668390110346929009 2075453001292582760196757)
              ·
                refine ⟨97286859435589816884223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2075453001292582760196757 97286859435589816884223)
                ·
                  rfl

theorem cell19_319723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_319723 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319723 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319723 prefixEnd_319723 := by exact prefixLift 319723
  have htrace : WordTrace (prefixWord ++ tailWord_319723) baseStart_319723 baseEnd_319723 := by
    simpa [prefixWord, tailWord_319723, baseEnd_319723] using wordTrace_append hprefix tailTrace_319723
  have hstable : (prefixWord ++ tailWord_319723).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319723).length < 2 ^ (prefixWord ++ tailWord_319723).sum := by decide
  have hdescent : baseEnd_319723 < baseStart_319723 := by decide
  rcases family_descends (prefixWord ++ tailWord_319723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319738 : List Nat := [3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_319738 : Nat := 118140960795 + 319738 * 2 ^ 59
def prefixEnd_319738 : Nat := 4983230072969 + 3 ^ 40 * 319738 * 2
def baseEnd_319738 : Nat := 97291423708074226550849

theorem tailTrace_319738 : CollatzResearch.WordTrace tailWord_319738 prefixEnd_319738 97291423708074226550849 := by
  unfold tailWord_319738
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915450728912826937007967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7774535277100871832021245 2915450728912826937007967)
  ·
    refine ⟨4373176093369240405511951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2915450728912826937007967 4373176093369240405511951)
    ·
      refine ⟨6559764140053860608267927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4373176093369240405511951 6559764140053860608267927)
      ·
        refine ⟨9839646210080790912401891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6559764140053860608267927 9839646210080790912401891)
        ·
          refine ⟨14759469315121186368602837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9839646210080790912401891 14759469315121186368602837)
          ·
            refine ⟨345925062073152805514129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 14759469315121186368602837 345925062073152805514129)
            ·
              refine ⟨259443796554864604135597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345925062073152805514129 259443796554864604135597)
              ·
                refine ⟨97291423708074226550849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259443796554864604135597 97291423708074226550849)
                ·
                  rfl

theorem cell19_319738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_319738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319738 prefixEnd_319738 := by exact prefixLift 319738
  have htrace : WordTrace (prefixWord ++ tailWord_319738) baseStart_319738 baseEnd_319738 := by
    simpa [prefixWord, tailWord_319738, baseEnd_319738] using wordTrace_append hprefix tailTrace_319738
  have hstable : (prefixWord ++ tailWord_319738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319738).length < 2 ^ (prefixWord ++ tailWord_319738).sum := by decide
  have hdescent : baseEnd_319738 < baseStart_319738 := by decide
  rcases family_descends (prefixWord ++ tailWord_319738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319740 : List Nat := [2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_319740 : Nat := 118140960795 + 319740 * 2 ^ 59
def prefixEnd_319740 : Nat := 4983230072969 + 3 ^ 40 * 319740 * 2
def baseEnd_319740 : Nat := 97292032277738814506399

theorem tailTrace_319740 : CollatzResearch.WordTrace tailWord_319740 prefixEnd_319740 97292032277738814506399 := by
  unfold tailWord_319740
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830937930822031044802337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7774583907762708059736449 5830937930822031044802337)
  ·
    refine ⟨4373203448116523283601753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5830937930822031044802337 4373203448116523283601753)
    ·
      refine ⟨3279902586087392462701315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4373203448116523283601753 3279902586087392462701315)
      ·
        refine ⟨4919853879131088694051973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3279902586087392462701315 4919853879131088694051973)
        ·
          refine ⟨922472602337079130134745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4919853879131088694051973 922472602337079130134745)
          ·
            refine ⟨691854451752809347601059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922472602337079130134745 691854451752809347601059)
            ·
              refine ⟨1037781677629214021401589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 691854451752809347601059 1037781677629214021401589)
              ·
                refine ⟨97292032277738814506399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1037781677629214021401589 97292032277738814506399)
                ·
                  rfl

theorem cell19_319740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_319740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319740 prefixEnd_319740 := by exact prefixLift 319740
  have htrace : WordTrace (prefixWord ++ tailWord_319740) baseStart_319740 baseEnd_319740 := by
    simpa [prefixWord, tailWord_319740, baseEnd_319740] using wordTrace_append hprefix tailTrace_319740
  have hstable : (prefixWord ++ tailWord_319740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319740).length < 2 ^ (prefixWord ++ tailWord_319740).sum := by decide
  have hdescent : baseEnd_319740 < baseStart_319740 := by decide
  rcases family_descends (prefixWord ++ tailWord_319740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319761 : List Nat := [1, 2, 2, 1, 1, 5, 7]
def baseStart_319761 : Nat := 118140960795 + 319761 * 2 ^ 59
def prefixEnd_319761 : Nat := 4983230072969 + 3 ^ 40 * 319761 * 2
def baseEnd_319761 : Nat := 32432807419738996013225

theorem tailTrace_319761 : CollatzResearch.WordTrace tailWord_319761 prefixEnd_319761 32432807419738996013225 := by
  unfold tailWord_319761
  simp only [CollatzResearch.WordTrace]
  refine ⟨11662641794567982676119137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7775094529711988450746091 11662641794567982676119137)
  ·
    refine ⟨8746981345925987007089353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11662641794567982676119137 8746981345925987007089353)
    ·
      refine ⟨6560236009444490255317015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8746981345925987007089353 6560236009444490255317015)
      ·
        refine ⟨9840354014166735382975523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6560236009444490255317015 9840354014166735382975523)
        ·
          refine ⟨14760531021250103074463285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9840354014166735382975523 14760531021250103074463285)
          ·
            refine ⟨1383799783242197163230933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14760531021250103074463285 1383799783242197163230933)
            ·
              refine ⟨32432807419738996013225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1383799783242197163230933 32432807419738996013225)
              ·
                rfl

theorem cell19_319761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 7].length) (baseStart_319761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319761 prefixEnd_319761 := by exact prefixLift 319761
  have htrace : WordTrace (prefixWord ++ tailWord_319761) baseStart_319761 baseEnd_319761 := by
    simpa [prefixWord, tailWord_319761, baseEnd_319761] using wordTrace_append hprefix tailTrace_319761
  have hstable : (prefixWord ++ tailWord_319761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319761).length < 2 ^ (prefixWord ++ tailWord_319761).sum := by decide
  have hdescent : baseEnd_319761 < baseStart_319761 := by decide
  rcases family_descends (prefixWord ++ tailWord_319761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319774 : List Nat := [4, 3, 2, 1, 1, 2, 2, 4]
def baseStart_319774 : Nat := 118140960795 + 319774 * 2 ^ 59
def prefixEnd_319774 : Nat := 4983230072969 + 3 ^ 40 * 319774 * 2
def baseEnd_319774 : Nat := 97302377962036809750751

theorem tailTrace_319774 : CollatzResearch.WordTrace tailWord_319774 prefixEnd_319774 97302377962036809750751 := by
  unfold tailWord_319774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1457889492940110737042797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7775410629013923930894917 1457889492940110737042797)
  ·
    refine ⟨546708559852541526391049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1457889492940110737042797 546708559852541526391049)
    ·
      refine ⟨410031419889406144793287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 546708559852541526391049 410031419889406144793287)
      ·
        refine ⟨615047129834109217189931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 410031419889406144793287 615047129834109217189931)
        ·
          refine ⟨922570694751163825784897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615047129834109217189931 922570694751163825784897)
          ·
            refine ⟨691928021063372869338673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922570694751163825784897 691928021063372869338673)
            ·
              refine ⟨518946015797529652004005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 691928021063372869338673 518946015797529652004005)
              ·
                refine ⟨97302377962036809750751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518946015797529652004005 97302377962036809750751)
                ·
                  rfl

theorem cell19_319774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_319774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319774 prefixEnd_319774 := by exact prefixLift 319774
  have htrace : WordTrace (prefixWord ++ tailWord_319774) baseStart_319774 baseEnd_319774 := by
    simpa [prefixWord, tailWord_319774, baseEnd_319774] using wordTrace_append hprefix tailTrace_319774
  have hstable : (prefixWord ++ tailWord_319774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319774).length < 2 ^ (prefixWord ++ tailWord_319774).sum := by decide
  have hdescent : baseEnd_319774 < baseStart_319774 := by decide
  rcases family_descends (prefixWord ++ tailWord_319774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319778 : List Nat := [3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_319778 : Nat := 118140960795 + 319778 * 2 ^ 59
def prefixEnd_319778 : Nat := 4983230072969 + 3 ^ 40 * 319778 * 2
def baseEnd_319778 : Nat := 97303595101365985661851

theorem tailTrace_319778 : CollatzResearch.WordTrace tailWord_319778 prefixEnd_319778 97303595101365985661851 := by
  unfold tailWord_319778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915815458876598644871997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7775507890337596386325325 2915815458876598644871997)
  ·
    refine ⟨1093430797078724491826999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2915815458876598644871997 1093430797078724491826999)
    ·
      refine ⟨1640146195618086737740499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093430797078724491826999 1640146195618086737740499)
      ·
        refine ⟨2460219293427130106610749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1640146195618086737740499 2460219293427130106610749)
        ·
          refine ⟨922582235035173789979031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2460219293427130106610749 922582235035173789979031)
          ·
            refine ⟨1383873352552760684968547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922582235035173789979031 1383873352552760684968547)
            ·
              refine ⟨2075810028829141027452821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1383873352552760684968547 2075810028829141027452821)
              ·
                refine ⟨97303595101365985661851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2075810028829141027452821 97303595101365985661851)
                ·
                  rfl

theorem cell19_319778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_319778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319778 prefixEnd_319778 := by exact prefixLift 319778
  have htrace : WordTrace (prefixWord ++ tailWord_319778) baseStart_319778 baseEnd_319778 := by
    simpa [prefixWord, tailWord_319778, baseEnd_319778] using wordTrace_append hprefix tailTrace_319778
  have hstable : (prefixWord ++ tailWord_319778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319778).length < 2 ^ (prefixWord ++ tailWord_319778).sum := by decide
  have hdescent : baseEnd_319778 < baseStart_319778 := by decide
  rcases family_descends (prefixWord ++ tailWord_319778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319852 : List Nat := [2, 2, 1, 1, 6, 1, 3, 3]
def baseStart_319852 : Nat := 118140960795 + 319852 * 2 ^ 59
def prefixEnd_319852 : Nat := 4983230072969 + 3 ^ 40 * 319852 * 2
def baseEnd_319852 : Nat := 97326112178955740017205

theorem tailTrace_319852 : CollatzResearch.WordTrace tailWord_319852 prefixEnd_319852 97326112178955740017205 := by
  unfold tailWord_319852
  simp only [CollatzResearch.WordTrace]
  refine ⟨5832980418619152608840905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7777307224825536811787873 5832980418619152608840905)
  ·
    refine ⟨4374735313964364456630679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5832980418619152608840905 4374735313964364456630679)
    ·
      refine ⟨6562102970946546684946019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374735313964364456630679 6562102970946546684946019)
      ·
        refine ⟨9843154456419820027419029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6562102970946546684946019 9843154456419820027419029)
        ·
          refine ⟨461397865144679063785267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 9843154456419820027419029 461397865144679063785267)
          ·
            refine ⟨692096797717018595677901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461397865144679063785267 692096797717018595677901)
            ·
              refine ⟨259536299143881973379213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 692096797717018595677901 259536299143881973379213)
              ·
                refine ⟨97326112178955740017205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259536299143881973379213 97326112178955740017205)
                ·
                  rfl

theorem cell19_319852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 3].length) (baseStart_319852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319852 prefixEnd_319852 := by exact prefixLift 319852
  have htrace : WordTrace (prefixWord ++ tailWord_319852) baseStart_319852 baseEnd_319852 := by
    simpa [prefixWord, tailWord_319852, baseEnd_319852] using wordTrace_append hprefix tailTrace_319852
  have hstable : (prefixWord ++ tailWord_319852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319852).length < 2 ^ (prefixWord ++ tailWord_319852).sum := by decide
  have hdescent : baseEnd_319852 < baseStart_319852 := by decide
  rcases family_descends (prefixWord ++ tailWord_319852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319873 : List Nat := [1, 2, 4, 3, 1, 2, 6]
def baseStart_319873 : Nat := 118140960795 + 319873 * 2 ^ 59
def prefixEnd_319873 : Nat := 4983230072969 + 3 ^ 40 * 319873 * 2
def baseEnd_319873 : Nat := 32444167386811304516827

theorem tailTrace_319873 : CollatzResearch.WordTrace tailWord_319873 prefixEnd_319873 32444167386811304516827 := by
  unfold tailWord_319873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11666726770162225804196273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7777817846774817202797515 11666726770162225804196273)
  ·
    refine ⟨8750045077621669353147205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11666726770162225804196273 8750045077621669353147205)
    ·
      refine ⟨1640633452054063003715101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8750045077621669353147205 1640633452054063003715101)
      ·
        refine ⟨615237544520273626393163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1640633452054063003715101 615237544520273626393163)
        ·
          refine ⟨922856316780410439589745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615237544520273626393163 922856316780410439589745)
          ·
            refine ⟨692142237585307829692309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922856316780410439589745 692142237585307829692309)
            ·
              refine ⟨32444167386811304516827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 692142237585307829692309 32444167386811304516827)
              ·
                rfl

theorem cell19_319873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_319873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319873 prefixEnd_319873 := by exact prefixLift 319873
  have htrace : WordTrace (prefixWord ++ tailWord_319873) baseStart_319873 baseEnd_319873 := by
    simpa [prefixWord, tailWord_319873, baseEnd_319873] using wordTrace_append hprefix tailTrace_319873
  have hstable : (prefixWord ++ tailWord_319873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319873).length < 2 ^ (prefixWord ++ tailWord_319873).sum := by decide
  have hdescent : baseEnd_319873 < baseStart_319873 := by decide
  rcases family_descends (prefixWord ++ tailWord_319873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319905 : List Nat := [1, 2, 3, 5, 2, 1, 2, 3]
def baseStart_319905 : Nat := 118140960795 + 319905 * 2 ^ 59
def prefixEnd_319905 : Nat := 4983230072969 + 3 ^ 40 * 319905 * 2
def baseEnd_319905 : Nat := 97342239275067320839283

theorem tailTrace_319905 : CollatzResearch.WordTrace tailWord_319905 prefixEnd_319905 97342239275067320839283 := by
  unfold tailWord_319905
  simp only [CollatzResearch.WordTrace]
  refine ⟨11667893906046295269361169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7778595937364196846240779 11667893906046295269361169)
  ·
    refine ⟨8750920429534721452020877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11667893906046295269361169 8750920429534721452020877)
    ·
      refine ⟨3281595161075520544507829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8750920429534721452020877 3281595161075520544507829)
      ·
        refine ⟨307649546350830051047609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3281595161075520544507829 307649546350830051047609)
        ·
          refine ⟨230737159763122538285707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307649546350830051047609 230737159763122538285707)
          ·
            refine ⟨346105739644683807428561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230737159763122538285707 346105739644683807428561)
            ·
              refine ⟨259579304733512855571421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346105739644683807428561 259579304733512855571421)
              ·
                refine ⟨97342239275067320839283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259579304733512855571421 97342239275067320839283)
                ·
                  rfl

theorem cell19_319905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_319905 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319905 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319905 prefixEnd_319905 := by exact prefixLift 319905
  have htrace : WordTrace (prefixWord ++ tailWord_319905) baseStart_319905 baseEnd_319905 := by
    simpa [prefixWord, tailWord_319905, baseEnd_319905] using wordTrace_append hprefix tailTrace_319905
  have hstable : (prefixWord ++ tailWord_319905).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319905).length < 2 ^ (prefixWord ++ tailWord_319905).sum := by decide
  have hdescent : baseEnd_319905 < baseStart_319905 := by decide
  rcases family_descends (prefixWord ++ tailWord_319905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319911 : List Nat := [1, 1, 6, 1, 1, 3, 1, 5]
def baseStart_319911 : Nat := 118140960795 + 319911 * 2 ^ 59
def prefixEnd_319911 : Nat := 4983230072969 + 3 ^ 40 * 319911 * 2
def baseEnd_319911 : Nat := 97344064984061084705933

theorem tailTrace_319911 : CollatzResearch.WordTrace tailWord_319911 prefixEnd_319911 97344064984061084705933 := by
  unfold tailWord_319911
  simp only [CollatzResearch.WordTrace]
  refine ⟨11668112744024558294079587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7778741829349705529386391 11668112744024558294079587)
  ·
    refine ⟨17502169116036837441119381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11668112744024558294079587 17502169116036837441119381)
    ·
      refine ⟨820414177314226755052471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17502169116036837441119381 820414177314226755052471)
      ·
        refine ⟨1230621265971340132578707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820414177314226755052471 1230621265971340132578707)
        ·
          refine ⟨1845931898957010198868061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1230621265971340132578707 1845931898957010198868061)
          ·
            refine ⟨692224462108878824575523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1845931898957010198868061 692224462108878824575523)
            ·
              refine ⟨1038336693163318236863285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692224462108878824575523 1038336693163318236863285)
              ·
                refine ⟨97344064984061084705933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1038336693163318236863285 97344064984061084705933)
                ·
                  rfl

theorem cell19_319911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_319911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319911 prefixEnd_319911 := by exact prefixLift 319911
  have htrace : WordTrace (prefixWord ++ tailWord_319911) baseStart_319911 baseEnd_319911 := by
    simpa [prefixWord, tailWord_319911, baseEnd_319911] using wordTrace_append hprefix tailTrace_319911
  have hstable : (prefixWord ++ tailWord_319911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319911).length < 2 ^ (prefixWord ++ tailWord_319911).sum := by decide
  have hdescent : baseEnd_319911 < baseStart_319911 := by decide
  rcases family_descends (prefixWord ++ tailWord_319911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_319924 : List Nat := [2, 5, 2, 2, 2, 1, 5]
def baseStart_319924 : Nat := 118140960795 + 319924 * 2 ^ 59
def prefixEnd_319924 : Nat := 4983230072969 + 3 ^ 40 * 319924 * 2
def baseEnd_319924 : Nat := 32449340228960302139003

theorem tailTrace_319924 : CollatzResearch.WordTrace tailWord_319924 prefixEnd_319924 32449340228960302139003 := by
  unfold tailWord_319924
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834293446488730757151413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7779057928651641009535217 5834293446488730757151413)
  ·
    refine ⟨546965010608318508482945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5834293446488730757151413 546965010608318508482945)
    ·
      refine ⟨410223757956238881362209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 546965010608318508482945 410223757956238881362209)
      ·
        refine ⟨307667818467179161021657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410223757956238881362209 307667818467179161021657)
        ·
          refine ⟨230750863850384370766243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307667818467179161021657 230750863850384370766243)
          ·
            refine ⟨346126295775576556149365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230750863850384370766243 346126295775576556149365)
            ·
              refine ⟨32449340228960302139003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 346126295775576556149365 32449340228960302139003)
              ·
                rfl

theorem cell19_319924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_319924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_319924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_319924 prefixEnd_319924 := by exact prefixLift 319924
  have htrace : WordTrace (prefixWord ++ tailWord_319924) baseStart_319924 baseEnd_319924 := by
    simpa [prefixWord, tailWord_319924, baseEnd_319924] using wordTrace_append hprefix tailTrace_319924
  have hstable : (prefixWord ++ tailWord_319924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_319924).length < 2 ^ (prefixWord ++ tailWord_319924).sum := by decide
  have hdescent : baseEnd_319924 < baseStart_319924 := by decide
  rcases family_descends (prefixWord ++ tailWord_319924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320002 : List Nat := [3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_320002 : Nat := 118140960795 + 320002 * 2 ^ 59
def prefixEnd_320002 : Nat := 4983230072969 + 3 ^ 40 * 320002 * 2
def baseEnd_320002 : Nat := 97371754903799836683463

theorem tailTrace_320002 : CollatzResearch.WordTrace tailWord_320002 prefixEnd_320002 97371754903799836683463 := by
  unfold tailWord_320002
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917857946673720208910565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7780954524463253890428173 2917857946673720208910565)
  ·
    refine ⟨547098365001322539170731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2917857946673720208910565 547098365001322539170731)
    ·
      refine ⟨820647547501983808756097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547098365001322539170731 820647547501983808756097)
      ·
        refine ⟨615485660626487856567073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 820647547501983808756097 615485660626487856567073)
        ·
          refine ⟨461614245469865892425305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615485660626487856567073 461614245469865892425305)
          ·
            refine ⟨346210684102399419318979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461614245469865892425305 346210684102399419318979)
            ·
              refine ⟨519316026153599128978469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346210684102399419318979 519316026153599128978469)
              ·
                refine ⟨97371754903799836683463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519316026153599128978469 97371754903799836683463)
                ·
                  rfl

theorem cell19_320002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_320002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320002 prefixEnd_320002 := by exact prefixLift 320002
  have htrace : WordTrace (prefixWord ++ tailWord_320002) baseStart_320002 baseEnd_320002 := by
    simpa [prefixWord, tailWord_320002, baseEnd_320002] using wordTrace_append hprefix tailTrace_320002
  have hstable : (prefixWord ++ tailWord_320002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320002).length < 2 ^ (prefixWord ++ tailWord_320002).sum := by decide
  have hdescent : baseEnd_320002 < baseStart_320002 := by decide
  rcases family_descends (prefixWord ++ tailWord_320002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320004 : List Nat := [2, 3, 2, 3, 1, 3, 1, 4]
def baseStart_320004 : Nat := 118140960795 + 320004 * 2 ^ 59
def prefixEnd_320004 : Nat := 4983230072969 + 3 ^ 40 * 320004 * 2
def baseEnd_320004 : Nat := 97372363473464424639013

theorem tailTrace_320004 : CollatzResearch.WordTrace tailWord_320004 prefixEnd_320004 97372363473464424639013 := by
  unfold tailWord_320004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5835752366343817588607533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7781003155125090118143377 5835752366343817588607533)
  ·
    refine ⟨2188407137378931595727825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5835752366343817588607533 2188407137378931595727825)
    ·
      refine ⟨1641305353034198696795869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2188407137378931595727825 1641305353034198696795869)
      ·
        refine ⟨615489507387824511298451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1641305353034198696795869 615489507387824511298451)
        ·
          refine ⟨923234261081736766947677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 615489507387824511298451 923234261081736766947677)
          ·
            refine ⟨346212847905651287605379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923234261081736766947677 346212847905651287605379)
            ·
              refine ⟨519319271858476931408069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346212847905651287605379 519319271858476931408069)
              ·
                refine ⟨97372363473464424639013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519319271858476931408069 97372363473464424639013)
                ·
                  rfl

theorem cell19_320004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_320004 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320004 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320004 prefixEnd_320004 := by exact prefixLift 320004
  have htrace : WordTrace (prefixWord ++ tailWord_320004) baseStart_320004 baseEnd_320004 := by
    simpa [prefixWord, tailWord_320004, baseEnd_320004] using wordTrace_append hprefix tailTrace_320004
  have hstable : (prefixWord ++ tailWord_320004).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320004).length < 2 ^ (prefixWord ++ tailWord_320004).sum := by decide
  have hdescent : baseEnd_320004 < baseStart_320004 := by decide
  rcases family_descends (prefixWord ++ tailWord_320004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320101 : List Nat := [1, 3, 1, 3, 4, 2, 5]
def baseStart_320101 : Nat := 118140960795 + 320101 * 2 ^ 59
def prefixEnd_320101 : Nat := 4983230072969 + 3 ^ 40 * 320101 * 2
def baseEnd_320101 : Nat := 32467293034065646827731

theorem tailTrace_320101 : CollatzResearch.WordTrace tailWord_320101 prefixEnd_320101 32467293034065646827731 := by
  unfold tailWord_320101
  simp only [CollatzResearch.WordTrace]
  refine ⟨11675042613336220743496157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7783361742224147162330771 11675042613336220743496157)
  ·
    refine ⟨4378140980001082778811059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11675042613336220743496157 4378140980001082778811059)
    ·
      refine ⟨6567211470001624168216589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378140980001082778811059 6567211470001624168216589)
      ·
        refine ⟨2462704301250609063081221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6567211470001624168216589 2462704301250609063081221)
        ·
          refine ⟨461757056484489199327729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2462704301250609063081221 461757056484489199327729)
          ·
            refine ⟨346317792363366899495797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461757056484489199327729 346317792363366899495797)
            ·
              refine ⟨32467293034065646827731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 346317792363366899495797 32467293034065646827731)
              ·
                rfl

theorem cell19_320101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_320101 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320101 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320101 prefixEnd_320101 := by exact prefixLift 320101
  have htrace : WordTrace (prefixWord ++ tailWord_320101) baseStart_320101 baseEnd_320101 := by
    simpa [prefixWord, tailWord_320101, baseEnd_320101] using wordTrace_append hprefix tailTrace_320101
  have hstable : (prefixWord ++ tailWord_320101).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320101).length < 2 ^ (prefixWord ++ tailWord_320101).sum := by decide
  have hdescent : baseEnd_320101 < baseStart_320101 := by decide
  rcases family_descends (prefixWord ++ tailWord_320101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320118 : List Nat := [5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_320118 : Nat := 118140960795 + 320118 * 2 ^ 59
def prefixEnd_320118 : Nat := 4983230072969 + 3 ^ 40 * 320118 * 2
def baseEnd_320118 : Nat := 97407051944345938105369

theorem tailTrace_320118 : CollatzResearch.WordTrace tailWord_320118 prefixEnd_320118 97407051944345938105369 := by
  unfold tailWord_320118
  simp only [CollatzResearch.WordTrace]
  refine ⟨729728915892164540429063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7783775102849755097910005 729728915892164540429063)
  ·
    refine ⟨1094593373838246810643595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 729728915892164540429063 1094593373838246810643595)
    ·
      refine ⟨1641890060757370215965393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1094593373838246810643595 1641890060757370215965393)
      ·
        refine ⟨1231417545568027661974045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1641890060757370215965393 1231417545568027661974045)
        ·
          refine ⟨461781579588010373240267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231417545568027661974045 461781579588010373240267)
          ·
            refine ⟨692672369382015559860401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461781579588010373240267 692672369382015559860401)
            ·
              refine ⟨519504277036511669895301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692672369382015559860401 519504277036511669895301)
              ·
                refine ⟨97407051944345938105369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519504277036511669895301 97407051944345938105369)
                ·
                  rfl

theorem cell19_320118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_320118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320118 prefixEnd_320118 := by exact prefixLift 320118
  have htrace : WordTrace (prefixWord ++ tailWord_320118) baseStart_320118 baseEnd_320118 := by
    simpa [prefixWord, tailWord_320118, baseEnd_320118] using wordTrace_append hprefix tailTrace_320118
  have hstable : (prefixWord ++ tailWord_320118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320118).length < 2 ^ (prefixWord ++ tailWord_320118).sum := by decide
  have hdescent : baseEnd_320118 < baseStart_320118 := by decide
  rcases family_descends (prefixWord ++ tailWord_320118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320160 : List Nat := [2, 1, 1, 4, 4, 7]
def baseStart_320160 : Nat := 118140960795 + 320160 * 2 ^ 59
def prefixEnd_320160 : Nat := 4983230072969 + 3 ^ 40 * 320160 * 2
def baseEnd_320160 : Nat := 10824425767478031685769

theorem tailTrace_320160 : CollatzResearch.WordTrace tailWord_320160 prefixEnd_320160 10824425767478031685769 := by
  unfold tailWord_320160
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838597260061236909946967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7784796346748315879929289 5838597260061236909946967)
  ·
    refine ⟨8757895890091855364920451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5838597260061236909946967 8757895890091855364920451)
    ·
      refine ⟨13136843835137783047380677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8757895890091855364920451 13136843835137783047380677)
      ·
        refine ⟨2463158219088334321383877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13136843835137783047380677 2463158219088334321383877)
        ·
          refine ⟨461842166079062685259477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2463158219088334321383877 461842166079062685259477)
          ·
            refine ⟨10824425767478031685769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 461842166079062685259477 10824425767478031685769)
            ·
              rfl

theorem cell19_320160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_320160 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320160 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320160 prefixEnd_320160 := by exact prefixLift 320160
  have htrace : WordTrace (prefixWord ++ tailWord_320160) baseStart_320160 baseEnd_320160 := by
    simpa [prefixWord, tailWord_320160, baseEnd_320160] using wordTrace_append hprefix tailTrace_320160
  have hstable : (prefixWord ++ tailWord_320160).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320160).length < 2 ^ (prefixWord ++ tailWord_320160).sum := by decide
  have hdescent : baseEnd_320160 < baseStart_320160 := by decide
  rcases family_descends (prefixWord ++ tailWord_320160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320179 : List Nat := [1, 1, 1, 2, 3, 4, 3, 4]
def baseStart_320179 : Nat := 118140960795 + 320179 * 2 ^ 59
def prefixEnd_320179 : Nat := 4983230072969 + 3 ^ 40 * 320179 * 2
def baseEnd_320179 : Nat := 97425613319115870749647

theorem tailTrace_320179 : CollatzResearch.WordTrace tailWord_320179 prefixEnd_320179 97425613319115870749647 := by
  unfold tailWord_320179
  simp only [CollatzResearch.WordTrace]
  refine ⟨11677887507053640064835591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7785258338035760043223727 11677887507053640064835591)
  ·
    refine ⟨17516831260580460097253387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11677887507053640064835591 17516831260580460097253387)
    ·
      refine ⟨26275246890870690145880081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17516831260580460097253387 26275246890870690145880081)
      ·
        refine ⟨19706435168153017609410061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26275246890870690145880081 19706435168153017609410061)
        ·
          refine ⟨7389913188057381603528773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19706435168153017609410061 7389913188057381603528773)
          ·
            refine ⟨1385608722760759050661645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7389913188057381603528773 1385608722760759050661645)
            ·
              refine ⟨519603271035284643998117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1385608722760759050661645 519603271035284643998117)
              ·
                refine ⟨97425613319115870749647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519603271035284643998117 97425613319115870749647)
                ·
                  rfl

theorem cell19_320179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_320179 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320179 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320179 prefixEnd_320179 := by exact prefixLift 320179
  have htrace : WordTrace (prefixWord ++ tailWord_320179) baseStart_320179 baseEnd_320179 := by
    simpa [prefixWord, tailWord_320179, baseEnd_320179] using wordTrace_append hprefix tailTrace_320179
  have hstable : (prefixWord ++ tailWord_320179).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320179).length < 2 ^ (prefixWord ++ tailWord_320179).sum := by decide
  have hdescent : baseEnd_320179 < baseStart_320179 := by decide
  rcases family_descends (prefixWord ++ tailWord_320179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320245 : List Nat := [1, 3, 6, 1, 2, 1, 2, 3]
def baseStart_320245 : Nat := 118140960795 + 320245 * 2 ^ 59
def prefixEnd_320245 : Nat := 4983230072969 + 3 ^ 40 * 320245 * 2
def baseEnd_320245 : Nat := 97445696118047273282801

theorem tailTrace_320245 : CollatzResearch.WordTrace tailWord_320245 prefixEnd_320245 97445696118047273282801 := by
  unfold tailWord_320245
  simp only [CollatzResearch.WordTrace]
  refine ⟨11680294724814533336738189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7786863149876355557825459 11680294724814533336738189)
  ·
    refine ⟨4380110521805450001276821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11680294724814533336738189 4380110521805450001276821)
    ·
      refine ⟨205317680709630468809851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4380110521805450001276821 205317680709630468809851)
      ·
        refine ⟨307976521064445703214777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205317680709630468809851 307976521064445703214777)
        ·
          refine ⟨230982390798334277411083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307976521064445703214777 230982390798334277411083)
          ·
            refine ⟨346473586197501416116625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230982390798334277411083 346473586197501416116625)
            ·
              refine ⟨259855189648126062087469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346473586197501416116625 259855189648126062087469)
              ·
                refine ⟨97445696118047273282801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259855189648126062087469 97445696118047273282801)
                ·
                  rfl

theorem cell19_320245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_320245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320245 prefixEnd_320245 := by exact prefixLift 320245
  have htrace : WordTrace (prefixWord ++ tailWord_320245) baseStart_320245 baseEnd_320245 := by
    simpa [prefixWord, tailWord_320245, baseEnd_320245] using wordTrace_append hprefix tailTrace_320245
  have hstable : (prefixWord ++ tailWord_320245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320245).length < 2 ^ (prefixWord ++ tailWord_320245).sum := by decide
  have hdescent : baseEnd_320245 < baseStart_320245 := by decide
  rcases family_descends (prefixWord ++ tailWord_320245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320293 : List Nat := [1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_320293 : Nat := 118140960795 + 320293 * 2 ^ 59
def prefixEnd_320293 : Nat := 4983230072969 + 3 ^ 40 * 320293 * 2
def baseEnd_320293 : Nat := 97460301789997384216003

theorem tailTrace_320293 : CollatzResearch.WordTrace tailWord_320293 prefixEnd_320293 97460301789997384216003 := by
  unfold tailWord_320293
  simp only [CollatzResearch.WordTrace]
  refine ⟨11682045428640637534485533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7788030285760425022990355 11682045428640637534485533)
  ·
    refine ⟨4380767035740239075432075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11682045428640637534485533 4380767035740239075432075)
    ·
      refine ⟨6571150553610358613148113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4380767035740239075432075 6571150553610358613148113)
      ·
        refine ⟨4928362915207768959861085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6571150553610358613148113 4928362915207768959861085)
        ·
          refine ⟨1848136093202913359947907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4928362915207768959861085 1848136093202913359947907)
          ·
            refine ⟨2772204139804370039921861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1848136093202913359947907 2772204139804370039921861)
            ·
              refine ⟨519788276213319382485349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2772204139804370039921861 519788276213319382485349)
              ·
                refine ⟨97460301789997384216003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519788276213319382485349 97460301789997384216003)
                ·
                  rfl

theorem cell19_320293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_320293 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320293 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320293 prefixEnd_320293 := by exact prefixLift 320293
  have htrace : WordTrace (prefixWord ++ tailWord_320293) baseStart_320293 baseEnd_320293 := by
    simpa [prefixWord, tailWord_320293, baseEnd_320293] using wordTrace_append hprefix tailTrace_320293
  have hstable : (prefixWord ++ tailWord_320293).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320293).length < 2 ^ (prefixWord ++ tailWord_320293).sum := by decide
  have hdescent : baseEnd_320293 < baseStart_320293 := by decide
  rcases family_descends (prefixWord ++ tailWord_320293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320348 : List Nat := [2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_320348 : Nat := 118140960795 + 320348 * 2 ^ 59
def prefixEnd_320348 : Nat := 4983230072969 + 3 ^ 40 * 320348 * 2
def baseEnd_320348 : Nat := 97477037455773552993631

theorem tailTrace_320348 : CollatzResearch.WordTrace tailWord_320348 prefixEnd_320348 97477037455773552993631 := by
  unfold tailWord_320348
  simp only [CollatzResearch.WordTrace]
  refine ⟨5842025721720690963868849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7789367628960921285158465 5842025721720690963868849)
  ·
    refine ⟨4381519291290518222901637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5842025721720690963868849 4381519291290518222901637)
    ·
      refine ⟨821534867116972166794057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4381519291290518222901637 821534867116972166794057)
      ·
        refine ⟨616151150337729125095543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 821534867116972166794057 616151150337729125095543)
        ·
          refine ⟨924226725506593687643315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616151150337729125095543 924226725506593687643315)
          ·
            refine ⟨1386340088259890531464973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924226725506593687643315 1386340088259890531464973)
            ·
              refine ⟨519877533097458949299365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1386340088259890531464973 519877533097458949299365)
              ·
                refine ⟨97477037455773552993631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 519877533097458949299365 97477037455773552993631)
                ·
                  rfl

theorem cell19_320348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_320348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320348 prefixEnd_320348 := by exact prefixLift 320348
  have htrace : WordTrace (prefixWord ++ tailWord_320348) baseStart_320348 baseEnd_320348 := by
    simpa [prefixWord, tailWord_320348, baseEnd_320348] using wordTrace_append hprefix tailTrace_320348
  have hstable : (prefixWord ++ tailWord_320348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320348).length < 2 ^ (prefixWord ++ tailWord_320348).sum := by decide
  have hdescent : baseEnd_320348 < baseStart_320348 := by decide
  rcases family_descends (prefixWord ++ tailWord_320348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320371 : List Nat := [1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_320371 : Nat := 118140960795 + 320371 * 2 ^ 59
def prefixEnd_320371 : Nat := 4983230072969 + 3 ^ 40 * 320371 * 2
def baseEnd_320371 : Nat := 97484036006916314482457

theorem tailTrace_320371 : CollatzResearch.WordTrace tailWord_320371 prefixEnd_320371 97484036006916314482457 := by
  unfold tailWord_320371
  simp only [CollatzResearch.WordTrace]
  refine ⟨11684890322358056855824967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7789926881572037903883311 11684890322358056855824967)
  ·
    refine ⟨17527335483537085283737451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11684890322358056855824967 17527335483537085283737451)
    ·
      refine ⟨26291003225305627925606177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17527335483537085283737451 26291003225305627925606177)
      ·
        refine ⟨19718252418979220944204633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26291003225305627925606177 19718252418979220944204633)
        ·
          refine ⟨14788689314234415708153475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19718252418979220944204633 14788689314234415708153475)
          ·
            refine ⟨22183033971351623562230213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14788689314234415708153475 22183033971351623562230213)
            ·
              refine ⟨4159318869628429417918165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22183033971351623562230213 4159318869628429417918165)
              ·
                refine ⟨97484036006916314482457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4159318869628429417918165 97484036006916314482457)
                ·
                  rfl

theorem cell19_320371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_320371 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320371 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320371 prefixEnd_320371 := by exact prefixLift 320371
  have htrace : WordTrace (prefixWord ++ tailWord_320371) baseStart_320371 baseEnd_320371 := by
    simpa [prefixWord, tailWord_320371, baseEnd_320371] using wordTrace_append hprefix tailTrace_320371
  have hstable : (prefixWord ++ tailWord_320371).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320371).length < 2 ^ (prefixWord ++ tailWord_320371).sum := by decide
  have hdescent : baseEnd_320371 < baseStart_320371 := by decide
  rcases family_descends (prefixWord ++ tailWord_320371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320409 : List Nat := [1, 2, 1, 2, 1, 3, 1, 8]
def baseStart_320409 : Nat := 118140960795 + 320409 * 2 ^ 59
def prefixEnd_320409 : Nat := 4983230072969 + 3 ^ 40 * 320409 * 2
def baseEnd_320409 : Nat := 97495598830543485637909

theorem tailTrace_320409 : CollatzResearch.WordTrace tailWord_320409 prefixEnd_320409 97495598830543485637909 := by
  unfold tailWord_320409
  simp only [CollatzResearch.WordTrace]
  refine ⟨11686276296220389345708281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7790850864146926230472187 11686276296220389345708281)
  ·
    refine ⟨8764707222165292009281211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11686276296220389345708281 8764707222165292009281211)
    ·
      refine ⟨13147060833247938013921817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8764707222165292009281211 13147060833247938013921817)
      ·
        refine ⟨9860295624935953510441363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13147060833247938013921817 9860295624935953510441363)
        ·
          refine ⟨14790443437403930265662045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9860295624935953510441363 14790443437403930265662045)
          ·
            refine ⟨5546416289026473849623267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14790443437403930265662045 5546416289026473849623267)
            ·
              refine ⟨8319624433539710774434901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5546416289026473849623267 8319624433539710774434901)
              ·
                refine ⟨97495598830543485637909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8319624433539710774434901 97495598830543485637909)
                ·
                  rfl

theorem cell19_320409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_320409 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320409 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320409 prefixEnd_320409 := by exact prefixLift 320409
  have htrace : WordTrace (prefixWord ++ tailWord_320409) baseStart_320409 baseEnd_320409 := by
    simpa [prefixWord, tailWord_320409, baseEnd_320409] using wordTrace_append hprefix tailTrace_320409
  have hstable : (prefixWord ++ tailWord_320409).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320409).length < 2 ^ (prefixWord ++ tailWord_320409).sum := by decide
  have hdescent : baseEnd_320409 < baseStart_320409 := by decide
  rcases family_descends (prefixWord ++ tailWord_320409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320428 : List Nat := [2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_320428 : Nat := 118140960795 + 320428 * 2 ^ 59
def prefixEnd_320428 : Nat := 4983230072969 + 3 ^ 40 * 320428 * 2
def baseEnd_320428 : Nat := 97501380242357071215635

theorem tailTrace_320428 : CollatzResearch.WordTrace tailWord_320428 prefixEnd_320428 97501380242357071215635 := by
  unfold tailWord_320428
  simp only [CollatzResearch.WordTrace]
  refine ⟨5843484641575777795324969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7791312855434370393766625 5843484641575777795324969)
  ·
    refine ⟨4382613481181833346493727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5843484641575777795324969 4382613481181833346493727)
    ·
      refine ⟨6573920221772750019740591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4382613481181833346493727 6573920221772750019740591)
      ·
        refine ⟨9860880332659125029610887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6573920221772750019740591 9860880332659125029610887)
        ·
          refine ⟨14791320498988687544416331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9860880332659125029610887 14791320498988687544416331)
          ·
            refine ⟨22186980748483031316624497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14791320498988687544416331 22186980748483031316624497)
            ·
              refine ⟨16640235561362273487468373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22186980748483031316624497 16640235561362273487468373)
              ·
                refine ⟨97501380242357071215635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16640235561362273487468373 97501380242357071215635)
                ·
                  rfl

theorem cell19_320428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_320428 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320428 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320428 prefixEnd_320428 := by exact prefixLift 320428
  have htrace : WordTrace (prefixWord ++ tailWord_320428) baseStart_320428 baseEnd_320428 := by
    simpa [prefixWord, tailWord_320428, baseEnd_320428] using wordTrace_append hprefix tailTrace_320428
  have hstable : (prefixWord ++ tailWord_320428).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320428).length < 2 ^ (prefixWord ++ tailWord_320428).sum := by decide
  have hdescent : baseEnd_320428 < baseStart_320428 := by decide
  rcases family_descends (prefixWord ++ tailWord_320428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320502 : List Nat := [5, 1, 1, 1, 3, 8]
def baseStart_320502 : Nat := 118140960795 + 320502 * 2 ^ 59
def prefixEnd_320502 : Nat := 4983230072969 + 3 ^ 40 * 320502 * 2
def baseEnd_320502 : Nat := 10835988591105202841221

theorem tailTrace_320502 : CollatzResearch.WordTrace tailWord_320502 prefixEnd_320502 10835988591105202841221 := by
  unfold tailWord_320502
  simp only [CollatzResearch.WordTrace]
  refine ⟨730604267805216639302735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7793112189922310819229173 730604267805216639302735)
  ·
    refine ⟨1095906401707824958954103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730604267805216639302735 1095906401707824958954103)
    ·
      refine ⟨1643859602561737438431155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1095906401707824958954103 1643859602561737438431155)
      ·
        refine ⟨2465789403842606157646733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643859602561737438431155 2465789403842606157646733)
        ·
          refine ⟨924671026440977309117525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2465789403842606157646733 924671026440977309117525)
          ·
            refine ⟨10835988591105202841221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 924671026440977309117525 10835988591105202841221)
            ·
              rfl

theorem cell19_320502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_320502 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320502 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320502 prefixEnd_320502 := by exact prefixLift 320502
  have htrace : WordTrace (prefixWord ++ tailWord_320502) baseStart_320502 baseEnd_320502 := by
    simpa [prefixWord, tailWord_320502, baseEnd_320502] using wordTrace_append hprefix tailTrace_320502
  have hstable : (prefixWord ++ tailWord_320502).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320502).length < 2 ^ (prefixWord ++ tailWord_320502).sum := by decide
  have hdescent : baseEnd_320502 < baseStart_320502 := by decide
  rcases family_descends (prefixWord ++ tailWord_320502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320561 : List Nat := [1, 2, 2, 3, 1, 2, 8]
def baseStart_320561 : Nat := 118140960795 + 320561 * 2 ^ 59
def prefixEnd_320561 : Nat := 4983230072969 + 3 ^ 40 * 320561 * 2
def baseEnd_320561 : Nat := 32513950041684056753239

theorem tailTrace_320561 : CollatzResearch.WordTrace tailWord_320561 prefixEnd_320561 32513950041684056753239 := by
  unfold tailWord_320561
  simp only [CollatzResearch.WordTrace]
  refine ⟨11691820191669719305241537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7794546794446479536827691 11691820191669719305241537)
  ·
    refine ⟨8768865143752289478931153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11691820191669719305241537 8768865143752289478931153)
    ·
      refine ⟨6576648857814217109198365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8768865143752289478931153 6576648857814217109198365)
      ·
        refine ⟨2466243321680331415949387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6576648857814217109198365 2466243321680331415949387)
        ·
          refine ⟨3699364982520497123924081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2466243321680331415949387 3699364982520497123924081)
          ·
            refine ⟨2774523736890372842943061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3699364982520497123924081 2774523736890372842943061)
            ·
              refine ⟨32513950041684056753239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2774523736890372842943061 32513950041684056753239)
              ·
                rfl

theorem cell19_320561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_320561 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320561 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320561 prefixEnd_320561 := by exact prefixLift 320561
  have htrace : WordTrace (prefixWord ++ tailWord_320561) baseStart_320561 baseEnd_320561 := by
    simpa [prefixWord, tailWord_320561, baseEnd_320561] using wordTrace_append hprefix tailTrace_320561
  have hstable : (prefixWord ++ tailWord_320561).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320561).length < 2 ^ (prefixWord ++ tailWord_320561).sum := by decide
  have hdescent : baseEnd_320561 < baseStart_320561 := by decide
  rcases family_descends (prefixWord ++ tailWord_320561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320654 : List Nat := [4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_320654 : Nat := 118140960795 + 320654 * 2 ^ 59
def prefixEnd_320654 : Nat := 4983230072969 + 3 ^ 40 * 320654 * 2
def baseEnd_320654 : Nat := 97570148614455510192797

theorem tailTrace_320654 : CollatzResearch.WordTrace tailWord_320654 prefixEnd_320654 97570148614455510192797 := by
  unfold tailWord_320654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1461901522541599523547127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7796808120221864125584677 1461901522541599523547127)
  ·
    refine ⟨2192852283812399285320691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1461901522541599523547127 2192852283812399285320691)
    ·
      refine ⟨3289278425718598927981037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2192852283812399285320691 3289278425718598927981037)
      ·
        refine ⟨1233479409644474597992889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3289278425718598927981037 1233479409644474597992889)
        ·
          refine ⟨925109557233355948494667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1233479409644474597992889 925109557233355948494667)
          ·
            refine ⟨1387664335850033922742001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925109557233355948494667 1387664335850033922742001)
            ·
              refine ⟨1040748251887525442056501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387664335850033922742001 1040748251887525442056501)
              ·
                refine ⟨97570148614455510192797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1040748251887525442056501 97570148614455510192797)
                ·
                  rfl

theorem cell19_320654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_320654 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320654 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320654 prefixEnd_320654 := by exact prefixLift 320654
  have htrace : WordTrace (prefixWord ++ tailWord_320654) baseStart_320654 baseEnd_320654 := by
    simpa [prefixWord, tailWord_320654, baseEnd_320654] using wordTrace_append hprefix tailTrace_320654
  have hstable : (prefixWord ++ tailWord_320654).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320654).length < 2 ^ (prefixWord ++ tailWord_320654).sum := by decide
  have hdescent : baseEnd_320654 < baseStart_320654 := by decide
  rcases family_descends (prefixWord ++ tailWord_320654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320764 : List Nat := [2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_320764 : Nat := 118140960795 + 320764 * 2 ^ 59
def prefixEnd_320764 : Nat := 4983230072969 + 3 ^ 40 * 320764 * 2
def baseEnd_320764 : Nat := 97603619946007847748053

theorem tailTrace_320764 : CollatzResearch.WordTrace tailWord_320764 prefixEnd_320764 97603619946007847748053 := by
  unfold tailWord_320764
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849612104967142487440673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7799482806622856649920897 5849612104967142487440673)
  ·
    refine ⟨4387209078725356865580505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5849612104967142487440673 4387209078725356865580505)
    ·
      refine ⟨3290406809044017649185379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4387209078725356865580505 3290406809044017649185379)
      ·
        refine ⟨4935610213566026473778069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290406809044017649185379 4935610213566026473778069)
        ·
          refine ⟨231356728760907490958347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4935610213566026473778069 231356728760907490958347)
          ·
            refine ⟨347035093141361236437521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231356728760907490958347 347035093141361236437521)
            ·
              refine ⟨260276319856020927328141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347035093141361236437521 260276319856020927328141)
              ·
                refine ⟨97603619946007847748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260276319856020927328141 97603619946007847748053)
                ·
                  rfl

theorem cell19_320764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_320764 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320764 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320764 prefixEnd_320764 := by exact prefixLift 320764
  have htrace : WordTrace (prefixWord ++ tailWord_320764) baseStart_320764 baseEnd_320764 := by
    simpa [prefixWord, tailWord_320764, baseEnd_320764] using wordTrace_append hprefix tailTrace_320764
  have hstable : (prefixWord ++ tailWord_320764).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320764).length < 2 ^ (prefixWord ++ tailWord_320764).sum := by decide
  have hdescent : baseEnd_320764 < baseStart_320764 := by decide
  rcases family_descends (prefixWord ++ tailWord_320764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320766 : List Nat := [4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_320766 : Nat := 118140960795 + 320766 * 2 ^ 59
def prefixEnd_320766 : Nat := 4983230072969 + 3 ^ 40 * 320766 * 2
def baseEnd_320766 : Nat := 97604228515672435703603

theorem tailTrace_320766 : CollatzResearch.WordTrace tailWord_320766 prefixEnd_320766 97604228515672435703603 := by
  unfold tailWord_320766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462412144490879914556769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7799531437284692877636101 1462412144490879914556769)
  ·
    refine ⟨1096809108368159935917577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1462412144490879914556769 1096809108368159935917577)
    ·
      refine ⟨822606831276119951938183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1096809108368159935917577 822606831276119951938183)
      ·
        refine ⟨1233910246914179927907275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822606831276119951938183 1233910246914179927907275)
        ·
          refine ⟨1850865370371269891860913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1233910246914179927907275 1850865370371269891860913)
          ·
            refine ⟨1388149027778452418895685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850865370371269891860913 1388149027778452418895685)
            ·
              refine ⟨260277942708459828542941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1388149027778452418895685 260277942708459828542941)
              ·
                refine ⟨97604228515672435703603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260277942708459828542941 97604228515672435703603)
                ·
                  rfl

theorem cell19_320766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_320766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320766 prefixEnd_320766 := by exact prefixLift 320766
  have htrace : WordTrace (prefixWord ++ tailWord_320766) baseStart_320766 baseEnd_320766 := by
    simpa [prefixWord, tailWord_320766, baseEnd_320766] using wordTrace_append hprefix tailTrace_320766
  have hstable : (prefixWord ++ tailWord_320766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320766).length < 2 ^ (prefixWord ++ tailWord_320766).sum := by decide
  have hdescent : baseEnd_320766 < baseStart_320766 := by decide
  rcases family_descends (prefixWord ++ tailWord_320766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320878 : List Nat := [4, 1, 2, 4, 1, 1, 3, 3]
def baseStart_320878 : Nat := 118140960795 + 320878 * 2 ^ 59
def prefixEnd_320878 : Nat := 4983230072969 + 3 ^ 40 * 320878 * 2
def baseEnd_320878 : Nat := 97638308416889361214409

theorem tailTrace_320878 : CollatzResearch.WordTrace tailWord_320878 prefixEnd_320878 97638308416889361214409 := by
  unfold tailWord_320878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462922766440160305566411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7802254754347521629687525 1462922766440160305566411)
  ·
    refine ⟨2194384149660240458349617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1462922766440160305566411 2194384149660240458349617)
    ·
      refine ⟨1645788112245180343762213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2194384149660240458349617 1645788112245180343762213)
      ·
        refine ⟨308585271045971314455415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1645788112245180343762213 308585271045971314455415)
        ·
          refine ⟨462877906568956971683123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308585271045971314455415 462877906568956971683123)
          ·
            refine ⟨694316859853435457524685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462877906568956971683123 694316859853435457524685)
            ·
              refine ⟨260368822445038296571757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694316859853435457524685 260368822445038296571757)
              ·
                refine ⟨97638308416889361214409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260368822445038296571757 97638308416889361214409)
                ·
                  rfl

theorem cell19_320878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_320878 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320878 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320878 prefixEnd_320878 := by exact prefixLift 320878
  have htrace : WordTrace (prefixWord ++ tailWord_320878) baseStart_320878 baseEnd_320878 := by
    simpa [prefixWord, tailWord_320878, baseEnd_320878] using wordTrace_append hprefix tailTrace_320878
  have hstable : (prefixWord ++ tailWord_320878).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320878).length < 2 ^ (prefixWord ++ tailWord_320878).sum := by decide
  have hdescent : baseEnd_320878 < baseStart_320878 := by decide
  rcases family_descends (prefixWord ++ tailWord_320878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_320882 : List Nat := [3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_320882 : Nat := 118140960795 + 320882 * 2 ^ 59
def prefixEnd_320882 : Nat := 4983230072969 + 3 ^ 40 * 320882 * 2
def baseEnd_320882 : Nat := 97639525556218537125509

theorem tailTrace_320882 : CollatzResearch.WordTrace tailWord_320882 prefixEnd_320882 97639525556218537125509 := by
  unfold tailWord_320882
  simp only [CollatzResearch.WordTrace]
  refine ⟨2925882005876697781919225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7802352015671194085117933 2925882005876697781919225)
  ·
    refine ⟨2194411504407523336439419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2925882005876697781919225 2194411504407523336439419)
    ·
      refine ⟨3291617256611285004659129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194411504407523336439419 3291617256611285004659129)
      ·
        refine ⟨2468712942458463753494347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3291617256611285004659129 2468712942458463753494347)
        ·
          refine ⟨3703069413687695630241521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2468712942458463753494347 3703069413687695630241521)
          ·
            refine ⟨2777302060265771722681141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3703069413687695630241521 2777302060265771722681141)
            ·
              refine ⟨260372068149916099001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2777302060265771722681141 260372068149916099001357)
              ·
                refine ⟨97639525556218537125509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260372068149916099001357 97639525556218537125509)
                ·
                  rfl

theorem cell19_320882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_320882 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_320882 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_320882 prefixEnd_320882 := by exact prefixLift 320882
  have htrace : WordTrace (prefixWord ++ tailWord_320882) baseStart_320882 baseEnd_320882 := by
    simpa [prefixWord, tailWord_320882, baseEnd_320882] using wordTrace_append hprefix tailTrace_320882
  have hstable : (prefixWord ++ tailWord_320882).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_320882).length < 2 ^ (prefixWord ++ tailWord_320882).sum := by decide
  have hdescent : baseEnd_320882 < baseStart_320882 := by decide
  rcases family_descends (prefixWord ++ tailWord_320882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
