import V185TrunkScan21Chunk097

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1189634 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1189634 : Nat := 118140960795 + 1189634 * 2 ^ 59
def prefixEnd_1189634 : Nat := 4983230072969 + 3 ^ 40 * 1189634 * 2
def baseEnd_1189634 : Nat := 271490686635957237868435

theorem tailTrace_1189634 : CollatzResearch.WordTrace tailWord_1189634 prefixEnd_1189634 271490686635957237868435 := by
  unfold tailWord_1189634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10847379143041666539213989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28926344381444444104570637 10847379143041666539213989)
  ·
    refine ⟨2033883589320312476102623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10847379143041666539213989 2033883589320312476102623)
    ·
      refine ⟨3050825383980468714153935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2033883589320312476102623 3050825383980468714153935)
      ·
        refine ⟨4576238075970703071230903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050825383980468714153935 4576238075970703071230903)
        ·
          refine ⟨6864357113956054606846355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4576238075970703071230903 6864357113956054606846355)
          ·
            refine ⟨10296535670934081910269533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6864357113956054606846355 10296535670934081910269533)
            ·
              refine ⟨3861200876600280716351075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10296535670934081910269533 3861200876600280716351075)
              ·
                refine ⟨5791801314900421074526613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3861200876600280716351075 5791801314900421074526613)
                ·
                  refine ⟨271490686635957237868435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5791801314900421074526613 271490686635957237868435)
                  ·
                    rfl

theorem cell21_1189634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1189634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189634 prefixEnd_1189634 := by exact prefixLift 1189634
  have htrace : WordTrace (prefixWord ++ tailWord_1189634) baseStart_1189634 baseEnd_1189634 := by
    simpa [prefixWord, tailWord_1189634, baseEnd_1189634] using wordTrace_append hprefix tailTrace_1189634
  have hstable : (prefixWord ++ tailWord_1189634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189634).length < 2 ^ (prefixWord ++ tailWord_1189634).sum := by decide
  have hdescent : baseEnd_1189634 < baseStart_1189634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189665 : List Nat := [1, 2, 3, 2, 1, 5, 2, 5]
def baseStart_1189665 : Nat := 118140960795 + 1189665 * 2 ^ 59
def prefixEnd_1189665 : Nat := 4983230072969 + 3 ^ 40 * 1189665 * 2
def baseEnd_1189665 : Nat := 90499253752769357617235

theorem tailTrace_1189665 : CollatzResearch.WordTrace tailWord_1189665 prefixEnd_1189665 90499253752769357617235 := by
  unfold tailWord_1189665
  simp only [CollatzResearch.WordTrace]
  refine ⟨43390647235054358451234449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28927098156702905634156299 43390647235054358451234449)
  ·
    refine ⟨32542985426290768838425837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43390647235054358451234449 32542985426290768838425837)
    ·
      refine ⟨12203619534859038314409689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32542985426290768838425837 12203619534859038314409689)
      ·
        refine ⟨9152714651144278735807267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12203619534859038314409689 9152714651144278735807267)
        ·
          refine ⟨13729071976716418103710901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9152714651144278735807267 13729071976716418103710901)
          ·
            refine ⟨1287100497817164197222897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13729071976716418103710901 1287100497817164197222897)
            ·
              refine ⟨965325373362873147917173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287100497817164197222897 965325373362873147917173)
              ·
                refine ⟨90499253752769357617235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 965325373362873147917173 90499253752769357617235)
                ·
                  rfl

theorem cell21_1189665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 5].length) (baseStart_1189665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189665 prefixEnd_1189665 := by exact prefixLift 1189665
  have htrace : WordTrace (prefixWord ++ tailWord_1189665) baseStart_1189665 baseEnd_1189665 := by
    simpa [prefixWord, tailWord_1189665, baseEnd_1189665] using wordTrace_append hprefix tailTrace_1189665
  have hstable : (prefixWord ++ tailWord_1189665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189665).length < 2 ^ (prefixWord ++ tailWord_1189665).sum := by decide
  have hdescent : baseEnd_1189665 < baseStart_1189665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189752 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_1189752 : Nat := 118140960795 + 1189752 * 2 ^ 59
def prefixEnd_1189752 : Nat := 4983230072969 + 3 ^ 40 * 1189752 * 2
def baseEnd_1189752 : Nat := 271517615843615254901527

theorem tailTrace_1189752 : CollatzResearch.WordTrace tailWord_1189752 prefixEnd_1189752 271517615843615254901527 := by
  unfold tailWord_1189752
  simp only [CollatzResearch.WordTrace]
  refine ⟨21696910192869586154825755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28929213590492781539767673 21696910192869586154825755)
  ·
    refine ⟨32545365289304379232238633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21696910192869586154825755 32545365289304379232238633)
    ·
      refine ⟨24409023966978284424178975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32545365289304379232238633 24409023966978284424178975)
      ·
        refine ⟨36613535950467426636268463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24409023966978284424178975 36613535950467426636268463)
        ·
          refine ⟨54920303925701139954402695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36613535950467426636268463 54920303925701139954402695)
          ·
            refine ⟨82380455888551709931604043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54920303925701139954402695 82380455888551709931604043)
            ·
              refine ⟨123570683832827564897406065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82380455888551709931604043 123570683832827564897406065)
              ·
                refine ⟨92678012874620673673054549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123570683832827564897406065 92678012874620673673054549)
                ·
                  refine ⟨271517615843615254901527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92678012874620673673054549 271517615843615254901527)
                  ·
                    rfl

theorem cell21_1189752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_1189752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189752 prefixEnd_1189752 := by exact prefixLift 1189752
  have htrace : WordTrace (prefixWord ++ tailWord_1189752) baseStart_1189752 baseEnd_1189752 := by
    simpa [prefixWord, tailWord_1189752, baseEnd_1189752] using wordTrace_append hprefix tailTrace_1189752
  have hstable : (prefixWord ++ tailWord_1189752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189752).length < 2 ^ (prefixWord ++ tailWord_1189752).sum := by decide
  have hdescent : baseEnd_1189752 < baseStart_1189752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189758 : List Nat := [4, 2, 3, 1, 1, 3, 1, 6]
def baseStart_1189758 : Nat := 118140960795 + 1189758 * 2 ^ 59
def prefixEnd_1189758 : Nat := 4983230072969 + 3 ^ 40 * 1189758 * 2
def baseEnd_1189758 : Nat := 90506328375120192600505

theorem tailTrace_1189758 : CollatzResearch.WordTrace tailWord_1189758 prefixEnd_1189758 90506328375120192600505 := by
  unfold tailWord_1189758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424254902964679416796241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28929359482478290222913285 5424254902964679416796241)
  ·
    refine ⟨4068191177223509562597181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5424254902964679416796241 4068191177223509562597181)
    ·
      refine ⟨1525571691458816085973943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4068191177223509562597181 1525571691458816085973943)
      ·
        refine ⟨2288357537188224128960915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1525571691458816085973943 2288357537188224128960915)
        ·
          refine ⟨3432536305782336193441373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2288357537188224128960915 3432536305782336193441373)
          ·
            refine ⟨1287201114668376072540515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3432536305782336193441373 1287201114668376072540515)
            ·
              refine ⟨1930801672002564108810773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287201114668376072540515 1930801672002564108810773)
              ·
                refine ⟨90506328375120192600505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1930801672002564108810773 90506328375120192600505)
                ·
                  rfl

theorem cell21_1189758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_1189758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189758 prefixEnd_1189758 := by exact prefixLift 1189758
  have htrace : WordTrace (prefixWord ++ tailWord_1189758) baseStart_1189758 baseEnd_1189758 := by
    simpa [prefixWord, tailWord_1189758, baseEnd_1189758] using wordTrace_append hprefix tailTrace_1189758
  have hstable : (prefixWord ++ tailWord_1189758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189758).length < 2 ^ (prefixWord ++ tailWord_1189758).sum := by decide
  have hdescent : baseEnd_1189758 < baseStart_1189758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189769 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_1189769 : Nat := 118140960795 + 1189769 * 2 ^ 59
def prefixEnd_1189769 : Nat := 4983230072969 + 3 ^ 40 * 1189769 * 2
def baseEnd_1189769 : Nat := 271521495475227003118159

theorem tailTrace_1189769 : CollatzResearch.WordTrace tailWord_1189769 prefixEnd_1189769 271521495475227003118159 := by
  unfold tailWord_1189769
  simp only [CollatzResearch.WordTrace]
  refine ⟨43394440426677584213020361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28929626951118389475346907 43394440426677584213020361)
  ·
    refine ⟨32545830320008188159765271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43394440426677584213020361 32545830320008188159765271)
    ·
      refine ⟨48818745480012282239647907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32545830320008188159765271 48818745480012282239647907)
      ·
        refine ⟨73228118220018423359471861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48818745480012282239647907 73228118220018423359471861)
        ·
          refine ⟨6865136083126727189950487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73228118220018423359471861 6865136083126727189950487)
          ·
            refine ⟨10297704124690090784925731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6865136083126727189950487 10297704124690090784925731)
            ·
              refine ⟨15446556187035136177388597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10297704124690090784925731 15446556187035136177388597)
              ·
                refine ⟨1448114642534544016630181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15446556187035136177388597 1448114642534544016630181)
                ·
                  refine ⟨271521495475227003118159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448114642534544016630181 271521495475227003118159)
                  ·
                    rfl

theorem cell21_1189769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_1189769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189769 prefixEnd_1189769 := by exact prefixLift 1189769
  have htrace : WordTrace (prefixWord ++ tailWord_1189769) baseStart_1189769 baseEnd_1189769 := by
    simpa [prefixWord, tailWord_1189769, baseEnd_1189769] using wordTrace_append hprefix tailTrace_1189769
  have hstable : (prefixWord ++ tailWord_1189769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189769).length < 2 ^ (prefixWord ++ tailWord_1189769).sum := by decide
  have hdescent : baseEnd_1189769 < baseStart_1189769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189806 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_1189806 : Nat := 118140960795 + 1189806 * 2 ^ 59
def prefixEnd_1189806 : Nat := 4983230072969 + 3 ^ 40 * 1189806 * 2
def baseEnd_1189806 : Nat := 271529939379323161001417

theorem tailTrace_1189806 : CollatzResearch.WordTrace tailWord_1189806 prefixEnd_1189806 271529939379323161001417 := by
  unfold tailWord_1189806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5424473740942942441514659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28930526618362359688078181 5424473740942942441514659)
  ·
    refine ⟨8136710611414413662271989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5424473740942942441514659 8136710611414413662271989)
    ·
      refine ⟨762816619820101280837999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8136710611414413662271989 762816619820101280837999)
      ·
        refine ⟨1144224929730151921256999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 762816619820101280837999 1144224929730151921256999)
        ·
          refine ⟨1716337394595227881885499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144224929730151921256999 1716337394595227881885499)
          ·
            refine ⟨2574506091892841822828249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716337394595227881885499 2574506091892841822828249)
            ·
              refine ⟨1930879568919631367121187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2574506091892841822828249 1930879568919631367121187)
              ·
                refine ⟨2896319353379447050681781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930879568919631367121187 2896319353379447050681781)
                ·
                  refine ⟨271529939379323161001417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2896319353379447050681781 271529939379323161001417)
                  ·
                    rfl

theorem cell21_1189806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_1189806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189806 prefixEnd_1189806 := by exact prefixLift 1189806
  have htrace : WordTrace (prefixWord ++ tailWord_1189806) baseStart_1189806 baseEnd_1189806 := by
    simpa [prefixWord, tailWord_1189806, baseEnd_1189806] using wordTrace_append hprefix tailTrace_1189806
  have hstable : (prefixWord ++ tailWord_1189806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189806).length < 2 ^ (prefixWord ++ tailWord_1189806).sum := by decide
  have hdescent : baseEnd_1189806 < baseStart_1189806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189820 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_1189820 : Nat := 118140960795 + 1189820 * 2 ^ 59
def prefixEnd_1189820 : Nat := 4983230072969 + 3 ^ 40 * 1189820 * 2
def baseEnd_1189820 : Nat := 271533134370062247768055

theorem tailTrace_1189820 : CollatzResearch.WordTrace tailWord_1189820 prefixEnd_1189820 271533134370062247768055 := by
  unfold tailWord_1189820
  simp only [CollatzResearch.WordTrace]
  refine ⟨21698150274746409961563457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28930867032995213282084609 21698150274746409961563457)
  ·
    refine ⟨16273612706059807471172593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21698150274746409961563457 16273612706059807471172593)
    ·
      refine ⟨12205209529544855603379445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16273612706059807471172593 12205209529544855603379445)
      ·
        refine ⟨1144238393394830212816823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12205209529544855603379445 1144238393394830212816823)
        ·
          refine ⟨1716357590092245319225235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1144238393394830212816823 1716357590092245319225235)
          ·
            refine ⟨2574536385138367978837853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1716357590092245319225235 2574536385138367978837853)
            ·
              refine ⟨965451144426887992064195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2574536385138367978837853 965451144426887992064195)
              ·
                refine ⟨1448176716640331988096293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 965451144426887992064195 1448176716640331988096293)
                ·
                  refine ⟨271533134370062247768055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448176716640331988096293 271533134370062247768055)
                  ·
                    rfl

theorem cell21_1189820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_1189820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189820 prefixEnd_1189820 := by exact prefixLift 1189820
  have htrace : WordTrace (prefixWord ++ tailWord_1189820) baseStart_1189820 baseEnd_1189820 := by
    simpa [prefixWord, tailWord_1189820, baseEnd_1189820] using wordTrace_append hprefix tailTrace_1189820
  have hstable : (prefixWord ++ tailWord_1189820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189820).length < 2 ^ (prefixWord ++ tailWord_1189820).sum := by decide
  have hdescent : baseEnd_1189820 < baseStart_1189820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189845 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1189845 : Nat := 118140960795 + 1189845 * 2 ^ 59
def prefixEnd_1189845 : Nat := 4983230072969 + 3 ^ 40 * 1189845 * 2
def baseEnd_1189845 : Nat := 271538839710667759851337

theorem tailTrace_1189845 : CollatzResearch.WordTrace tailWord_1189845 prefixEnd_1189845 271538839710667759851337 := by
  unfold tailWord_1189845
  simp only [CollatzResearch.WordTrace]
  refine ⟨43397212374402249192786989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28931474916268166128524659 43397212374402249192786989)
  ·
    refine ⟨16273954640400843447295121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43397212374402249192786989 16273954640400843447295121)
    ·
      refine ⟨12205465980300632585471341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16273954640400843447295121 12205465980300632585471341)
      ·
        refine ⟨4577049742612737219551753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12205465980300632585471341 4577049742612737219551753)
        ·
          refine ⟨3432787306959552914663815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4577049742612737219551753 3432787306959552914663815)
          ·
            refine ⟨5149180960439329371995723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3432787306959552914663815 5149180960439329371995723)
            ·
              refine ⟨7723771440658994057993585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5149180960439329371995723 7723771440658994057993585)
              ·
                refine ⟨5792828580494245543495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7723771440658994057993585 5792828580494245543495189)
                ·
                  refine ⟨271538839710667759851337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5792828580494245543495189 271538839710667759851337)
                  ·
                    rfl

theorem cell21_1189845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1189845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189845 prefixEnd_1189845 := by exact prefixLift 1189845
  have htrace : WordTrace (prefixWord ++ tailWord_1189845) baseStart_1189845 baseEnd_1189845 := by
    simpa [prefixWord, tailWord_1189845, baseEnd_1189845] using wordTrace_append hprefix tailTrace_1189845
  have hstable : (prefixWord ++ tailWord_1189845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189845).length < 2 ^ (prefixWord ++ tailWord_1189845).sum := by decide
  have hdescent : baseEnd_1189845 < baseStart_1189845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189859 : List Nat := [1, 1, 1, 6, 1, 2, 9]
def baseStart_1189859 : Nat := 118140960795 + 1189859 * 2 ^ 59
def prefixEnd_1189859 : Nat := 4983230072969 + 3 ^ 40 * 1189859 * 2
def baseEnd_1189859 : Nat := 30171337189045205179775

theorem tailTrace_1189859 : CollatzResearch.WordTrace tailWord_1189859 prefixEnd_1189859 30171337189045205179775 := by
  unfold tailWord_1189859
  simp only [CollatzResearch.WordTrace]
  refine ⟨43397722996351529583796631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28931815330901019722531087 43397722996351529583796631)
  ·
    refine ⟨65096584494527294375694947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43397722996351529583796631 65096584494527294375694947)
    ·
      refine ⟨97644876741790941563542421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65096584494527294375694947 97644876741790941563542421)
      ·
        refine ⟨4577103597271450385791051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 97644876741790941563542421 4577103597271450385791051)
        ·
          refine ⟨6865655395907175578686577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4577103597271450385791051 6865655395907175578686577)
          ·
            refine ⟨5149241546930381684014933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6865655395907175578686577 5149241546930381684014933)
            ·
              refine ⟨30171337189045205179775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5149241546930381684014933 30171337189045205179775)
              ·
                rfl

theorem cell21_1189859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 9].length) (baseStart_1189859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189859 prefixEnd_1189859 := by exact prefixLift 1189859
  have htrace : WordTrace (prefixWord ++ tailWord_1189859) baseStart_1189859 baseEnd_1189859 := by
    simpa [prefixWord, tailWord_1189859, baseEnd_1189859] using wordTrace_append hprefix tailTrace_1189859
  have hstable : (prefixWord ++ tailWord_1189859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189859).length < 2 ^ (prefixWord ++ tailWord_1189859).sum := by decide
  have hdescent : baseEnd_1189859 < baseStart_1189859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189952 : List Nat := [2, 1, 1, 2, 2, 5, 3, 5]
def baseStart_1189952 : Nat := 118140960795 + 1189952 * 2 ^ 59
def prefixEnd_1189952 : Nat := 4983230072969 + 3 ^ 40 * 1189952 * 2
def baseEnd_1189952 : Nat := 90521086189486450522595

theorem tailTrace_1189952 : CollatzResearch.WordTrace tailWord_1189952 prefixEnd_1189952 90521086189486450522595 := by
  unfold tailWord_1189952
  simp only [CollatzResearch.WordTrace]
  refine ⟨21700557492507303233466055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28934076656676404311288073 21700557492507303233466055)
  ·
    refine ⟨32550836238760954850199083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21700557492507303233466055 32550836238760954850199083)
    ·
      refine ⟨48826254358141432275298625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32550836238760954850199083 48826254358141432275298625)
      ·
        refine ⟨36619690768606074206473969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48826254358141432275298625 36619690768606074206473969)
        ·
          refine ⟨27464768076454555654855477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36619690768606074206473969 27464768076454555654855477)
          ·
            refine ⟨2574822007167614592642701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27464768076454555654855477 2574822007167614592642701)
            ·
              refine ⟨965558252687855472241013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2574822007167614592642701 965558252687855472241013)
              ·
                refine ⟨90521086189486450522595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 965558252687855472241013 90521086189486450522595)
                ·
                  rfl

theorem cell21_1189952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_1189952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189952 prefixEnd_1189952 := by exact prefixLift 1189952
  have htrace : WordTrace (prefixWord ++ tailWord_1189952) baseStart_1189952 baseEnd_1189952 := by
    simpa [prefixWord, tailWord_1189952, baseEnd_1189952] using wordTrace_append hprefix tailTrace_1189952
  have hstable : (prefixWord ++ tailWord_1189952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189952).length < 2 ^ (prefixWord ++ tailWord_1189952).sum := by decide
  have hdescent : baseEnd_1189952 < baseStart_1189952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190017 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 3]
def baseStart_1190017 : Nat := 118140960795 + 1190017 * 2 ^ 59
def prefixEnd_1190017 : Nat := 4983230072969 + 3 ^ 40 * 1190017 * 2
def baseEnd_1190017 : Nat := 271578092454033682984319

theorem tailTrace_1190017 : CollatzResearch.WordTrace tailWord_1190017 prefixEnd_1190017 271578092454033682984319 := by
  unfold tailWord_1190017
  simp only [CollatzResearch.WordTrace]
  refine ⟨43403485729779122568048305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28935657153186081712032203 43403485729779122568048305)
  ·
    refine ⟨32552614297334341926036229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43403485729779122568048305 32552614297334341926036229)
    ·
      refine ⟨6103615180750189111131793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32552614297334341926036229 6103615180750189111131793)
      ·
        refine ⟨4577711385562641833348845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6103615180750189111131793 4577711385562641833348845)
        ·
          refine ⟨1716641769585990687505817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4577711385562641833348845 1716641769585990687505817)
          ·
            refine ⟨1287481327189493015629363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716641769585990687505817 1287481327189493015629363)
            ·
              refine ⟨1931221990784239523444045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287481327189493015629363 1931221990784239523444045)
              ·
                refine ⟨724208246544089821291517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1931221990784239523444045 724208246544089821291517)
                ·
                  refine ⟨271578092454033682984319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724208246544089821291517 271578092454033682984319)
                  ·
                    rfl

theorem cell21_1190017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_1190017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190017 prefixEnd_1190017 := by exact prefixLift 1190017
  have htrace : WordTrace (prefixWord ++ tailWord_1190017) baseStart_1190017 baseEnd_1190017 := by
    simpa [prefixWord, tailWord_1190017, baseEnd_1190017] using wordTrace_append hprefix tailTrace_1190017
  have hstable : (prefixWord ++ tailWord_1190017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190017).length < 2 ^ (prefixWord ++ tailWord_1190017).sum := by decide
  have hdescent : baseEnd_1190017 < baseStart_1190017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190104 : List Nat := [2, 1, 2, 2, 4, 3, 1, 6]
def baseStart_1190104 : Nat := 118140960795 + 1190104 * 2 ^ 59
def prefixEnd_1190104 : Nat := 4983230072969 + 3 ^ 40 * 1190104 * 2
def baseEnd_1190104 : Nat := 90532649013113621678047

theorem tailTrace_1190104 : CollatzResearch.WordTrace tailWord_1190104 prefixEnd_1190104 90532649013113621678047 := by
  unfold tailWord_1190104
  simp only [CollatzResearch.WordTrace]
  refine ⟨21703329440231968213232683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28937772586975957617643577 21703329440231968213232683)
  ·
    refine ⟨32554994160347952319849025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21703329440231968213232683 32554994160347952319849025)
    ·
      refine ⟨24416245620260964239886769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32554994160347952319849025 24416245620260964239886769)
      ·
        refine ⟨18312184215195723179915077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24416245620260964239886769 18312184215195723179915077)
        ·
          refine ⟨3433534540349198096234077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18312184215195723179915077 3433534540349198096234077)
          ·
            refine ⟨1287575452630949286087779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3433534540349198096234077 1287575452630949286087779)
            ·
              refine ⟨1931363178946423929131669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287575452630949286087779 1931363178946423929131669)
              ·
                refine ⟨90532649013113621678047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1931363178946423929131669 90532649013113621678047)
                ·
                  rfl

theorem cell21_1190104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_1190104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190104 prefixEnd_1190104 := by exact prefixLift 1190104
  have htrace : WordTrace (prefixWord ++ tailWord_1190104) baseStart_1190104 baseEnd_1190104 := by
    simpa [prefixWord, tailWord_1190104, baseEnd_1190104] using wordTrace_append hprefix tailTrace_1190104
  have hstable : (prefixWord ++ tailWord_1190104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190104).length < 2 ^ (prefixWord ++ tailWord_1190104).sum := by decide
  have hdescent : baseEnd_1190104 < baseStart_1190104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190180 : List Nat := [2, 3, 1, 3, 1, 2, 4, 5]
def baseStart_1190180 : Nat := 118140960795 + 1190180 * 2 ^ 59
def prefixEnd_1190180 : Nat := 4983230072969 + 3 ^ 40 * 1190180 * 2
def baseEnd_1190180 : Nat := 90538430424927207255773

theorem tailTrace_1190180 : CollatzResearch.WordTrace tailWord_1190180 prefixEnd_1190180 90538430424927207255773 := by
  unfold tailWord_1190180
  simp only [CollatzResearch.WordTrace]
  refine ⟨21704715414094300703115997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28939620552125734270821329 21704715414094300703115997)
  ·
    refine ⟨8139268280285362763668499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21704715414094300703115997 8139268280285362763668499)
    ·
      refine ⟨12208902420428044145502749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8139268280285362763668499 12208902420428044145502749)
      ·
        refine ⟨4578338407660516554563531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12208902420428044145502749 4578338407660516554563531)
        ·
          refine ⟨6867507611490774831845297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4578338407660516554563531 6867507611490774831845297)
          ·
            refine ⟨5150630708618081123883973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6867507611490774831845297 5150630708618081123883973)
            ·
              refine ⟨965743257865890210728245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5150630708618081123883973 965743257865890210728245)
              ·
                refine ⟨90538430424927207255773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 965743257865890210728245 90538430424927207255773)
                ·
                  rfl

theorem cell21_1190180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_1190180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190180 prefixEnd_1190180 := by exact prefixLift 1190180
  have htrace : WordTrace (prefixWord ++ tailWord_1190180) baseStart_1190180 baseEnd_1190180 := by
    simpa [prefixWord, tailWord_1190180, baseEnd_1190180] using wordTrace_append hprefix tailTrace_1190180
  have hstable : (prefixWord ++ tailWord_1190180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190180).length < 2 ^ (prefixWord ++ tailWord_1190180).sum := by decide
  have hdescent : baseEnd_1190180 < baseStart_1190180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190186 : List Nat := [3, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_1190186 : Nat := 118140960795 + 1190186 * 2 ^ 59
def prefixEnd_1190186 : Nat := 4983230072969 + 3 ^ 40 * 1190186 * 2
def baseEnd_1190186 : Nat := 271616660556526944667307

theorem tailTrace_1190186 : CollatzResearch.WordTrace tailWord_1190186 prefixEnd_1190186 271616660556526944667307 := by
  unfold tailWord_1190186
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852412416541716107737603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28939766444111242953966941 10852412416541716107737603)
  ·
    refine ⟨16278618624812574161606405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10852412416541716107737603 16278618624812574161606405)
    ·
      refine ⟨3052240992152357655301201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16278618624812574161606405 3052240992152357655301201)
      ·
        refine ⟨2289180744114268241475901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3052240992152357655301201 2289180744114268241475901)
        ·
          refine ⟨858442779042850590553463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2289180744114268241475901 858442779042850590553463)
          ·
            refine ⟨1287664168564275885830195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858442779042850590553463 1287664168564275885830195)
            ·
              refine ⟨1931496252846413828745293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1287664168564275885830195 1931496252846413828745293)
              ·
                refine ⟨724311094817405185779485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1931496252846413828745293 724311094817405185779485)
                ·
                  refine ⟨271616660556526944667307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724311094817405185779485 271616660556526944667307)
                  ·
                    rfl

theorem cell21_1190186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_1190186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190186 prefixEnd_1190186 := by exact prefixLift 1190186
  have htrace : WordTrace (prefixWord ++ tailWord_1190186) baseStart_1190186 baseEnd_1190186 := by
    simpa [prefixWord, tailWord_1190186, baseEnd_1190186] using wordTrace_append hprefix tailTrace_1190186
  have hstable : (prefixWord ++ tailWord_1190186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190186).length < 2 ^ (prefixWord ++ tailWord_1190186).sum := by decide
  have hdescent : baseEnd_1190186 < baseStart_1190186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190225 : List Nat := [1, 2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_1190225 : Nat := 118140960795 + 1190225 * 2 ^ 59
def prefixEnd_1190225 : Nat := 4983230072969 + 3 ^ 40 * 1190225 * 2
def baseEnd_1190225 : Nat := 271625560887871543517227

theorem tailTrace_1190225 : CollatzResearch.WordTrace tailWord_1190225 prefixEnd_1190225 271625560887871543517227 := by
  unfold tailWord_1190225
  simp only [CollatzResearch.WordTrace]
  refine ⟨43411072113025574091620129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28940714742017049394413419 43411072113025574091620129)
  ·
    refine ⟨32558304084769180568715097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43411072113025574091620129 32558304084769180568715097)
    ·
      refine ⟨24418728063576885426536323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32558304084769180568715097 24418728063576885426536323)
      ·
        refine ⟨36628092095365328139804485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24418728063576885426536323 36628092095365328139804485)
        ·
          refine ⟨6867767267880999026213341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36628092095365328139804485 6867767267880999026213341)
          ·
            refine ⟨2575412725455374634830003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6867767267880999026213341 2575412725455374634830003)
            ·
              refine ⟨3863119088183061952245005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575412725455374634830003 3863119088183061952245005)
              ·
                refine ⟨1448669658068648232091877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3863119088183061952245005 1448669658068648232091877)
                ·
                  refine ⟨271625560887871543517227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1448669658068648232091877 271625560887871543517227)
                  ·
                    rfl

theorem cell21_1190225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_1190225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190225 prefixEnd_1190225 := by exact prefixLift 1190225
  have htrace : WordTrace (prefixWord ++ tailWord_1190225) baseStart_1190225 baseEnd_1190225 := by
    simpa [prefixWord, tailWord_1190225, baseEnd_1190225] using wordTrace_append hprefix tailTrace_1190225
  have hstable : (prefixWord ++ tailWord_1190225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190225).length < 2 ^ (prefixWord ++ tailWord_1190225).sum := by decide
  have hdescent : baseEnd_1190225 < baseStart_1190225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190405 : List Nat := [1, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_1190405 : Nat := 118140960795 + 1190405 * 2 ^ 59
def prefixEnd_1190405 : Nat := 4983230072969 + 3 ^ 40 * 1190405 * 2
def baseEnd_1190405 : Nat := 271666639340231230516859

theorem tailTrace_1190405 : CollatzResearch.WordTrace tailWord_1190405 prefixEnd_1190405 271666639340231230516859 := by
  unfold tailWord_1190405
  simp only [CollatzResearch.WordTrace]
  refine ⟨43417637252373464833172669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28945091501582309888781779 43417637252373464833172669)
  ·
    refine ⟨16281613969640049312439751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43417637252373464833172669 16281613969640049312439751)
    ·
      refine ⟨24422420954460073968659627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16281613969640049312439751 24422420954460073968659627)
      ·
        refine ⟨36633631431690110952989441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24422420954460073968659627 36633631431690110952989441)
        ·
          refine ⟨27475223573767583214742081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36633631431690110952989441 27475223573767583214742081)
          ·
            refine ⟨20606417680325687411056561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27475223573767583214742081 20606417680325687411056561)
            ·
              refine ⟨15454813260244265558292421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20606417680325687411056561 15454813260244265558292421)
              ·
                refine ⟨2897777486295799792179829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15454813260244265558292421 2897777486295799792179829)
                ·
                  refine ⟨271666639340231230516859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2897777486295799792179829 271666639340231230516859)
                  ·
                    rfl

theorem cell21_1190405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_1190405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190405 prefixEnd_1190405 := by exact prefixLift 1190405
  have htrace : WordTrace (prefixWord ++ tailWord_1190405) baseStart_1190405 baseEnd_1190405 := by
    simpa [prefixWord, tailWord_1190405, baseEnd_1190405] using wordTrace_append hprefix tailTrace_1190405
  have hstable : (prefixWord ++ tailWord_1190405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190405).length < 2 ^ (prefixWord ++ tailWord_1190405).sum := by decide
  have hdescent : baseEnd_1190405 < baseStart_1190405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190518 : List Nat := [5, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1190518 : Nat := 118140960795 + 1190518 * 2 ^ 59
def prefixEnd_1190518 : Nat := 4983230072969 + 3 ^ 40 * 1190518 * 2
def baseEnd_1190518 : Nat := 90564142493256048377765

theorem tailTrace_1190518 : CollatzResearch.WordTrace tailWord_1190518 prefixEnd_1190518 90564142493256048377765 := by
  unfold tailWord_1190518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713859918810255320752263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28947839133976056754690805 2713859918810255320752263)
  ·
    refine ⟨4070789878215382981128395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2713859918810255320752263 4070789878215382981128395)
    ·
      refine ⟨6106184817323074471692593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4070789878215382981128395 6106184817323074471692593)
      ·
        refine ⟨4579638612992305853769445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6106184817323074471692593 4579638612992305853769445)
        ·
          refine ⟨858682239936057347581771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4579638612992305853769445 858682239936057347581771)
          ·
            refine ⟨1288023359904086021372657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 858682239936057347581771 1288023359904086021372657)
            ·
              refine ⟨966017519928064516029493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288023359904086021372657 966017519928064516029493)
              ·
                refine ⟨90564142493256048377765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966017519928064516029493 90564142493256048377765)
                ·
                  rfl

theorem cell21_1190518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1190518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190518 prefixEnd_1190518 := by exact prefixLift 1190518
  have htrace : WordTrace (prefixWord ++ tailWord_1190518) baseStart_1190518 baseEnd_1190518 := by
    simpa [prefixWord, tailWord_1190518, baseEnd_1190518] using wordTrace_append hprefix tailTrace_1190518
  have hstable : (prefixWord ++ tailWord_1190518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190518).length < 2 ^ (prefixWord ++ tailWord_1190518).sum := by decide
  have hdescent : baseEnd_1190518 < baseStart_1190518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190532 : List Nat := [2, 3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_1190532 : Nat := 118140960795 + 1190532 * 2 ^ 59
def prefixEnd_1190532 : Nat := 4983230072969 + 3 ^ 40 * 1190532 * 2
def baseEnd_1190532 : Nat := 271695622470507231899933

theorem tailTrace_1190532 : CollatzResearch.WordTrace tailWord_1190532 prefixEnd_1190532 271695622470507231899933 := by
  unfold tailWord_1190532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21711134661456682761522925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28948179548608910348697233 21711134661456682761522925)
  ·
    refine ⟨8141675498046256035571097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21711134661456682761522925 8141675498046256035571097)
    ·
      refine ⟨6106256623534692026678323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8141675498046256035571097 6106256623534692026678323)
      ·
        refine ⟨9159384935302038040017485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6106256623534692026678323 9159384935302038040017485)
        ·
          refine ⟨3434769350738264265006557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9159384935302038040017485 3434769350738264265006557)
          ·
            refine ⟨1288038506526849099377459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3434769350738264265006557 1288038506526849099377459)
            ·
              refine ⟨1932057759790273649066189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288038506526849099377459 1932057759790273649066189)
              ·
                refine ⟨724521659921352618399821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1932057759790273649066189 724521659921352618399821)
                ·
                  refine ⟨271695622470507231899933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724521659921352618399821 271695622470507231899933)
                  ·
                    rfl

theorem cell21_1190532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_1190532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190532 prefixEnd_1190532 := by exact prefixLift 1190532
  have htrace : WordTrace (prefixWord ++ tailWord_1190532) baseStart_1190532 baseEnd_1190532 := by
    simpa [prefixWord, tailWord_1190532, baseEnd_1190532] using wordTrace_append hprefix tailTrace_1190532
  have hstable : (prefixWord ++ tailWord_1190532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190532).length < 2 ^ (prefixWord ++ tailWord_1190532).sum := by decide
  have hdescent : baseEnd_1190532 < baseStart_1190532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190602 : List Nat := [3, 1, 2, 1, 4, 10]
def baseStart_1190602 : Nat := 118140960795 + 1190602 * 2 ^ 59
def prefixEnd_1190602 : Nat := 4983230072969 + 3 ^ 40 * 1190602 * 2
def baseEnd_1190602 : Nat := 10063392497192691323449

theorem tailTrace_1190602 : CollatzResearch.WordTrace tailWord_1190602 prefixEnd_1190602 10063392497192691323449 := by
  unfold tailWord_1190602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856205608164941869523515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28949881621773178318729373 10856205608164941869523515)
  ·
    refine ⟨16284308412247412804285273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856205608164941869523515 16284308412247412804285273)
    ·
      refine ⟨12213231309185559603213955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16284308412247412804285273 12213231309185559603213955)
      ·
        refine ⟨18319846963778339404820933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12213231309185559603213955 18319846963778339404820933)
        ·
          refine ⟨3434971305708438638403925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18319846963778339404820933 3434971305708438638403925)
          ·
            refine ⟨10063392497192691323449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3434971305708438638403925 10063392497192691323449)
            ·
              rfl

theorem cell21_1190602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 10].length) (baseStart_1190602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190602 prefixEnd_1190602 := by exact prefixLift 1190602
  have htrace : WordTrace (prefixWord ++ tailWord_1190602) baseStart_1190602 baseEnd_1190602 := by
    simpa [prefixWord, tailWord_1190602, baseEnd_1190602] using wordTrace_append hprefix tailTrace_1190602
  have hstable : (prefixWord ++ tailWord_1190602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190602).length < 2 ^ (prefixWord ++ tailWord_1190602).sum := by decide
  have hdescent : baseEnd_1190602 < baseStart_1190602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190647 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_1190647 : Nat := 118140960795 + 1190647 * 2 ^ 59
def prefixEnd_1190647 : Nat := 4983230072969 + 3 ^ 40 * 1190647 * 2
def baseEnd_1190647 : Nat := 271721867037292587483031

theorem tailTrace_1190647 : CollatzResearch.WordTrace tailWord_1190647 prefixEnd_1190647 271721867037292587483031 := by
  unfold tailWord_1190647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43426463717496740163482195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28950975811664493442321463 43426463717496740163482195)
  ·
    refine ⟨65139695576245110245223293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43426463717496740163482195 65139695576245110245223293)
    ·
      refine ⟨24427385841091916341958735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65139695576245110245223293 24427385841091916341958735)
      ·
        refine ⟨36641078761637874512938103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24427385841091916341958735 36641078761637874512938103)
        ·
          refine ⟨54961618142456811769407155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36641078761637874512938103 54961618142456811769407155)
          ·
            refine ⟨82442427213685217654110733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54961618142456811769407155 82442427213685217654110733)
            ·
              refine ⟨30915910205131956620291525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82442427213685217654110733 30915910205131956620291525)
              ·
                refine ⟨5796733163462241866304661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30915910205131956620291525 5796733163462241866304661)
                ·
                  refine ⟨271721867037292587483031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5796733163462241866304661 271721867037292587483031)
                  ·
                    rfl

theorem cell21_1190647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_1190647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190647 prefixEnd_1190647 := by exact prefixLift 1190647
  have htrace : WordTrace (prefixWord ++ tailWord_1190647) baseStart_1190647 baseEnd_1190647 := by
    simpa [prefixWord, tailWord_1190647, baseEnd_1190647] using wordTrace_append hprefix tailTrace_1190647
  have hstable : (prefixWord ++ tailWord_1190647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190647).length < 2 ^ (prefixWord ++ tailWord_1190647).sum := by decide
  have hdescent : baseEnd_1190647 < baseStart_1190647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190650 : List Nat := [3, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_1190650 : Nat := 118140960795 + 1190650 * 2 ^ 59
def prefixEnd_1190650 : Nat := 4983230072969 + 3 ^ 40 * 1190650 * 2
def baseEnd_1190650 : Nat := 271722551678165248933025

theorem tailTrace_1190650 : CollatzResearch.WordTrace tailWord_1190650 prefixEnd_1190650 271722551678165248933025 := by
  unfold tailWord_1190650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856643284121467918960351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28951048757657247783894269 10856643284121467918960351)
  ·
    refine ⟨16284964926182201878440527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10856643284121467918960351 16284964926182201878440527)
    ·
      refine ⟨24427447389273302817660791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16284964926182201878440527 24427447389273302817660791)
      ·
        refine ⟨36641171083909954226491187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24427447389273302817660791 36641171083909954226491187)
        ·
          refine ⟨54961756625864931339736781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36641171083909954226491187 54961756625864931339736781)
          ·
            refine ⟨20610658734699349252401293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54961756625864931339736781 20610658734699349252401293)
            ·
              refine ⟨7728997025512255969650485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20610658734699349252401293 7728997025512255969650485)
              ·
                refine ⟨724593471141773997154733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7728997025512255969650485 724593471141773997154733)
                ·
                  refine ⟨271722551678165248933025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724593471141773997154733 271722551678165248933025)
                  ·
                    rfl

theorem cell21_1190650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_1190650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190650 prefixEnd_1190650 := by exact prefixLift 1190650
  have htrace : WordTrace (prefixWord ++ tailWord_1190650) baseStart_1190650 baseEnd_1190650 := by
    simpa [prefixWord, tailWord_1190650, baseEnd_1190650] using wordTrace_append hprefix tailTrace_1190650
  have hstable : (prefixWord ++ tailWord_1190650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190650).length < 2 ^ (prefixWord ++ tailWord_1190650).sum := by decide
  have hdescent : baseEnd_1190650 < baseStart_1190650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190664 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_1190664 : Nat := 118140960795 + 1190664 * 2 ^ 59
def prefixEnd_1190664 : Nat := 4983230072969 + 3 ^ 40 * 1190664 * 2
def baseEnd_1190664 : Nat := 271725746668904335699663

theorem tailTrace_1190664 : CollatzResearch.WordTrace tailWord_1190664 prefixEnd_1190664 271725746668904335699663 := by
  unfold tailWord_1190664
  simp only [CollatzResearch.WordTrace]
  refine ⟨21713541879217576033425523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28951389172290101377900697 21713541879217576033425523)
  ·
    refine ⟨32570312818826364050138285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21713541879217576033425523 32570312818826364050138285)
    ·
      refine ⟨12213867307059886518801857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32570312818826364050138285 12213867307059886518801857)
      ·
        refine ⟨9160400480294914889101393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12213867307059886518801857 9160400480294914889101393)
        ·
          refine ⟨6870300360221186166826045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9160400480294914889101393 6870300360221186166826045)
          ·
            refine ⟨2576362635082944812559767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6870300360221186166826045 2576362635082944812559767)
            ·
              refine ⟨3864543952624417218839651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576362635082944812559767 3864543952624417218839651)
              ·
                refine ⟨5796815928936625828259477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864543952624417218839651 5796815928936625828259477)
                ·
                  refine ⟨271725746668904335699663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5796815928936625828259477 271725746668904335699663)
                  ·
                    rfl

theorem cell21_1190664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_1190664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190664 prefixEnd_1190664 := by exact prefixLift 1190664
  have htrace : WordTrace (prefixWord ++ tailWord_1190664) baseStart_1190664 baseEnd_1190664 := by
    simpa [prefixWord, tailWord_1190664, baseEnd_1190664] using wordTrace_append hprefix tailTrace_1190664
  have hstable : (prefixWord ++ tailWord_1190664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190664).length < 2 ^ (prefixWord ++ tailWord_1190664).sum := by decide
  have hdescent : baseEnd_1190664 < baseStart_1190664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190723 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_1190723 : Nat := 118140960795 + 1190723 * 2 ^ 59
def prefixEnd_1190723 : Nat := 4983230072969 + 3 ^ 40 * 1190723 * 2
def baseEnd_1190723 : Nat := 271739211272733344216209

theorem tailTrace_1190723 : CollatzResearch.WordTrace tailWord_1190723 prefixEnd_1190723 271739211272733344216209 := by
  unfold tailWord_1190723
  simp only [CollatzResearch.WordTrace]
  refine ⟨43429235665221405143248823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28952823776814270095499215 43429235665221405143248823)
  ·
    refine ⟨65143853497832107714873235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43429235665221405143248823 65143853497832107714873235)
    ·
      refine ⟨97715780246748161572309853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65143853497832107714873235 97715780246748161572309853)
      ·
        refine ⟨36643417592530560589616195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97715780246748161572309853 36643417592530560589616195)
        ·
          refine ⟨54965126388795840884424293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36643417592530560589616195 54965126388795840884424293)
          ·
            refine ⟨10305961197899220165829555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54965126388795840884424293 10305961197899220165829555)
            ·
              refine ⟨15458941796848830248744333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10305961197899220165829555 15458941796848830248744333)
              ·
                refine ⟨5797103173818311343279125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15458941796848830248744333 5797103173818311343279125)
                ·
                  refine ⟨271739211272733344216209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5797103173818311343279125 271739211272733344216209)
                  ·
                    rfl

theorem cell21_1190723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_1190723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190723 prefixEnd_1190723 := by exact prefixLift 1190723
  have htrace : WordTrace (prefixWord ++ tailWord_1190723) baseStart_1190723 baseEnd_1190723 := by
    simpa [prefixWord, tailWord_1190723, baseEnd_1190723] using wordTrace_append hprefix tailTrace_1190723
  have hstable : (prefixWord ++ tailWord_1190723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190723).length < 2 ^ (prefixWord ++ tailWord_1190723).sum := by decide
  have hdescent : baseEnd_1190723 < baseStart_1190723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190774 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_1190774 : Nat := 118140960795 + 1190774 * 2 ^ 59
def prefixEnd_1190774 : Nat := 4983230072969 + 3 ^ 40 * 1190774 * 2
def baseEnd_1190774 : Nat := 271750850167568588866105

theorem tailTrace_1190774 : CollatzResearch.WordTrace tailWord_1190774 prefixEnd_1190774 271750850167568588866105 := by
  unfold tailWord_1190774
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714443486752290053334711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28954063858691093902236917 2714443486752290053334711)
  ·
    refine ⟨4071665230128435080002067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2714443486752290053334711 4071665230128435080002067)
    ·
      refine ⟨6107497845192652620003101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071665230128435080002067 6107497845192652620003101)
      ·
        refine ⟨2290311691947244732501163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6107497845192652620003101 2290311691947244732501163)
        ·
          refine ⟨3435467537920867098751745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290311691947244732501163 3435467537920867098751745)
          ·
            refine ⟨2576600653440650324063809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435467537920867098751745 2576600653440650324063809)
            ·
              refine ⟨1932450490080487743047857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576600653440650324063809 1932450490080487743047857)
              ·
                refine ⟨1449337867560365807285893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932450490080487743047857 1449337867560365807285893)
                ·
                  refine ⟨271750850167568588866105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449337867560365807285893 271750850167568588866105)
                  ·
                    rfl

theorem cell21_1190774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_1190774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190774 prefixEnd_1190774 := by exact prefixLift 1190774
  have htrace : WordTrace (prefixWord ++ tailWord_1190774) baseStart_1190774 baseEnd_1190774 := by
    simpa [prefixWord, tailWord_1190774, baseEnd_1190774] using wordTrace_append hprefix tailTrace_1190774
  have hstable : (prefixWord ++ tailWord_1190774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190774).length < 2 ^ (prefixWord ++ tailWord_1190774).sum := by decide
  have hdescent : baseEnd_1190774 < baseStart_1190774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190836 : List Nat := [2, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1190836 : Nat := 118140960795 + 1190836 * 2 ^ 59
def prefixEnd_1190836 : Nat := 4983230072969 + 3 ^ 40 * 1190836 * 2
def baseEnd_1190836 : Nat := 271764999412270258832645

theorem tailTrace_1190836 : CollatzResearch.WordTrace tailWord_1190836 prefixEnd_1190836 271764999412270258832645 := by
  unfold tailWord_1190836
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716678556906012721056181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28955571409208016961408241 21716678556906012721056181)
  ·
    refine ⟨2035938614709938692599017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21716678556906012721056181 2035938614709938692599017)
    ·
      refine ⟨1526953961032454019449263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2035938614709938692599017 1526953961032454019449263)
      ·
        refine ⟨2290430941548681029173895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526953961032454019449263 2290430941548681029173895)
        ·
          refine ⟨3435646412323021543760843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290430941548681029173895 3435646412323021543760843)
          ·
            refine ⟨5153469618484532315641265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435646412323021543760843 5153469618484532315641265)
            ·
              refine ⟨3865102213863399236730949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5153469618484532315641265 3865102213863399236730949)
              ·
                refine ⟨724706665099387356887053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3865102213863399236730949 724706665099387356887053)
                ·
                  refine ⟨271764999412270258832645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724706665099387356887053 271764999412270258832645)
                  ·
                    rfl

theorem cell21_1190836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1190836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190836 prefixEnd_1190836 := by exact prefixLift 1190836
  have htrace : WordTrace (prefixWord ++ tailWord_1190836) baseStart_1190836 baseEnd_1190836 := by
    simpa [prefixWord, tailWord_1190836, baseEnd_1190836] using wordTrace_append hprefix tailTrace_1190836
  have hstable : (prefixWord ++ tailWord_1190836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190836).length < 2 ^ (prefixWord ++ tailWord_1190836).sum := by decide
  have hdescent : baseEnd_1190836 < baseStart_1190836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190895 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 3]
def baseStart_1190895 : Nat := 118140960795 + 1190895 * 2 ^ 59
def prefixEnd_1190895 : Nat := 4983230072969 + 3 ^ 40 * 1190895 * 2
def baseEnd_1190895 : Nat := 271778464016099267349191

theorem tailTrace_1190895 : CollatzResearch.WordTrace tailWord_1190895 prefixEnd_1190895 271778464016099267349191 := by
  unfold tailWord_1190895
  simp only [CollatzResearch.WordTrace]
  refine ⟨43435509020598278518510139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28957006013732185679006759 43435509020598278518510139)
  ·
    refine ⟨65153263530897417777765209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43435509020598278518510139 65153263530897417777765209)
    ·
      refine ⟨48864947648173063333323907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65153263530897417777765209 48864947648173063333323907)
      ·
        refine ⟨73297421472259594999985861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48864947648173063333323907 73297421472259594999985861)
        ·
          refine ⟨13743266526048674062497349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73297421472259594999985861 13743266526048674062497349)
          ·
            refine ⟨2576862473634126386718253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13743266526048674062497349 2576862473634126386718253)
            ·
              refine ⟨966323427612797395019345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2576862473634126386718253 966323427612797395019345)
              ·
                refine ⟨724742570709598046264509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 966323427612797395019345 724742570709598046264509)
                ·
                  refine ⟨271778464016099267349191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724742570709598046264509 271778464016099267349191)
                  ·
                    rfl

theorem cell21_1190895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 3].length) (baseStart_1190895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190895 prefixEnd_1190895 := by exact prefixLift 1190895
  have htrace : WordTrace (prefixWord ++ tailWord_1190895) baseStart_1190895 baseEnd_1190895 := by
    simpa [prefixWord, tailWord_1190895, baseEnd_1190895] using wordTrace_append hprefix tailTrace_1190895
  have hstable : (prefixWord ++ tailWord_1190895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190895).length < 2 ^ (prefixWord ++ tailWord_1190895).sum := by decide
  have hdescent : baseEnd_1190895 < baseStart_1190895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1190968 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_1190968 : Nat := 118140960795 + 1190968 * 2 ^ 59
def prefixEnd_1190968 : Nat := 4983230072969 + 3 ^ 40 * 1190968 * 2
def baseEnd_1190968 : Nat := 271795123610667362632375

theorem tailTrace_1190968 : CollatzResearch.WordTrace tailWord_1190968 prefixEnd_1190968 271795123610667362632375 := by
  unfold tailWord_1190968
  simp only [CollatzResearch.WordTrace]
  refine ⟨21719085774666905992958779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28958781032889207990611705 21719085774666905992958779)
  ·
    refine ⟨32578628662000358989438169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21719085774666905992958779 32578628662000358989438169)
    ·
      refine ⟨24433971496500269242078627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32578628662000358989438169 24433971496500269242078627)
      ·
        refine ⟨36650957244750403863117941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24433971496500269242078627 36650957244750403863117941)
        ·
          refine ⟨3436027241695350362167307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36650957244750403863117941 3436027241695350362167307)
          ·
            refine ⟨5154040862543025543250961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436027241695350362167307 5154040862543025543250961)
            ·
              refine ⟨3865530646907269157438221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154040862543025543250961 3865530646907269157438221)
              ·
                refine ⟨1449573992590225934039333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865530646907269157438221 1449573992590225934039333)
                ·
                  refine ⟨271795123610667362632375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449573992590225934039333 271795123610667362632375)
                  ·
                    rfl

theorem cell21_1190968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_1190968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1190968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1190968 prefixEnd_1190968 := by exact prefixLift 1190968
  have htrace : WordTrace (prefixWord ++ tailWord_1190968) baseStart_1190968 baseEnd_1190968 := by
    simpa [prefixWord, tailWord_1190968, baseEnd_1190968] using wordTrace_append hprefix tailTrace_1190968
  have hstable : (prefixWord ++ tailWord_1190968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1190968).length < 2 ^ (prefixWord ++ tailWord_1190968).sum := by decide
  have hdescent : baseEnd_1190968 < baseStart_1190968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1190968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191013 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1191013 : Nat := 118140960795 + 1191013 * 2 ^ 59
def prefixEnd_1191013 : Nat := 4983230072969 + 3 ^ 40 * 1191013 * 2
def baseEnd_1191013 : Nat := 271805393223757284382283

theorem tailTrace_1191013 : CollatzResearch.WordTrace tailWord_1191013 prefixEnd_1191013 271805393223757284382283 := by
  unfold tailWord_1191013
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439812834170784671305693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28959875222780523114203795 43439812834170784671305693)
  ·
    refine ⟨16289929812814044251739635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43439812834170784671305693 16289929812814044251739635)
    ·
      refine ⟨24434894719221066377609453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16289929812814044251739635 24434894719221066377609453)
      ·
        refine ⟨9163085519707899891603545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24434894719221066377609453 9163085519707899891603545)
        ·
          refine ⟨6872314139780924918702659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9163085519707899891603545 6872314139780924918702659)
          ·
            refine ⟨10308471209671387378053989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6872314139780924918702659 10308471209671387378053989)
            ·
              refine ⟨1932838351813385133385123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10308471209671387378053989 1932838351813385133385123)
              ·
                refine ⟨2899257527720077700077685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932838351813385133385123 2899257527720077700077685)
                ·
                  refine ⟨271805393223757284382283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2899257527720077700077685 271805393223757284382283)
                  ·
                    rfl

theorem cell21_1191013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1191013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191013 prefixEnd_1191013 := by exact prefixLift 1191013
  have htrace : WordTrace (prefixWord ++ tailWord_1191013) baseStart_1191013 baseEnd_1191013 := by
    simpa [prefixWord, tailWord_1191013, baseEnd_1191013] using wordTrace_append hprefix tailTrace_1191013
  have hstable : (prefixWord ++ tailWord_1191013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191013).length < 2 ^ (prefixWord ++ tailWord_1191013).sum := by decide
  have hdescent : baseEnd_1191013 < baseStart_1191013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191058 : List Nat := [3, 2, 3, 1, 1, 2, 9]
def baseStart_1191058 : Nat := 118140960795 + 1191058 * 2 ^ 59
def prefixEnd_1191058 : Nat := 4983230072969 + 3 ^ 40 * 1191058 * 2
def baseEnd_1191058 : Nat := 30201740315205245125799

theorem tailTrace_1191058 : CollatzResearch.WordTrace tailWord_1191058 prefixEnd_1191058 30201740315205245125799 := by
  unfold tailWord_1191058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10860363529751939339173457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28960969412671838237795885 10860363529751939339173457)
  ·
    refine ⟨8145272647313954504380093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10860363529751939339173457 8145272647313954504380093)
    ·
      refine ⟨3054477242742732939142535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8145272647313954504380093 3054477242742732939142535)
      ·
        refine ⟨4581715864114099408713803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054477242742732939142535 4581715864114099408713803)
        ·
          refine ⟨6872573796171149113070705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4581715864114099408713803 6872573796171149113070705)
          ·
            refine ⟨5154430347128361834803029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6872573796171149113070705 5154430347128361834803029)
            ·
              refine ⟨30201740315205245125799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5154430347128361834803029 30201740315205245125799)
              ·
                rfl

theorem cell21_1191058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 9].length) (baseStart_1191058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191058 prefixEnd_1191058 := by exact prefixLift 1191058
  have htrace : WordTrace (prefixWord ++ tailWord_1191058) baseStart_1191058 baseEnd_1191058 := by
    simpa [prefixWord, tailWord_1191058, baseEnd_1191058] using wordTrace_append hprefix tailTrace_1191058
  have hstable : (prefixWord ++ tailWord_1191058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191058).length < 2 ^ (prefixWord ++ tailWord_1191058).sum := by decide
  have hdescent : baseEnd_1191058 < baseStart_1191058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191148 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_1191148 : Nat := 118140960795 + 1191148 * 2 ^ 59
def prefixEnd_1191148 : Nat := 4983230072969 + 3 ^ 40 * 1191148 * 2
def baseEnd_1191148 : Nat := 271836202063027049632007

theorem tailTrace_1191148 : CollatzResearch.WordTrace tailWord_1191148 prefixEnd_1191148 271836202063027049632007 := by
  unfold tailWord_1191148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21722368344340851363735049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28963157792454468484980065 21722368344340851363735049)
  ·
    refine ⟨16291776258255638522801287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21722368344340851363735049 16291776258255638522801287)
    ·
      refine ⟨24437664387383457784201931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16291776258255638522801287 24437664387383457784201931)
      ·
        refine ⟨36656496581075186676302897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24437664387383457784201931 36656496581075186676302897)
        ·
          refine ⟨27492372435806390007227173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36656496581075186676302897 27492372435806390007227173)
          ·
            refine ⟨5154819831713698126355095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27492372435806390007227173 5154819831713698126355095)
            ·
              refine ⟨7732229747570547189532643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154819831713698126355095 7732229747570547189532643)
              ·
                refine ⟨11598344621355820784298965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7732229747570547189532643 11598344621355820784298965)
                ·
                  refine ⟨271836202063027049632007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11598344621355820784298965 271836202063027049632007)
                  ·
                    rfl

theorem cell21_1191148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_1191148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191148 prefixEnd_1191148 := by exact prefixLift 1191148
  have htrace : WordTrace (prefixWord ++ tailWord_1191148) baseStart_1191148 baseEnd_1191148 := by
    simpa [prefixWord, tailWord_1191148, baseEnd_1191148] using wordTrace_append hprefix tailTrace_1191148
  have hstable : (prefixWord ++ tailWord_1191148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191148).length < 2 ^ (prefixWord ++ tailWord_1191148).sum := by decide
  have hdescent : baseEnd_1191148 < baseStart_1191148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191151 : List Nat := [1, 1, 2, 1, 7, 1, 3, 5]
def baseStart_1191151 : Nat := 118140960795 + 1191151 * 2 ^ 59
def prefixEnd_1191151 : Nat := 4983230072969 + 3 ^ 40 * 1191151 * 2
def baseEnd_1191151 : Nat := 90612295567966570360667

theorem tailTrace_1191151 : CollatzResearch.WordTrace tailWord_1191151 prefixEnd_1191151 90612295567966570360667 := by
  unfold tailWord_1191151
  simp only [CollatzResearch.WordTrace]
  refine ⟨43444846107670834239829307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28963230738447222826552871 43444846107670834239829307)
  ·
    refine ⟨65167269161506251359743961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43444846107670834239829307 65167269161506251359743961)
    ·
      refine ⟨48875451871129688519807971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65167269161506251359743961 48875451871129688519807971)
      ·
        refine ⟨73313177806694532779711957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48875451871129688519807971 73313177806694532779711957)
        ·
          refine ⟨1718277604844403112024499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 73313177806694532779711957 1718277604844403112024499)
          ·
            refine ⟨2577416407266604668036749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718277604844403112024499 2577416407266604668036749)
            ·
              refine ⟨966531152724976750513781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2577416407266604668036749 966531152724976750513781)
              ·
                refine ⟨90612295567966570360667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966531152724976750513781 90612295567966570360667)
                ·
                  rfl

theorem cell21_1191151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 5].length) (baseStart_1191151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191151 prefixEnd_1191151 := by exact prefixLift 1191151
  have htrace : WordTrace (prefixWord ++ tailWord_1191151) baseStart_1191151 baseEnd_1191151 := by
    simpa [prefixWord, tailWord_1191151, baseEnd_1191151] using wordTrace_append hprefix tailTrace_1191151
  have hstable : (prefixWord ++ tailWord_1191151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191151).length < 2 ^ (prefixWord ++ tailWord_1191151).sum := by decide
  have hdescent : baseEnd_1191151 < baseStart_1191151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191179 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_1191179 : Nat := 118140960795 + 1191179 * 2 ^ 59
def prefixEnd_1191179 : Nat := 4983230072969 + 3 ^ 40 * 1191179 * 2
def baseEnd_1191179 : Nat := 271843276685377884615277

theorem tailTrace_1191179 : CollatzResearch.WordTrace tailWord_1191179 prefixEnd_1191179 271843276685377884615277 := by
  unfold tailWord_1191179
  simp only [CollatzResearch.WordTrace]
  refine ⟨43445867351569395021848591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28963911567712930014565727 43445867351569395021848591)
  ·
    refine ⟨65168801027354092532772887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43445867351569395021848591 65168801027354092532772887)
    ·
      refine ⟨97753201541031138799159331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65168801027354092532772887 97753201541031138799159331)
      ·
        refine ⟨146629802311546708198738997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97753201541031138799159331 146629802311546708198738997)
        ·
          refine ⟨13746543966707503893631781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146629802311546708198738997 13746543966707503893631781)
          ·
            refine ⟨2577476993757656980055959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13746543966707503893631781 2577476993757656980055959)
            ·
              refine ⟨3866215490636485470083939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577476993757656980055959 3866215490636485470083939)
              ·
                refine ⟨5799323235954728205125909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866215490636485470083939 5799323235954728205125909)
                ·
                  refine ⟨271843276685377884615277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5799323235954728205125909 271843276685377884615277)
                  ·
                    rfl

theorem cell21_1191179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_1191179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191179 prefixEnd_1191179 := by exact prefixLift 1191179
  have htrace : WordTrace (prefixWord ++ tailWord_1191179) baseStart_1191179 baseEnd_1191179 := by
    simpa [prefixWord, tailWord_1191179, baseEnd_1191179] using wordTrace_append hprefix tailTrace_1191179
  have hstable : (prefixWord ++ tailWord_1191179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191179).length < 2 ^ (prefixWord ++ tailWord_1191179).sum := by decide
  have hdescent : baseEnd_1191179 < baseStart_1191179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191182 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_1191182 : Nat := 118140960795 + 1191182 * 2 ^ 59
def prefixEnd_1191182 : Nat := 4983230072969 + 3 ^ 40 * 1191182 * 2
def baseEnd_1191182 : Nat := 271843961326250546065271

theorem tailTrace_1191182 : CollatzResearch.WordTrace tailWord_1191182 prefixEnd_1191182 271843961326250546065271 := by
  unfold tailWord_1191182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5430747096319815816775975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28963984513705684356138533 5430747096319815816775975)
  ·
    refine ⟨8146120644479723725163963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5430747096319815816775975 8146120644479723725163963)
    ·
      refine ⟨12219180966719585587745945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8146120644479723725163963 12219180966719585587745945)
      ·
        refine ⟨9164385725039689190809459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12219180966719585587745945 9164385725039689190809459)
        ·
          refine ⟨13746578587559533786214189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9164385725039689190809459 13746578587559533786214189)
          ·
            refine ⟨5154966970334825169830321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13746578587559533786214189 5154966970334825169830321)
            ·
              refine ⟨3866225227751118877372741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154966970334825169830321 3866225227751118877372741)
              ·
                refine ⟨724917230203334789507389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3866225227751118877372741 724917230203334789507389)
                ·
                  refine ⟨271843961326250546065271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724917230203334789507389 271843961326250546065271)
                  ·
                    rfl

theorem cell21_1191182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_1191182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191182 prefixEnd_1191182 := by exact prefixLift 1191182
  have htrace : WordTrace (prefixWord ++ tailWord_1191182) baseStart_1191182 baseEnd_1191182 := by
    simpa [prefixWord, tailWord_1191182, baseEnd_1191182] using wordTrace_append hprefix tailTrace_1191182
  have hstable : (prefixWord ++ tailWord_1191182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191182).length < 2 ^ (prefixWord ++ tailWord_1191182).sum := by decide
  have hdescent : baseEnd_1191182 < baseStart_1191182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191241 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 3]
def baseStart_1191241 : Nat := 118140960795 + 1191241 * 2 ^ 59
def prefixEnd_1191241 : Nat := 4983230072969 + 3 ^ 40 * 1191241 * 2
def baseEnd_1191241 : Nat := 271857425930079554581817

theorem tailTrace_1191241 : CollatzResearch.WordTrace tailWord_1191241 prefixEnd_1191241 271857425930079554581817 := by
  unfold tailWord_1191241
  simp only [CollatzResearch.WordTrace]
  refine ⟨43448128677344779610605577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28965419118229853073737051 43448128677344779610605577)
  ·
    refine ⟨32586096508008584707954183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43448128677344779610605577 32586096508008584707954183)
    ·
      refine ⟨48879144762012877061931275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32586096508008584707954183 48879144762012877061931275)
      ·
        refine ⟨73318717143019315592896913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48879144762012877061931275 73318717143019315592896913)
        ·
          refine ⟨54989037857264486694672685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73318717143019315592896913 54989037857264486694672685)
          ·
            refine ⟨20620889196474182510502257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54989037857264486694672685 20620889196474182510502257)
            ·
              refine ⟨15465666897355636882876693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20620889196474182510502257 15465666897355636882876693)
              ·
                refine ⟨724953135813545478884845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15465666897355636882876693 724953135813545478884845)
                ·
                  refine ⟨271857425930079554581817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 724953135813545478884845 271857425930079554581817)
                  ·
                    rfl

theorem cell21_1191241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_1191241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191241 prefixEnd_1191241 := by exact prefixLift 1191241
  have htrace : WordTrace (prefixWord ++ tailWord_1191241) baseStart_1191241 baseEnd_1191241 := by
    simpa [prefixWord, tailWord_1191241, baseEnd_1191241] using wordTrace_append hprefix tailTrace_1191241
  have hstable : (prefixWord ++ tailWord_1191241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191241).length < 2 ^ (prefixWord ++ tailWord_1191241).sum := by decide
  have hdescent : baseEnd_1191241 < baseStart_1191241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191269 : List Nat := [1, 3, 1, 3, 1, 2, 1, 9]
def baseStart_1191269 : Nat := 118140960795 + 1191269 * 2 ^ 59
def prefixEnd_1191269 : Nat := 4983230072969 + 3 ^ 40 * 1191269 * 2
def baseEnd_1191269 : Nat := 90621271970519242705031

theorem tailTrace_1191269 : CollatzResearch.WordTrace tailWord_1191269 prefixEnd_1191269 90621271970519242705031 := by
  unfold tailWord_1191269
  simp only [CollatzResearch.WordTrace]
  refine ⟨43449149921243340392624861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28966099947495560261749907 43449149921243340392624861)
  ·
    refine ⟨16293431220466252647234323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43449149921243340392624861 16293431220466252647234323)
    ·
      refine ⟨24440146830699378970851485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16293431220466252647234323 24440146830699378970851485)
      ·
        refine ⟨9165055061512267114069307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24440146830699378970851485 9165055061512267114069307)
        ·
          refine ⟨13747582592268400671103961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9165055061512267114069307 13747582592268400671103961)
          ·
            refine ⟨10310686944201300503327971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13747582592268400671103961 10310686944201300503327971)
            ·
              refine ⟨15466030416301950754991957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10310686944201300503327971 15466030416301950754991957)
              ·
                refine ⟨90621271970519242705031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15466030416301950754991957 90621271970519242705031)
                ·
                  rfl

theorem cell21_1191269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_1191269 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191269 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191269 prefixEnd_1191269 := by exact prefixLift 1191269
  have htrace : WordTrace (prefixWord ++ tailWord_1191269) baseStart_1191269 baseEnd_1191269 := by
    simpa [prefixWord, tailWord_1191269, baseEnd_1191269] using wordTrace_append hprefix tailTrace_1191269
  have hstable : (prefixWord ++ tailWord_1191269).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191269).length < 2 ^ (prefixWord ++ tailWord_1191269).sum := by decide
  have hdescent : baseEnd_1191269 < baseStart_1191269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191345 : List Nat := [1, 2, 2, 4, 1, 1, 10]
def baseStart_1191345 : Nat := 118140960795 + 1191345 * 2 ^ 59
def prefixEnd_1191345 : Nat := 4983230072969 + 3 ^ 40 * 1191345 * 2
def baseEnd_1191345 : Nat := 30209017794110942760919

theorem tailTrace_1191345 : CollatzResearch.WordTrace tailWord_1191345 prefixEnd_1191345 30209017794110942760919 := by
  unfold tailWord_1191345
  simp only [CollatzResearch.WordTrace]
  refine ⟨43451921868968005372391489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28967947912645336914927659 43451921868968005372391489)
  ·
    refine ⟨32588941401726004029293617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43451921868968005372391489 32588941401726004029293617)
    ·
      refine ⟨24441706051294503021970213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32588941401726004029293617 24441706051294503021970213)
      ·
        refine ⟨4582819884617719316619415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24441706051294503021970213 4582819884617719316619415)
        ·
          refine ⟨6874229826926578974929123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4582819884617719316619415 6874229826926578974929123)
          ·
            refine ⟨10311344740389868462393685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6874229826926578974929123 10311344740389868462393685)
            ·
              refine ⟨30209017794110942760919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10311344740389868462393685 30209017794110942760919)
              ·
                rfl

theorem cell21_1191345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 10].length) (baseStart_1191345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191345 prefixEnd_1191345 := by exact prefixLift 1191345
  have htrace : WordTrace (prefixWord ++ tailWord_1191345) baseStart_1191345 baseEnd_1191345 := by
    simpa [prefixWord, tailWord_1191345, baseEnd_1191345] using wordTrace_append hprefix tailTrace_1191345
  have hstable : (prefixWord ++ tailWord_1191345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191345).length < 2 ^ (prefixWord ++ tailWord_1191345).sum := by decide
  have hdescent : baseEnd_1191345 < baseStart_1191345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191410 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_1191410 : Nat := 118140960795 + 1191410 * 2 ^ 59
def prefixEnd_1191410 : Nat := 4983230072969 + 3 ^ 40 * 1191410 * 2
def baseEnd_1191410 : Nat := 271895994032572816264805

theorem tailTrace_1191410 : CollatzResearch.WordTrace tailWord_1191410 prefixEnd_1191410 271895994032572816264805 := by
  unfold tailWord_1191410
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863573153433130368376921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28969528409155014315671789 10863573153433130368376921)
  ·
    refine ⟨8147679865074847776282691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10863573153433130368376921 8147679865074847776282691)
    ·
      refine ⟨12221519797612271664424037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8147679865074847776282691 12221519797612271664424037)
      ·
        refine ⟨2291534962052300937079507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12221519797612271664424037 2291534962052300937079507)
        ·
          refine ⟨3437302443078451405619261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291534962052300937079507 3437302443078451405619261)
          ·
            refine ⟨1288988416154419277107223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3437302443078451405619261 1288988416154419277107223)
            ·
              refine ⟨1933482624231628915660835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1288988416154419277107223 1933482624231628915660835)
              ·
                refine ⟨2900223936347443373491253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933482624231628915660835 2900223936347443373491253)
                ·
                  refine ⟨271895994032572816264805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2900223936347443373491253 271895994032572816264805)
                  ·
                    rfl

theorem cell21_1191410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_1191410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191410 prefixEnd_1191410 := by exact prefixLift 1191410
  have htrace : WordTrace (prefixWord ++ tailWord_1191410) baseStart_1191410 baseEnd_1191410 := by
    simpa [prefixWord, tailWord_1191410, baseEnd_1191410] using wordTrace_append hprefix tailTrace_1191410
  have hstable : (prefixWord ++ tailWord_1191410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191410).length < 2 ^ (prefixWord ++ tailWord_1191410).sum := by decide
  have hdescent : baseEnd_1191410 < baseStart_1191410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191421 : List Nat := [1, 4, 1, 1, 1, 4, 1, 8]
def baseStart_1191421 : Nat := 118140960795 + 1191421 * 2 ^ 59
def prefixEnd_1191421 : Nat := 4983230072969 + 3 ^ 40 * 1191421 * 2
def baseEnd_1191421 : Nat := 90632834794146413860483

theorem tailTrace_1191421 : CollatzResearch.WordTrace tailWord_1191421 prefixEnd_1191421 90632834794146413860483 := by
  unfold tailWord_1191421
  simp only [CollatzResearch.WordTrace]
  refine ⟨43454693816692670352158117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28969795877795113568105411 43454693816692670352158117)
  ·
    refine ⟨8147755090629875691029647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43454693816692670352158117 8147755090629875691029647)
    ·
      refine ⟨12221632635944813536544471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8147755090629875691029647 12221632635944813536544471)
      ·
        refine ⟨18332448953917220304816707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12221632635944813536544471 18332448953917220304816707)
        ·
          refine ⟨27498673430875830457225061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18332448953917220304816707 27498673430875830457225061)
          ·
            refine ⟨5156001268289218210729699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27498673430875830457225061 5156001268289218210729699)
            ·
              refine ⟨7734001902433827316094549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156001268289218210729699 7734001902433827316094549)
              ·
                refine ⟨90632834794146413860483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7734001902433827316094549 90632834794146413860483)
                ·
                  rfl

theorem cell21_1191421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_1191421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191421 prefixEnd_1191421 := by exact prefixLift 1191421
  have htrace : WordTrace (prefixWord ++ tailWord_1191421) baseStart_1191421 baseEnd_1191421 := by
    simpa [prefixWord, tailWord_1191421, baseEnd_1191421] using wordTrace_append hprefix tailTrace_1191421
  have hstable : (prefixWord ++ tailWord_1191421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191421).length < 2 ^ (prefixWord ++ tailWord_1191421).sum := by decide
  have hdescent : baseEnd_1191421 < baseStart_1191421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191517 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1191517 : Nat := 118140960795 + 1191517 * 2 ^ 59
def prefixEnd_1191517 : Nat := 4983230072969 + 3 ^ 40 * 1191517 * 2
def baseEnd_1191517 : Nat := 271920412890364407981253

theorem tailTrace_1191517 : CollatzResearch.WordTrace tailWord_1191517 prefixEnd_1191517 271920412890364407981253 := by
  unfold tailWord_1191517
  simp only [CollatzResearch.WordTrace]
  refine ⟨43458195224344878747652805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28972130149563252498435203 43458195224344878747652805)
  ·
    refine ⟨8148411604564664765184901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43458195224344878747652805 8148411604564664765184901)
    ·
      refine ⟨1527827175855874643472169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8148411604564664765184901 1527827175855874643472169)
      ·
        refine ⟨1145870381891905982604127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1527827175855874643472169 1145870381891905982604127)
        ·
          refine ⟨1718805572837858973906191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1145870381891905982604127 1718805572837858973906191)
          ·
            refine ⟨2578208359256788460859287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718805572837858973906191 2578208359256788460859287)
            ·
              refine ⟨3867312538885182691288931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578208359256788460859287 3867312538885182691288931)
              ·
                refine ⟨5800968808327774036933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867312538885182691288931 5800968808327774036933397)
                ·
                  refine ⟨271920412890364407981253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5800968808327774036933397 271920412890364407981253)
                  ·
                    rfl

theorem cell21_1191517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1191517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191517 prefixEnd_1191517 := by exact prefixLift 1191517
  have htrace : WordTrace (prefixWord ++ tailWord_1191517) baseStart_1191517 baseEnd_1191517 := by
    simpa [prefixWord, tailWord_1191517, baseEnd_1191517] using wordTrace_append hprefix tailTrace_1191517
  have hstable : (prefixWord ++ tailWord_1191517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191517).length < 2 ^ (prefixWord ++ tailWord_1191517).sum := by decide
  have hdescent : baseEnd_1191517 < baseStart_1191517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191562 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 3]
def baseStart_1191562 : Nat := 118140960795 + 1191562 * 2 ^ 59
def prefixEnd_1191562 : Nat := 4983230072969 + 3 ^ 40 * 1191562 * 2
def baseEnd_1191562 : Nat := 271930682503454329731161

theorem tailTrace_1191562 : CollatzResearch.WordTrace tailWord_1191562 prefixEnd_1191562 271930682503454329731161 := by
  unfold tailWord_1191562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10864959127295462858260235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28973224339454567622027293 10864959127295462858260235)
  ·
    refine ⟨16297438690943194287390353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10864959127295462858260235 16297438690943194287390353)
    ·
      refine ⟨12223079018207395715542765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16297438690943194287390353 12223079018207395715542765)
      ·
        refine ⟨4583654631827773393328537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12223079018207395715542765 4583654631827773393328537)
        ·
          refine ⟨3437740973870830044996403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4583654631827773393328537 3437740973870830044996403)
          ·
            refine ⟨5156611460806245067494605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437740973870830044996403 5156611460806245067494605)
            ·
              refine ⟨1933729297802341900310477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5156611460806245067494605 1933729297802341900310477)
              ·
                refine ⟨725148486675878212616429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1933729297802341900310477 725148486675878212616429)
                ·
                  refine ⟨271930682503454329731161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725148486675878212616429 271930682503454329731161)
                  ·
                    rfl

theorem cell21_1191562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 3].length) (baseStart_1191562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191562 prefixEnd_1191562 := by exact prefixLift 1191562
  have htrace : WordTrace (prefixWord ++ tailWord_1191562) baseStart_1191562 baseEnd_1191562 := by
    simpa [prefixWord, tailWord_1191562, baseEnd_1191562] using wordTrace_append hprefix tailTrace_1191562
  have hstable : (prefixWord ++ tailWord_1191562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191562).length < 2 ^ (prefixWord ++ tailWord_1191562).sum := by decide
  have hdescent : baseEnd_1191562 < baseStart_1191562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191666 : List Nat := [3, 2, 1, 3, 1, 1, 5, 5]
def baseStart_1191666 : Nat := 118140960795 + 1191666 * 2 ^ 59
def prefixEnd_1191666 : Nat := 4983230072969 + 3 ^ 40 * 1191666 * 2
def baseEnd_1191666 : Nat := 90651472240124419999205

theorem tailTrace_1191666 : CollatzResearch.WordTrace tailWord_1191666 prefixEnd_1191666 90651472240124419999205 := by
  unfold tailWord_1191666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10865907425201269298706713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28975753133870051463217901 10865907425201269298706713)
  ·
    refine ⟨8149430568900951974030035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10865907425201269298706713 8149430568900951974030035)
    ·
      refine ⟨12224145853351427961045053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8149430568900951974030035 12224145853351427961045053)
      ·
        refine ⟨4584054695006785485391895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12224145853351427961045053 4584054695006785485391895)
        ·
          refine ⟨6876082042510178228087843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584054695006785485391895 6876082042510178228087843)
          ·
            refine ⟨10314123063765267342131765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6876082042510178228087843 10314123063765267342131765)
            ·
              refine ⟨966949037227993813324853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10314123063765267342131765 966949037227993813324853)
              ·
                refine ⟨90651472240124419999205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966949037227993813324853 90651472240124419999205)
                ·
                  rfl

theorem cell21_1191666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_1191666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191666 prefixEnd_1191666 := by exact prefixLift 1191666
  have htrace : WordTrace (prefixWord ++ tailWord_1191666) baseStart_1191666 baseEnd_1191666 := by
    simpa [prefixWord, tailWord_1191666, baseEnd_1191666] using wordTrace_append hprefix tailTrace_1191666
  have hstable : (prefixWord ++ tailWord_1191666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191666).length < 2 ^ (prefixWord ++ tailWord_1191666).sum := by decide
  have hdescent : baseEnd_1191666 < baseStart_1191666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191731 : List Nat := [1, 1, 1, 2, 8, 1, 1, 3, 3]
def baseStart_1191731 : Nat := 118140960795 + 1191731 * 2 ^ 59
def prefixEnd_1191731 : Nat := 4983230072969 + 3 ^ 40 * 1191731 * 2
def baseEnd_1191731 : Nat := 271969250605947591414149

theorem tailTrace_1191731 : CollatzResearch.WordTrace tailWord_1191731 prefixEnd_1191731 271969250605947591414149 := by
  unfold tailWord_1191731
  simp only [CollatzResearch.WordTrace]
  refine ⟨43466000445569593295943047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28977333630379728863962031 43466000445569593295943047)
  ·
    refine ⟨65199000668354389943914571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43466000445569593295943047 65199000668354389943914571)
    ·
      refine ⟨97798501002531584915871857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65199000668354389943914571 97798501002531584915871857)
      ·
        refine ⟨73348875751898688686903893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97798501002531584915871857 73348875751898688686903893)
        ·
          refine ⟨859557137717562758049655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 73348875751898688686903893 859557137717562758049655)
          ·
            refine ⟨1289335706576344137074483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859557137717562758049655 1289335706576344137074483)
            ·
              refine ⟨1934003559864516205611725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289335706576344137074483 1934003559864516205611725)
              ·
                refine ⟨725251334949193577104397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934003559864516205611725 725251334949193577104397)
                ·
                  refine ⟨271969250605947591414149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725251334949193577104397 271969250605947591414149)
                  ·
                    rfl

theorem cell21_1191731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 3, 3].length) (baseStart_1191731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191731 prefixEnd_1191731 := by exact prefixLift 1191731
  have htrace : WordTrace (prefixWord ++ tailWord_1191731) baseStart_1191731 baseEnd_1191731 := by
    simpa [prefixWord, tailWord_1191731, baseEnd_1191731] using wordTrace_append hprefix tailTrace_1191731
  have hstable : (prefixWord ++ tailWord_1191731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191731).length < 2 ^ (prefixWord ++ tailWord_1191731).sum := by decide
  have hdescent : baseEnd_1191731 < baseStart_1191731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191742 : List Nat := [4, 2, 1, 2, 2, 3, 7]
def baseStart_1191742 : Nat := 118140960795 + 1191742 * 2 ^ 59
def prefixEnd_1191742 : Nat := 4983230072969 + 3 ^ 40 * 1191742 * 2
def baseEnd_1191742 : Nat := 30219084550646001858977

theorem tailTrace_1191742 : CollatzResearch.WordTrace tailWord_1191742 prefixEnd_1191742 30219084550646001858977 := by
  unfold tailWord_1191742
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433300206066217771824185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28977601099019828116395653 5433300206066217771824185)
  ·
    refine ⟨4074975154549663328868139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5433300206066217771824185 4074975154549663328868139)
    ·
      refine ⟨6112462731824494993302209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4074975154549663328868139 6112462731824494993302209)
      ·
        refine ⟨4584347048868371244976657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6112462731824494993302209 4584347048868371244976657)
        ·
          refine ⟨3438260286651278433732493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4584347048868371244976657 3438260286651278433732493)
          ·
            refine ⟨1289347607494229412649685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3438260286651278433732493 1289347607494229412649685)
            ·
              refine ⟨30219084550646001858977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1289347607494229412649685 30219084550646001858977)
              ·
                rfl

theorem cell21_1191742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 7].length) (baseStart_1191742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191742 prefixEnd_1191742 := by exact prefixLift 1191742
  have htrace : WordTrace (prefixWord ++ tailWord_1191742) baseStart_1191742 baseEnd_1191742 := by
    simpa [prefixWord, tailWord_1191742, baseEnd_1191742] using wordTrace_append hprefix tailTrace_1191742
  have hstable : (prefixWord ++ tailWord_1191742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191742).length < 2 ^ (prefixWord ++ tailWord_1191742).sum := by decide
  have hdescent : baseEnd_1191742 < baseStart_1191742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191880 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_1191880 : Nat := 118140960795 + 1191880 * 2 ^ 59
def prefixEnd_1191880 : Nat := 4983230072969 + 3 ^ 40 * 1191880 * 2
def baseEnd_1191880 : Nat := 272003254435956443430511

theorem tailTrace_1191880 : CollatzResearch.WordTrace tailWord_1191880 prefixEnd_1191880 272003254435956443430511 := by
  unfold tailWord_1191880
  simp only [CollatzResearch.WordTrace]
  refine ⟨21735717461014895871558547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28980956614686527828744729 21735717461014895871558547)
  ·
    refine ⟨32603576191522343807337821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21735717461014895871558547 32603576191522343807337821)
    ·
      refine ⟨12226341071820878927751683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32603576191522343807337821 12226341071820878927751683)
      ·
        refine ⟨18339511607731318391627525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12226341071820878927751683 18339511607731318391627525)
        ·
          refine ⟨3438658426449622198430161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18339511607731318391627525 3438658426449622198430161)
          ·
            refine ⟨2578993819837216648822621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3438658426449622198430161 2578993819837216648822621)
            ·
              refine ⟨967122682438956243308483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2578993819837216648822621 967122682438956243308483)
              ·
                refine ⟨1450684023658434364962725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967122682438956243308483 1450684023658434364962725)
                ·
                  refine ⟨272003254435956443430511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450684023658434364962725 272003254435956443430511)
                  ·
                    rfl

theorem cell21_1191880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_1191880 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191880 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191880 prefixEnd_1191880 := by exact prefixLift 1191880
  have htrace : WordTrace (prefixWord ++ tailWord_1191880) baseStart_1191880 baseEnd_1191880 := by
    simpa [prefixWord, tailWord_1191880, baseEnd_1191880] using wordTrace_append hprefix tailTrace_1191880
  have hstable : (prefixWord ++ tailWord_1191880).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191880).length < 2 ^ (prefixWord ++ tailWord_1191880).sum := by decide
  have hdescent : baseEnd_1191880 < baseStart_1191880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1191976 : List Nat := [2, 1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_1191976 : Nat := 118140960795 + 1191976 * 2 ^ 59
def prefixEnd_1191976 : Nat := 4983230072969 + 3 ^ 40 * 1191976 * 2
def baseEnd_1191976 : Nat := 272025162943881609830315

theorem tailTrace_1191976 : CollatzResearch.WordTrace tailWord_1191976 prefixEnd_1191976 272025162943881609830315 := by
  unfold tailWord_1191976
  simp only [CollatzResearch.WordTrace]
  refine ⟨21737468164841000069305891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28983290886454666759074521 21737468164841000069305891)
  ·
    refine ⟨32606202247261500103958837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21737468164841000069305891 32606202247261500103958837)
    ·
      refine ⟨3056831460680765634746141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32606202247261500103958837 3056831460680765634746141)
      ·
        refine ⟨1146311797755287113029803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3056831460680765634746141 1146311797755287113029803)
        ·
          refine ⟨1719467696632930669544705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146311797755287113029803 1719467696632930669544705)
          ·
            refine ⟨1289600772474698002158529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1719467696632930669544705 1289600772474698002158529)
            ·
              refine ⟨967200579356023501618897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289600772474698002158529 967200579356023501618897)
              ·
                refine ⟨725400434517017626214173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967200579356023501618897 725400434517017626214173)
                ·
                  refine ⟨272025162943881609830315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725400434517017626214173 272025162943881609830315)
                  ·
                    rfl

theorem cell21_1191976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_1191976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1191976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1191976 prefixEnd_1191976 := by exact prefixLift 1191976
  have htrace : WordTrace (prefixWord ++ tailWord_1191976) baseStart_1191976 baseEnd_1191976 := by
    simpa [prefixWord, tailWord_1191976, baseEnd_1191976] using wordTrace_append hprefix tailTrace_1191976
  have hstable : (prefixWord ++ tailWord_1191976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1191976).length < 2 ^ (prefixWord ++ tailWord_1191976).sum := by decide
  have hdescent : baseEnd_1191976 < baseStart_1191976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1191976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192012 : List Nat := [2, 2, 1, 3, 1, 1, 2, 9]
def baseStart_1192012 : Nat := 118140960795 + 1192012 * 2 ^ 59
def prefixEnd_1192012 : Nat := 4983230072969 + 3 ^ 40 * 1192012 * 2
def baseEnd_1192012 : Nat := 90677792878117849076747

theorem tailTrace_1192012 : CollatzResearch.WordTrace tailWord_1192012 prefixEnd_1192012 90677792878117849076747 := by
  unfold tailWord_1192012
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738124678775789143461145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28984166238367718857948193 21738124678775789143461145)
  ·
    refine ⟨16303593509081841857595859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21738124678775789143461145 16303593509081841857595859)
    ·
      refine ⟨24455390263622762786393789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16303593509081841857595859 24455390263622762786393789)
      ·
        refine ⟨9170771348858536044897671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24455390263622762786393789 9170771348858536044897671)
        ·
          refine ⟨13756157023287804067346507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9170771348858536044897671 13756157023287804067346507)
          ·
            refine ⟨20634235534931706101019761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13756157023287804067346507 20634235534931706101019761)
            ·
              refine ⟨15475676651198779575764821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20634235534931706101019761 15475676651198779575764821)
              ·
                refine ⟨90677792878117849076747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15475676651198779575764821 90677792878117849076747)
                ·
                  rfl

theorem cell21_1192012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_1192012 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192012 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192012 prefixEnd_1192012 := by exact prefixLift 1192012
  have htrace : WordTrace (prefixWord ++ tailWord_1192012) baseStart_1192012 baseEnd_1192012 := by
    simpa [prefixWord, tailWord_1192012, baseEnd_1192012] using wordTrace_append hprefix tailTrace_1192012
  have hstable : (prefixWord ++ tailWord_1192012).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192012).length < 2 ^ (prefixWord ++ tailWord_1192012).sum := by decide
  have hdescent : baseEnd_1192012 < baseStart_1192012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192018 : List Nat := [3, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1192018 : Nat := 118140960795 + 1192018 * 2 ^ 59
def prefixEnd_1192018 : Nat := 4983230072969 + 3 ^ 40 * 1192018 * 2
def baseEnd_1192018 : Nat := 272034747916098870130229

theorem tailTrace_1192018 : CollatzResearch.WordTrace tailWord_1192018 prefixEnd_1192018 272034747916098870130229 := by
  unfold tailWord_1192018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869117048882460327910177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28984312130353227541093805 10869117048882460327910177)
  ·
    refine ⟨8151837786661845245932633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10869117048882460327910177 8151837786661845245932633)
    ·
      refine ⟨6113878339996383934449475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8151837786661845245932633 6113878339996383934449475)
      ·
        refine ⟨9170817509994575901674213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6113878339996383934449475 9170817509994575901674213)
        ·
          refine ⟨1719528283123982981563915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9170817509994575901674213 1719528283123982981563915)
          ·
            refine ⟨2579292424685974472345873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719528283123982981563915 2579292424685974472345873)
            ·
              refine ⟨1934469318514480854259405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579292424685974472345873 1934469318514480854259405)
              ·
                refine ⟨725425994442930320347277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1934469318514480854259405 725425994442930320347277)
                ·
                  refine ⟨272034747916098870130229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725425994442930320347277 272034747916098870130229)
                  ·
                    rfl

theorem cell21_1192018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1192018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192018 prefixEnd_1192018 := by exact prefixLift 1192018
  have htrace : WordTrace (prefixWord ++ tailWord_1192018) baseStart_1192018 baseEnd_1192018 := by
    simpa [prefixWord, tailWord_1192018, baseEnd_1192018] using wordTrace_append hprefix tailTrace_1192018
  have hstable : (prefixWord ++ tailWord_1192018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192018).length < 2 ^ (prefixWord ++ tailWord_1192018).sum := by decide
  have hdescent : baseEnd_1192018 < baseStart_1192018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192074 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_1192074 : Nat := 118140960795 + 1192074 * 2 ^ 59
def prefixEnd_1192074 : Nat := 4983230072969 + 3 ^ 40 * 1192074 * 2
def baseEnd_1192074 : Nat := 272047527879055217196781

theorem tailTrace_1192074 : CollatzResearch.WordTrace tailWord_1192074 prefixEnd_1192074 272047527879055217196781 := by
  unfold tailWord_1192074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10869627670831740718919819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28985673788884641917119517 10869627670831740718919819)
  ·
    refine ⟨16304441506247611078379729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10869627670831740718919819 16304441506247611078379729)
    ·
      refine ⟨12228331129685708308784797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16304441506247611078379729 12228331129685708308784797)
      ·
        refine ⟨4585624173632140615794299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12228331129685708308784797 4585624173632140615794299)
        ·
          refine ⟨6878436260448210923691449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4585624173632140615794299 6878436260448210923691449)
          ·
            refine ⟨5158827195336158192768587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6878436260448210923691449 5158827195336158192768587)
            ·
              refine ⟨7738240793004237289152881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5158827195336158192768587 7738240793004237289152881)
              ·
                refine ⟨5803680594753177966864661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7738240793004237289152881 5803680594753177966864661)
                ·
                  refine ⟨272047527879055217196781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5803680594753177966864661 272047527879055217196781)
                  ·
                    rfl

theorem cell21_1192074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_1192074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192074 prefixEnd_1192074 := by exact prefixLift 1192074
  have htrace : WordTrace (prefixWord ++ tailWord_1192074) baseStart_1192074 baseEnd_1192074 := by
    simpa [prefixWord, tailWord_1192074, baseEnd_1192074] using wordTrace_append hprefix tailTrace_1192074
  have hstable : (prefixWord ++ tailWord_1192074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192074).length < 2 ^ (prefixWord ++ tailWord_1192074).sum := by decide
  have hdescent : baseEnd_1192074 < baseStart_1192074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192086 : List Nat := [5, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1192086 : Nat := 118140960795 + 1192086 * 2 ^ 59
def prefixEnd_1192086 : Nat := 4983230072969 + 3 ^ 40 * 1192086 * 2
def baseEnd_1192086 : Nat := 272050266442545862996757

theorem tailTrace_1192086 : CollatzResearch.WordTrace tailWord_1192086 prefixEnd_1192086 272050266442545862996757 := by
  unfold tailWord_1192086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717434272455218057819757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28985965572855659283410741 2717434272455218057819757)
  ·
    refine ⟨1019037852170706771682409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2717434272455218057819757 1019037852170706771682409)
    ·
      refine ⟨764278389128030078761807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1019037852170706771682409 764278389128030078761807)
      ·
        refine ⟨1146417583692045118142711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 764278389128030078761807 1146417583692045118142711)
        ·
          refine ⟨1719626375538067677214067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1146417583692045118142711 1719626375538067677214067)
          ·
            refine ⟨2579439563307101515821101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719626375538067677214067 2579439563307101515821101)
            ·
              refine ⟨967289836240163068432913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2579439563307101515821101 967289836240163068432913)
              ·
                refine ⟨725467377180122301324685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967289836240163068432913 725467377180122301324685)
                ·
                  refine ⟨272050266442545862996757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725467377180122301324685 272050266442545862996757)
                  ·
                    rfl

theorem cell21_1192086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1192086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192086 prefixEnd_1192086 := by exact prefixLift 1192086
  have htrace : WordTrace (prefixWord ++ tailWord_1192086) baseStart_1192086 baseEnd_1192086 := by
    simpa [prefixWord, tailWord_1192086, baseEnd_1192086] using wordTrace_append hprefix tailTrace_1192086
  have hstable : (prefixWord ++ tailWord_1192086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192086).length < 2 ^ (prefixWord ++ tailWord_1192086).sum := by decide
  have hdescent : baseEnd_1192086 < baseStart_1192086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192094 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1192094 : Nat := 118140960795 + 1192094 * 2 ^ 59
def prefixEnd_1192094 : Nat := 4983230072969 + 3 ^ 40 * 1192094 * 2
def baseEnd_1192094 : Nat := 272052092151539626863407

theorem tailTrace_1192094 : CollatzResearch.WordTrace tailWord_1192094 prefixEnd_1192094 272052092151539626863407 := by
  unfold tailWord_1192094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5434905017906813286425917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28986160095503004194271557 5434905017906813286425917)
  ·
    refine ⟨2038089381715054982409719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5434905017906813286425917 2038089381715054982409719)
    ·
      refine ⟨3057134072572582473614579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038089381715054982409719 3057134072572582473614579)
      ·
        refine ⟨4585701108858873710421869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3057134072572582473614579 4585701108858873710421869)
        ·
          refine ⟨1719637915822077641408201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4585701108858873710421869 1719637915822077641408201)
          ·
            refine ⟨1289728436866558231056151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1719637915822077641408201 1289728436866558231056151)
            ·
              refine ⟨1934592655299837346584227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289728436866558231056151 1934592655299837346584227)
              ·
                refine ⟨2901888982949756019876341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934592655299837346584227 2901888982949756019876341)
                ·
                  refine ⟨272052092151539626863407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901888982949756019876341 272052092151539626863407)
                  ·
                    rfl

theorem cell21_1192094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1192094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192094 prefixEnd_1192094 := by exact prefixLift 1192094
  have htrace : WordTrace (prefixWord ++ tailWord_1192094) baseStart_1192094 baseEnd_1192094 := by
    simpa [prefixWord, tailWord_1192094, baseEnd_1192094] using wordTrace_append hprefix tailTrace_1192094
  have hstable : (prefixWord ++ tailWord_1192094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192094).length < 2 ^ (prefixWord ++ tailWord_1192094).sum := by decide
  have hdescent : baseEnd_1192094 < baseStart_1192094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192133 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_1192133 : Nat := 118140960795 + 1192133 * 2 ^ 59
def prefixEnd_1192133 : Nat := 4983230072969 + 3 ^ 40 * 1192133 * 2
def baseEnd_1192133 : Nat := 272060992482884225713327

theorem tailTrace_1192133 : CollatzResearch.WordTrace tailWord_1192133 prefixEnd_1192133 272060992482884225713327 := by
  unfold tailWord_1192133
  simp only [CollatzResearch.WordTrace]
  refine ⟨43480662590113215952077053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987108393408810634718035 43480662590113215952077053)
  ·
    refine ⟨16305248471292455982028895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43480662590113215952077053 16305248471292455982028895)
    ·
      refine ⟨24457872706938683973043343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16305248471292455982028895 24457872706938683973043343)
      ·
        refine ⟨36686809060408025959565015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24457872706938683973043343 36686809060408025959565015)
        ·
          refine ⟨55030213590612038939347523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36686809060408025959565015 55030213590612038939347523)
          ·
            refine ⟨82545320385918058409021285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55030213590612038939347523 82545320385918058409021285)
            ·
              refine ⟨15477247572359635951691491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82545320385918058409021285 15477247572359635951691491)
              ·
                refine ⟨23215871358539453927537237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15477247572359635951691491 23215871358539453927537237)
                ·
                  refine ⟨272060992482884225713327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23215871358539453927537237 272060992482884225713327)
                  ·
                    rfl

theorem cell21_1192133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_1192133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192133 prefixEnd_1192133 := by exact prefixLift 1192133
  have htrace : WordTrace (prefixWord ++ tailWord_1192133) baseStart_1192133 baseEnd_1192133 := by
    simpa [prefixWord, tailWord_1192133, baseEnd_1192133] using wordTrace_append hprefix tailTrace_1192133
  have hstable : (prefixWord ++ tailWord_1192133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192133).length < 2 ^ (prefixWord ++ tailWord_1192133).sum := by decide
  have hdescent : baseEnd_1192133 < baseStart_1192133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192136 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_1192136 : Nat := 118140960795 + 1192136 * 2 ^ 59
def prefixEnd_1192136 : Nat := 4983230072969 + 3 ^ 40 * 1192136 * 2
def baseEnd_1192136 : Nat := 272061677123756887163321

theorem tailTrace_1192136 : CollatzResearch.WordTrace tailWord_1192136 prefixEnd_1192136 272061677123756887163321 := by
  unfold tailWord_1192136
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740386004551173732218131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28987181339401564976290841 21740386004551173732218131)
  ·
    refine ⟨32610579006826760598327197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21740386004551173732218131 32610579006826760598327197)
    ·
      refine ⟨12228967127560035224372699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32610579006826760598327197 12228967127560035224372699)
      ·
        refine ⟨18343450691340052836559049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12228967127560035224372699 18343450691340052836559049)
        ·
          refine ⟨13757588018505039627419287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18343450691340052836559049 13757588018505039627419287)
          ·
            refine ⟨20636382027757559441128931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757588018505039627419287 20636382027757559441128931)
            ·
              refine ⟨30954573041636339161693397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20636382027757559441128931 30954573041636339161693397)
              ·
                refine ⟨725497805663351699102189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30954573041636339161693397 725497805663351699102189)
                ·
                  refine ⟨272061677123756887163321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725497805663351699102189 272061677123756887163321)
                  ·
                    rfl

theorem cell21_1192136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_1192136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192136 prefixEnd_1192136 := by exact prefixLift 1192136
  have htrace : WordTrace (prefixWord ++ tailWord_1192136) baseStart_1192136 baseEnd_1192136 := by
    simpa [prefixWord, tailWord_1192136, baseEnd_1192136] using wordTrace_append hprefix tailTrace_1192136
  have hstable : (prefixWord ++ tailWord_1192136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192136).length < 2 ^ (prefixWord ++ tailWord_1192136).sum := by decide
  have hdescent : baseEnd_1192136 < baseStart_1192136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192153 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 3]
def baseStart_1192153 : Nat := 118140960795 + 1192153 * 2 ^ 59
def prefixEnd_1192153 : Nat := 4983230072969 + 3 ^ 40 * 1192153 * 2
def baseEnd_1192153 : Nat := 272065556755368635379953

theorem tailTrace_1192153 : CollatzResearch.WordTrace tailWord_1192153 prefixEnd_1192153 272065556755368635379953 := by
  unfold tailWord_1192153
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481392050040759367805113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987594700027172911870075 43481392050040759367805113)
  ·
    refine ⟨32611044037530569525853835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43481392050040759367805113 32611044037530569525853835)
    ·
      refine ⟨48916566056295854288780753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32611044037530569525853835 48916566056295854288780753)
      ·
        refine ⟨36687424542221890716585565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48916566056295854288780753 36687424542221890716585565)
        ·
          refine ⟨13757784203333209018719587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36687424542221890716585565 13757784203333209018719587)
          ·
            refine ⟨20636676304999813528079381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757784203333209018719587 20636676304999813528079381)
            ·
              refine ⟨967344201796866259128721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20636676304999813528079381 967344201796866259128721)
              ·
                refine ⟨725508151347649694346541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967344201796866259128721 725508151347649694346541)
                ·
                  refine ⟨272065556755368635379953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725508151347649694346541 272065556755368635379953)
                  ·
                    rfl

theorem cell21_1192153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_1192153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192153 prefixEnd_1192153 := by exact prefixLift 1192153
  have htrace : WordTrace (prefixWord ++ tailWord_1192153) baseStart_1192153 baseEnd_1192153 := by
    simpa [prefixWord, tailWord_1192153, baseEnd_1192153] using wordTrace_append hprefix tailTrace_1192153
  have hstable : (prefixWord ++ tailWord_1192153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192153).length < 2 ^ (prefixWord ++ tailWord_1192153).sum := by decide
  have hdescent : baseEnd_1192153 < baseStart_1192153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192156 : List Nat := [2, 2, 5, 2, 2, 1, 1, 6]
def baseStart_1192156 : Nat := 118140960795 + 1192156 * 2 ^ 59
def prefixEnd_1192156 : Nat := 4983230072969 + 3 ^ 40 * 1192156 * 2
def baseEnd_1192156 : Nat := 90688747132080432276649

theorem tailTrace_1192156 : CollatzResearch.WordTrace tailWord_1192156 prefixEnd_1192156 90688747132080432276649 := by
  unfold tailWord_1192156
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740750734514945440082161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28987667646019927253442881 21740750734514945440082161)
  ·
    refine ⟨16305563050886209080061621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21740750734514945440082161 16305563050886209080061621)
    ·
      refine ⟨1528646536020582101255777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16305563050886209080061621 1528646536020582101255777)
      ·
        refine ⟨1146484902015436575941833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1528646536020582101255777 1146484902015436575941833)
        ·
          refine ⟨859863676511577431956375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1146484902015436575941833 859863676511577431956375)
          ·
            refine ⟨1289795514767366147934563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859863676511577431956375 1289795514767366147934563)
            ·
              refine ⟨1934693272151049221901845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1289795514767366147934563 1934693272151049221901845)
              ·
                refine ⟨90688747132080432276649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1934693272151049221901845 90688747132080432276649)
                ·
                  rfl

theorem cell21_1192156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_1192156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192156 prefixEnd_1192156 := by exact prefixLift 1192156
  have htrace : WordTrace (prefixWord ++ tailWord_1192156) baseStart_1192156 baseEnd_1192156 := by
    simpa [prefixWord, tailWord_1192156, baseEnd_1192156] using wordTrace_append hprefix tailTrace_1192156
  have hstable : (prefixWord ++ tailWord_1192156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192156).length < 2 ^ (prefixWord ++ tailWord_1192156).sum := by decide
  have hdescent : baseEnd_1192156 < baseStart_1192156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192167 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_1192167 : Nat := 118140960795 + 1192167 * 2 ^ 59
def prefixEnd_1192167 : Nat := 4983230072969 + 3 ^ 40 * 1192167 * 2
def baseEnd_1192167 : Nat := 272068751746107722146591

theorem tailTrace_1192167 : CollatzResearch.WordTrace tailWord_1192167 prefixEnd_1192167 272068751746107722146591 := by
  unfold tailWord_1192167
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481902671990039758814755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28987935114660026505876503 43481902671990039758814755)
  ·
    refine ⟨65222854007985059638222133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43481902671990039758814755 65222854007985059638222133)
    ·
      refine ⟨6114642563248599341083325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65222854007985059638222133 6114642563248599341083325)
      ·
        refine ⟨2292990961218224752906247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6114642563248599341083325 2292990961218224752906247)
        ·
          refine ⟨3439486441827337129359371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292990961218224752906247 3439486441827337129359371)
          ·
            refine ⟨5159229662741005694039057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439486441827337129359371 5159229662741005694039057)
            ·
              refine ⟨3869422247055754270529293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5159229662741005694039057 3869422247055754270529293)
              ·
                refine ⟨1451033342645907851448485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3869422247055754270529293 1451033342645907851448485)
                ·
                  refine ⟨272068751746107722146591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451033342645907851448485 272068751746107722146591)
                  ·
                    rfl

theorem cell21_1192167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_1192167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192167 prefixEnd_1192167 := by exact prefixLift 1192167
  have htrace : WordTrace (prefixWord ++ tailWord_1192167) baseStart_1192167 baseEnd_1192167 := by
    simpa [prefixWord, tailWord_1192167, baseEnd_1192167] using wordTrace_append hprefix tailTrace_1192167
  have hstable : (prefixWord ++ tailWord_1192167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192167).length < 2 ^ (prefixWord ++ tailWord_1192167).sum := by decide
  have hdescent : baseEnd_1192167 < baseStart_1192167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192277 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 4]
def baseStart_1192277 : Nat := 118140960795 + 1192277 * 2 ^ 59
def prefixEnd_1192277 : Nat := 4983230072969 + 3 ^ 40 * 1192277 * 2
def baseEnd_1192277 : Nat := 272093855244771975313033

theorem tailTrace_1192277 : CollatzResearch.WordTrace tailWord_1192277 prefixEnd_1192277 272093855244771975313033 := by
  unfold tailWord_1192277
  simp only [CollatzResearch.WordTrace]
  refine ⟨43485914701591528545319085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28990609801061019030212723 43485914701591528545319085)
  ·
    refine ⟨16307218013096823204494657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43485914701591528545319085 16307218013096823204494657)
    ·
      refine ⟨12230413509822617403370993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16307218013096823204494657 12230413509822617403370993)
      ·
        refine ⟨9172810132366963052528245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12230413509822617403370993 9172810132366963052528245)
        ·
          refine ⟨859950949909402786174523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9172810132366963052528245 859950949909402786174523)
          ·
            refine ⟨1289926424864104179261785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 859950949909402786174523 1289926424864104179261785)
            ·
              refine ⟨967444818648078134446339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1289926424864104179261785 967444818648078134446339)
              ·
                refine ⟨1451167227972117201669509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967444818648078134446339 1451167227972117201669509)
                ·
                  refine ⟨272093855244771975313033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451167227972117201669509 272093855244771975313033)
                  ·
                    rfl

theorem cell21_1192277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_1192277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192277 prefixEnd_1192277 := by exact prefixLift 1192277
  have htrace : WordTrace (prefixWord ++ tailWord_1192277) baseStart_1192277 baseEnd_1192277 := by
    simpa [prefixWord, tailWord_1192277, baseEnd_1192277] using wordTrace_append hprefix tailTrace_1192277
  have hstable : (prefixWord ++ tailWord_1192277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192277).length < 2 ^ (prefixWord ++ tailWord_1192277).sum := by decide
  have hdescent : baseEnd_1192277 < baseStart_1192277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192502 : List Nat := [5, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1192502 : Nat := 118140960795 + 1192502 * 2 ^ 59
def prefixEnd_1192502 : Nat := 4983230072969 + 3 ^ 40 * 1192502 * 2
def baseEnd_1192502 : Nat := 90715067770073861354191

theorem tailTrace_1192502 : CollatzResearch.WordTrace tailWord_1192502 prefixEnd_1192502 90715067770073861354191 := by
  unfold tailWord_1192502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2718382570361024498266235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28996080750517594648173173 2718382570361024498266235)
  ·
    refine ⟨4077573855541536747399353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2718382570361024498266235 4077573855541536747399353)
    ·
      refine ⟨3058180391656152560549515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4077573855541536747399353 3058180391656152560549515)
      ·
        refine ⟨4587270587484228840824273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058180391656152560549515 4587270587484228840824273)
        ·
          refine ⟨3440452940613171630618205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4587270587484228840824273 3440452940613171630618205)
          ·
            refine ⟨1290169852729939361481827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3440452940613171630618205 1290169852729939361481827)
            ·
              refine ⟨1935254779094909042222741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290169852729939361481827 1935254779094909042222741)
              ·
                refine ⟨90715067770073861354191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1935254779094909042222741 90715067770073861354191)
                ·
                  rfl

theorem cell21_1192502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1192502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192502 prefixEnd_1192502 := by exact prefixLift 1192502
  have htrace : WordTrace (prefixWord ++ tailWord_1192502) baseStart_1192502 baseEnd_1192502 := by
    simpa [prefixWord, tailWord_1192502, baseEnd_1192502] using wordTrace_append hprefix tailTrace_1192502
  have hstable : (prefixWord ++ tailWord_1192502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192502).length < 2 ^ (prefixWord ++ tailWord_1192502).sum := by decide
  have hdescent : baseEnd_1192502 < baseStart_1192502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192527 : List Nat := [1, 1, 2, 1, 1, 2, 4, 9]
def baseStart_1192527 : Nat := 118140960795 + 1192527 * 2 ^ 59
def prefixEnd_1192527 : Nat := 4983230072969 + 3 ^ 40 * 1192527 * 2
def baseEnd_1192527 : Nat := 90716969550275698715285

theorem tailTrace_1192527 : CollatzResearch.WordTrace tailWord_1192527 prefixEnd_1192527 90716969550275698715285 := by
  unfold tailWord_1192527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43495032950685821241919835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28996688633790547494613223 43495032950685821241919835)
  ·
    refine ⟨65242549426028731862879753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43495032950685821241919835 65242549426028731862879753)
    ·
      refine ⟨48931912069521548897159815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65242549426028731862879753 48931912069521548897159815)
      ·
        refine ⟨73397868104282323345739723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48931912069521548897159815 73397868104282323345739723)
        ·
          refine ⟨110096802156423485018609585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73397868104282323345739723 110096802156423485018609585)
          ·
            refine ⟨82572601617317613763957189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110096802156423485018609585 82572601617317613763957189)
            ·
              refine ⟨15482362803247052580741973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82572601617317613763957189 15482362803247052580741973)
              ·
                refine ⟨90716969550275698715285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15482362803247052580741973 90716969550275698715285)
                ·
                  rfl

theorem cell21_1192527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_1192527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192527 prefixEnd_1192527 := by exact prefixLift 1192527
  have htrace : WordTrace (prefixWord ++ tailWord_1192527) baseStart_1192527 baseEnd_1192527 := by
    simpa [prefixWord, tailWord_1192527, baseEnd_1192527] using wordTrace_append hprefix tailTrace_1192527
  have hstable : (prefixWord ++ tailWord_1192527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192527).length < 2 ^ (prefixWord ++ tailWord_1192527).sum := by decide
  have hdescent : baseEnd_1192527 < baseStart_1192527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192606 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 6]
def baseStart_1192606 : Nat := 118140960795 + 1192606 * 2 ^ 59
def prefixEnd_1192606 : Nat := 4983230072969 + 3 ^ 40 * 1192606 * 2
def baseEnd_1192606 : Nat := 272168937527140514329027

theorem tailTrace_1192606 : CollatzResearch.WordTrace tailWord_1192606 prefixEnd_1192606 272168937527140514329027 := by
  unfold tailWord_1192606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437239289674952216755709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28998609544933078489363781 5437239289674952216755709)
  ·
    refine ⟨2038964733628107081283391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5437239289674952216755709 2038964733628107081283391)
    ·
      refine ⟨3058447100442160621925087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038964733628107081283391 3058447100442160621925087)
      ·
        refine ⟨4587670650663240932887631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058447100442160621925087 4587670650663240932887631)
        ·
          refine ⟨6881505975994861399331447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587670650663240932887631 6881505975994861399331447)
          ·
            refine ⟨10322258963992292098997171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6881505975994861399331447 10322258963992292098997171)
            ·
              refine ⟨15483388445988438148495757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10322258963992292098997171 15483388445988438148495757)
              ·
                refine ⟨5806270667245664305685909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15483388445988438148495757 5806270667245664305685909)
                ·
                  refine ⟨272168937527140514329027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5806270667245664305685909 272168937527140514329027)
                  ·
                    rfl

theorem cell21_1192606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_1192606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192606 prefixEnd_1192606 := by exact prefixLift 1192606
  have htrace : WordTrace (prefixWord ++ tailWord_1192606) baseStart_1192606 baseEnd_1192606 := by
    simpa [prefixWord, tailWord_1192606, baseEnd_1192606] using wordTrace_append hprefix tailTrace_1192606
  have hstable : (prefixWord ++ tailWord_1192606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192606).length < 2 ^ (prefixWord ++ tailWord_1192606).sum := by decide
  have hdescent : baseEnd_1192606 < baseStart_1192606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192609 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 5]
def baseStart_1192609 : Nat := 118140960795 + 1192609 * 2 ^ 59
def prefixEnd_1192609 : Nat := 4983230072969 + 3 ^ 40 * 1192609 * 2
def baseEnd_1192609 : Nat := 272169622168013175779021

theorem tailTrace_1192609 : CollatzResearch.WordTrace tailWord_1192609 prefixEnd_1192609 272169622168013175779021 := by
  unfold tailWord_1192609
  simp only [CollatzResearch.WordTrace]
  refine ⟨43498023736388749246404881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28998682490925832830936587 43498023736388749246404881)
  ·
    refine ⟨32623517802291561934803661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43498023736388749246404881 32623517802291561934803661)
    ·
      refine ⟨12233819175859335725551373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32623517802291561934803661 12233819175859335725551373)
      ·
        refine ⟨4587682190947250897081765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12233819175859335725551373 4587682190947250897081765)
        ·
          refine ⟨860190410802609543202831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4587682190947250897081765 860190410802609543202831)
          ·
            refine ⟨1290285616203914314804247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860190410802609543202831 1290285616203914314804247)
            ·
              refine ⟨1935428424305871472206371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290285616203914314804247 1935428424305871472206371)
              ·
                refine ⟨2903142636458807208309557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935428424305871472206371 2903142636458807208309557)
                ·
                  refine ⟨272169622168013175779021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2903142636458807208309557 272169622168013175779021)
                  ·
                    rfl

theorem cell21_1192609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_1192609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192609 prefixEnd_1192609 := by exact prefixLift 1192609
  have htrace : WordTrace (prefixWord ++ tailWord_1192609) baseStart_1192609 baseEnd_1192609 := by
    simpa [prefixWord, tailWord_1192609, baseEnd_1192609] using wordTrace_append hprefix tailTrace_1192609
  have hstable : (prefixWord ++ tailWord_1192609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192609).length < 2 ^ (prefixWord ++ tailWord_1192609).sum := by decide
  have hdescent : baseEnd_1192609 < baseStart_1192609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192623 : List Nat := [1, 1, 2, 1, 2, 7, 2, 1, 4]
def baseStart_1192623 : Nat := 118140960795 + 1192623 * 2 ^ 59
def prefixEnd_1192623 : Nat := 4983230072969 + 3 ^ 40 * 1192623 * 2
def baseEnd_1192623 : Nat := 272172817158752262545659

theorem tailTrace_1192623 : CollatzResearch.WordTrace tailWord_1192623 prefixEnd_1192623 272172817158752262545659 := by
  unfold tailWord_1192623
  simp only [CollatzResearch.WordTrace]
  refine ⟨43498534358338029637414523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28999022905558686424943015 43498534358338029637414523)
  ·
    refine ⟨65247801537507044456121785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43498534358338029637414523 65247801537507044456121785)
    ·
      refine ⟨48935851153130283342091339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65247801537507044456121785 48935851153130283342091339)
      ·
        refine ⟨73403776729695425013137009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48935851153130283342091339 73403776729695425013137009)
        ·
          refine ⟨55052832547271568759852757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73403776729695425013137009 55052832547271568759852757)
          ·
            refine ⟨1290300762826677392809049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 55052832547271568759852757 1290300762826677392809049)
            ·
              refine ⟨967725572120008044606787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290300762826677392809049 967725572120008044606787)
              ·
                refine ⟨1451588358180012066910181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 967725572120008044606787 1451588358180012066910181)
                ·
                  refine ⟨272172817158752262545659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451588358180012066910181 272172817158752262545659)
                  ·
                    rfl

theorem cell21_1192623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 2, 1, 4].length) (baseStart_1192623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192623 prefixEnd_1192623 := by exact prefixLift 1192623
  have htrace : WordTrace (prefixWord ++ tailWord_1192623) baseStart_1192623 baseEnd_1192623 := by
    simpa [prefixWord, tailWord_1192623, baseEnd_1192623] using wordTrace_append hprefix tailTrace_1192623
  have hstable : (prefixWord ++ tailWord_1192623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192623).length < 2 ^ (prefixWord ++ tailWord_1192623).sum := by decide
  have hdescent : baseEnd_1192623 < baseStart_1192623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192634 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1192634 : Nat := 118140960795 + 1192634 * 2 ^ 59
def prefixEnd_1192634 : Nat := 4983230072969 + 3 ^ 40 * 1192634 * 2
def baseEnd_1192634 : Nat := 272175327508618687862303

theorem tailTrace_1192634 : CollatzResearch.WordTrace tailWord_1192634 prefixEnd_1192634 272175327508618687862303 := by
  unfold tailWord_1192634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10874733890324544629016239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28999290374198785677376637 10874733890324544629016239)
  ·
    refine ⟨16312100835486816943524359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10874733890324544629016239 16312100835486816943524359)
    ·
      refine ⟨24468151253230225415286539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16312100835486816943524359 24468151253230225415286539)
      ·
        refine ⟨36702226879845338122929809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24468151253230225415286539 36702226879845338122929809)
        ·
          refine ⟨27526670159884003592197357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36702226879845338122929809 27526670159884003592197357)
          ·
            refine ⟨10322501309956501347074009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27526670159884003592197357 10322501309956501347074009)
            ·
              refine ⟨7741875982467376010305507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10322501309956501347074009 7741875982467376010305507)
              ·
                refine ⟨11612813973701064015458261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7741875982467376010305507 11612813973701064015458261)
                ·
                  refine ⟨272175327508618687862303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11612813973701064015458261 272175327508618687862303)
                  ·
                    rfl

theorem cell21_1192634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1192634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192634 prefixEnd_1192634 := by exact prefixLift 1192634
  have htrace : WordTrace (prefixWord ++ tailWord_1192634) baseStart_1192634 baseEnd_1192634 := by
    simpa [prefixWord, tailWord_1192634, baseEnd_1192634] using wordTrace_append hprefix tailTrace_1192634
  have hstable : (prefixWord ++ tailWord_1192634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192634).length < 2 ^ (prefixWord ++ tailWord_1192634).sum := by decide
  have hdescent : baseEnd_1192634 < baseStart_1192634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192696 : List Nat := [2, 1, 2, 1, 1, 2, 7, 5]
def baseStart_1192696 : Nat := 118140960795 + 1192696 * 2 ^ 59
def prefixEnd_1192696 : Nat := 4983230072969 + 3 ^ 40 * 1192696 * 2
def baseEnd_1192696 : Nat := 90729825584440119276281

theorem tailTrace_1192696 : CollatzResearch.WordTrace tailWord_1192696 prefixEnd_1192696 90729825584440119276281 := by
  unfold tailWord_1192696
  simp only [CollatzResearch.WordTrace]
  refine ⟨21750598443536781552410971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29000797924715708736547961 21750598443536781552410971)
  ·
    refine ⟨32625897665305172328616457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21750598443536781552410971 32625897665305172328616457)
    ·
      refine ⟨24469423248978879246462343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32625897665305172328616457 24469423248978879246462343)
      ·
        refine ⟨36704134873468318869693515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24469423248978879246462343 36704134873468318869693515)
        ·
          refine ⟨55056202310202478304540273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36704134873468318869693515 55056202310202478304540273)
          ·
            refine ⟨41292151732651858728405205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55056202310202478304540273 41292151732651858728405205)
            ·
              refine ⟨967784806234027938946997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41292151732651858728405205 967784806234027938946997)
              ·
                refine ⟨90729825584440119276281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 967784806234027938946997 90729825584440119276281)
                ·
                  rfl

theorem cell21_1192696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_1192696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192696 prefixEnd_1192696 := by exact prefixLift 1192696
  have htrace : WordTrace (prefixWord ++ tailWord_1192696) baseStart_1192696 baseEnd_1192696 := by
    simpa [prefixWord, tailWord_1192696, baseEnd_1192696] using wordTrace_append hprefix tailTrace_1192696
  have hstable : (prefixWord ++ tailWord_1192696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192696).length < 2 ^ (prefixWord ++ tailWord_1192696).sum := by decide
  have hdescent : baseEnd_1192696 < baseStart_1192696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192837 : List Nat := [1, 3, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1192837 : Nat := 118140960795 + 1192837 * 2 ^ 59
def prefixEnd_1192837 : Nat := 4983230072969 + 3 ^ 40 * 1192837 * 2
def baseEnd_1192837 : Nat := 272221654874335445978555

theorem tailTrace_1192837 : CollatzResearch.WordTrace tailWord_1192837 prefixEnd_1192837 272221654874335445978555 := by
  unfold tailWord_1192837
  simp only [CollatzResearch.WordTrace]
  refine ⟨43506339579562744185704765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29004226386375162790469843 43506339579562744185704765)
  ·
    refine ⟨16314877342336029069639287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43506339579562744185704765 16314877342336029069639287)
    ·
      refine ⟨24472316013504043604458931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16314877342336029069639287 24472316013504043604458931)
      ·
        refine ⟨36708474020256065406688397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24472316013504043604458931 36708474020256065406688397)
        ·
          refine ⟨13765677757596024527508149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36708474020256065406688397 13765677757596024527508149)
          ·
            refine ⟨1290532289774627299453889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13765677757596024527508149 1290532289774627299453889)
            ·
              refine ⟨967899217330970474590417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290532289774627299453889 967899217330970474590417)
              ·
                refine ⟨725924412998227855942813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 967899217330970474590417 725924412998227855942813)
                ·
                  refine ⟨272221654874335445978555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725924412998227855942813 272221654874335445978555)
                  ·
                    rfl

theorem cell21_1192837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1192837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192837 prefixEnd_1192837 := by exact prefixLift 1192837
  have htrace : WordTrace (prefixWord ++ tailWord_1192837) baseStart_1192837 baseEnd_1192837 := by
    simpa [prefixWord, tailWord_1192837, baseEnd_1192837] using wordTrace_append hprefix tailTrace_1192837
  have hstable : (prefixWord ++ tailWord_1192837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192837).length < 2 ^ (prefixWord ++ tailWord_1192837).sum := by decide
  have hdescent : baseEnd_1192837 < baseStart_1192837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192865 : List Nat := [1, 2, 3, 4, 1, 2, 3, 5]
def baseStart_1192865 : Nat := 118140960795 + 1192865 * 2 ^ 59
def prefixEnd_1192865 : Nat := 4983230072969 + 3 ^ 40 * 1192865 * 2
def baseEnd_1192865 : Nat := 90742681618604539837277

theorem tailTrace_1192865 : CollatzResearch.WordTrace tailWord_1192865 prefixEnd_1192865 90742681618604539837277 := by
  unfold tailWord_1192865
  simp only [CollatzResearch.WordTrace]
  refine ⟨43507360823461304967724049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29004907215640869978482699 43507360823461304967724049)
  ·
    refine ⟨32630520617595978725793037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43507360823461304967724049 32630520617595978725793037)
    ·
      refine ⟨12236445231598492022172389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32630520617595978725793037 12236445231598492022172389)
      ·
        refine ⟨2294333480924717254157323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12236445231598492022172389 2294333480924717254157323)
        ·
          refine ⟨3441500221387075881235985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294333480924717254157323 3441500221387075881235985)
          ·
            refine ⟨2581125166040306910926989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3441500221387075881235985 2581125166040306910926989)
            ·
              refine ⟨967921937265115091597621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2581125166040306910926989 967921937265115091597621)
              ·
                refine ⟨90742681618604539837277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 967921937265115091597621 90742681618604539837277)
                ·
                  rfl

theorem cell21_1192865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 5].length) (baseStart_1192865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192865 prefixEnd_1192865 := by exact prefixLift 1192865
  have htrace : WordTrace (prefixWord ++ tailWord_1192865) baseStart_1192865 baseEnd_1192865 := by
    simpa [prefixWord, tailWord_1192865, baseEnd_1192865] using wordTrace_append hprefix tailTrace_1192865
  have hstable : (prefixWord ++ tailWord_1192865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192865).length < 2 ^ (prefixWord ++ tailWord_1192865).sum := by decide
  have hdescent : baseEnd_1192865 < baseStart_1192865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192876 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_1192876 : Nat := 118140960795 + 1192876 * 2 ^ 59
def prefixEnd_1192876 : Nat := 4983230072969 + 3 ^ 40 * 1192876 * 2
def baseEnd_1192876 : Nat := 272230555205680044828475

theorem tailTrace_1192876 : CollatzResearch.WordTrace tailWord_1192876 prefixEnd_1192876 272230555205680044828475 := by
  unfold tailWord_1192876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21753881013210726923187241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29005174684280969230916321 21753881013210726923187241)
  ·
    refine ⟨16315410759908045192390431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21753881013210726923187241 16315410759908045192390431)
    ·
      refine ⟨24473116139862067788585647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16315410759908045192390431 24473116139862067788585647)
      ·
        refine ⟨36709674209793101682878471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24473116139862067788585647 36709674209793101682878471)
        ·
          refine ⟨55064511314689652524317707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36709674209793101682878471 55064511314689652524317707)
          ·
            refine ⟨82596766972034478786476561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55064511314689652524317707 82596766972034478786476561)
            ·
              refine ⟨61947575229025859089857421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82596766972034478786476561 61947575229025859089857421)
              ·
                refine ⟨23230340710884697158696533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61947575229025859089857421 23230340710884697158696533)
                ·
                  refine ⟨272230555205680044828475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23230340710884697158696533 272230555205680044828475)
                  ·
                    rfl

theorem cell21_1192876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_1192876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192876 prefixEnd_1192876 := by exact prefixLift 1192876
  have htrace : WordTrace (prefixWord ++ tailWord_1192876) baseStart_1192876 baseEnd_1192876 := by
    simpa [prefixWord, tailWord_1192876, baseEnd_1192876] using wordTrace_append hprefix tailTrace_1192876
  have hstable : (prefixWord ++ tailWord_1192876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192876).length < 2 ^ (prefixWord ++ tailWord_1192876).sum := by decide
  have hdescent : baseEnd_1192876 < baseStart_1192876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1192930 : List Nat := [3, 3, 3, 1, 1, 3, 1, 3, 3]
def baseStart_1192930 : Nat := 118140960795 + 1192930 * 2 ^ 59
def prefixEnd_1192930 : Nat := 4983230072969 + 3 ^ 40 * 1192930 * 2
def baseEnd_1192930 : Nat := 272242878741387950928365

theorem tailTrace_1192930 : CollatzResearch.WordTrace tailWord_1192930 prefixEnd_1192930 272242878741387950928365 := by
  unfold tailWord_1192930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10877432892056455267210061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29006487712150547379226829 10877432892056455267210061)
  ·
    refine ⟨4079037334521170725203773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10877432892056455267210061 4079037334521170725203773)
    ·
      refine ⟨1529639000445439021951415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4079037334521170725203773 1529639000445439021951415)
      ·
        refine ⟨2294458500668158532927123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529639000445439021951415 2294458500668158532927123)
        ·
          refine ⟨3441687751002237799390685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294458500668158532927123 3441687751002237799390685)
          ·
            refine ⟨1290632906625839174771507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3441687751002237799390685 1290632906625839174771507)
            ·
              refine ⟨1935949359938758762157261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1290632906625839174771507 1935949359938758762157261)
              ·
                refine ⟨725981009977034535808973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1935949359938758762157261 725981009977034535808973)
                ·
                  refine ⟨272242878741387950928365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 725981009977034535808973 272242878741387950928365)
                  ·
                    rfl

theorem cell21_1192930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_1192930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1192930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1192930 prefixEnd_1192930 := by exact prefixLift 1192930
  have htrace : WordTrace (prefixWord ++ tailWord_1192930) baseStart_1192930 baseEnd_1192930 := by
    simpa [prefixWord, tailWord_1192930, baseEnd_1192930] using wordTrace_append hprefix tailTrace_1192930
  have hstable : (prefixWord ++ tailWord_1192930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1192930).length < 2 ^ (prefixWord ++ tailWord_1192930).sum := by decide
  have hdescent : baseEnd_1192930 < baseStart_1192930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1192930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193093 : List Nat := [1, 3, 1, 1, 6, 2, 2, 5]
def baseStart_1193093 : Nat := 118140960795 + 1193093 * 2 ^ 59
def prefixEnd_1193093 : Nat := 4983230072969 + 3 ^ 40 * 1193093 * 2
def baseEnd_1193093 : Nat := 90760025854045296570455

theorem tailTrace_1193093 : CollatzResearch.WordTrace tailWord_1193093 prefixEnd_1193093 90760025854045296570455 := by
  unfold tailWord_1193093
  simp only [CollatzResearch.WordTrace]
  refine ⟨43515676666635299907023933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29010451111090199938015955 43515676666635299907023933)
  ·
    refine ⟨16318378749988237465133975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43515676666635299907023933 16318378749988237465133975)
    ·
      refine ⟨24477568124982356197700963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16318378749988237465133975 24477568124982356197700963)
      ·
        refine ⟨36716352187473534296551445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24477568124982356197700963 36716352187473534296551445)
        ·
          refine ⟨1721079008787821920150849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36716352187473534296551445 1721079008787821920150849)
          ·
            refine ⟨1290809256590866440113137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721079008787821920150849 1290809256590866440113137)
            ·
              refine ⟨968106942443149830084853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1290809256590866440113137 968106942443149830084853)
              ·
                refine ⟨90760025854045296570455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 968106942443149830084853 90760025854045296570455)
                ·
                  rfl

theorem cell21_1193093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 5].length) (baseStart_1193093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193093 prefixEnd_1193093 := by exact prefixLift 1193093
  have htrace : WordTrace (prefixWord ++ tailWord_1193093) baseStart_1193093 baseEnd_1193093 := by
    simpa [prefixWord, tailWord_1193093, baseEnd_1193093] using wordTrace_append hprefix tailTrace_1193093
  have hstable : (prefixWord ++ tailWord_1193093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193093).length < 2 ^ (prefixWord ++ tailWord_1193093).sum := by decide
  have hdescent : baseEnd_1193093 < baseStart_1193093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193107 : List Nat := [1, 1, 1, 2, 1, 2, 7, 3, 3]
def baseStart_1193107 : Nat := 118140960795 + 1193107 * 2 ^ 59
def prefixEnd_1193107 : Nat := 4983230072969 + 3 ^ 40 * 1193107 * 2
def baseEnd_1193107 : Nat := 272283272552874976478003

theorem tailTrace_1193107 : CollatzResearch.WordTrace tailWord_1193107 prefixEnd_1193107 272283272552874976478003 := by
  unfold tailWord_1193107
  simp only [CollatzResearch.WordTrace]
  refine ⟨43516187288584580298033575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29010791525723053532022383 43516187288584580298033575)
  ·
    refine ⟨65274280932876870447050363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43516187288584580298033575 65274280932876870447050363)
    ·
      refine ⟨97911421399315305670575545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65274280932876870447050363 97911421399315305670575545)
      ·
        refine ⟨73433566049486479252931659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97911421399315305670575545 73433566049486479252931659)
        ·
          refine ⟨110150349074229718879397489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73433566049486479252931659 110150349074229718879397489)
          ·
            refine ⟨82612761805672289159548117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110150349074229718879397489 82612761805672289159548117)
            ·
              refine ⟨1936236604820444277176909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82612761805672289159548117 1936236604820444277176909)
              ·
                refine ⟨726088726807666603941341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936236604820444277176909 726088726807666603941341)
                ·
                  refine ⟨272283272552874976478003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726088726807666603941341 272283272552874976478003)
                  ·
                    rfl

theorem cell21_1193107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3].length) (baseStart_1193107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193107 prefixEnd_1193107 := by exact prefixLift 1193107
  have htrace : WordTrace (prefixWord ++ tailWord_1193107) baseStart_1193107 baseEnd_1193107 := by
    simpa [prefixWord, tailWord_1193107, baseEnd_1193107] using wordTrace_append hprefix tailTrace_1193107
  have hstable : (prefixWord ++ tailWord_1193107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193107).length < 2 ^ (prefixWord ++ tailWord_1193107).sum := by decide
  have hdescent : baseEnd_1193107 < baseStart_1193107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193121 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_1193121 : Nat := 118140960795 + 1193121 * 2 ^ 59
def prefixEnd_1193121 : Nat := 4983230072969 + 3 ^ 40 * 1193121 * 2
def baseEnd_1193121 : Nat := 272286467543614063244641

theorem tailTrace_1193121 : CollatzResearch.WordTrace tailWord_1193121 prefixEnd_1193121 272286467543614063244641 := by
  unfold tailWord_1193121
  simp only [CollatzResearch.WordTrace]
  refine ⟨43516697910533860689043217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29011131940355907126028811 43516697910533860689043217)
  ·
    refine ⟨32637523432900395516782413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43516697910533860689043217 32637523432900395516782413)
    ·
      refine ⟨12239071287337648318793405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32637523432900395516782413 12239071287337648318793405)
      ·
        refine ⟨4589651732751618119547527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12239071287337648318793405 4589651732751618119547527)
        ·
          refine ⟨6884477599127427179321291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589651732751618119547527 6884477599127427179321291)
          ·
            refine ⟨10326716398691140768981937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6884477599127427179321291 10326716398691140768981937)
            ·
              refine ⟨7745037299018355576736453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10326716398691140768981937 7745037299018355576736453)
              ·
                refine ⟨1452194493565941670638085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7745037299018355576736453 1452194493565941670638085)
                ·
                  refine ⟨272286467543614063244641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452194493565941670638085 272286467543614063244641)
                  ·
                    rfl

theorem cell21_1193121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_1193121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193121 prefixEnd_1193121 := by exact prefixLift 1193121
  have htrace : WordTrace (prefixWord ++ tailWord_1193121) baseStart_1193121 baseEnd_1193121 := by
    simpa [prefixWord, tailWord_1193121, baseEnd_1193121] using wordTrace_append hprefix tailTrace_1193121
  have hstable : (prefixWord ++ tailWord_1193121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193121).length < 2 ^ (prefixWord ++ tailWord_1193121).sum := by decide
  have hdescent : baseEnd_1193121 < baseStart_1193121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193138 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_1193138 : Nat := 118140960795 + 1193138 * 2 ^ 59
def prefixEnd_1193138 : Nat := 4983230072969 + 3 ^ 40 * 1193138 * 2
def baseEnd_1193138 : Nat := 272290347175225811461273

theorem tailTrace_1193138 : CollatzResearch.WordTrace tailWord_1193138 prefixEnd_1193138 272290347175225811461273 := by
  unfold tailWord_1193138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10879329487868068148103017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29011545300981515061608045 10879329487868068148103017)
  ·
    refine ⟨8159497115901051111077263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10879329487868068148103017 8159497115901051111077263)
    ·
      refine ⟨12239245673851576666615895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8159497115901051111077263 12239245673851576666615895)
      ·
        refine ⟨18358868510777364999923843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12239245673851576666615895 18358868510777364999923843)
        ·
          refine ⟨27538302766166047499885765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18358868510777364999923843 27538302766166047499885765)
          ·
            refine ⟨5163431768656133906228581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27538302766166047499885765 5163431768656133906228581)
            ·
              refine ⟨968143456623025107417859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5163431768656133906228581 968143456623025107417859)
              ·
                refine ⟨1452215184934537661126789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968143456623025107417859 1452215184934537661126789)
                ·
                  refine ⟨272290347175225811461273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452215184934537661126789 272290347175225811461273)
                  ·
                    rfl

theorem cell21_1193138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_1193138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193138 prefixEnd_1193138 := by exact prefixLift 1193138
  have htrace : WordTrace (prefixWord ++ tailWord_1193138) baseStart_1193138 baseEnd_1193138 := by
    simpa [prefixWord, tailWord_1193138, baseEnd_1193138] using wordTrace_append hprefix tailTrace_1193138
  have hstable : (prefixWord ++ tailWord_1193138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193138).length < 2 ^ (prefixWord ++ tailWord_1193138).sum := by decide
  have hdescent : baseEnd_1193138 < baseStart_1193138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193225 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_1193225 : Nat := 118140960795 + 1193225 * 2 ^ 59
def prefixEnd_1193225 : Nat := 4983230072969 + 3 ^ 40 * 1193225 * 2
def baseEnd_1193225 : Nat := 272310201760532993511095

theorem tailTrace_1193225 : CollatzResearch.WordTrace tailWord_1193225 prefixEnd_1193225 272310201760532993511095 := by
  unfold tailWord_1193225
  simp only [CollatzResearch.WordTrace]
  refine ⟨43520491102157086450829129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29013660734771390967219419 43520491102157086450829129)
  ·
    refine ⟨32640368326617814838121847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43520491102157086450829129 32640368326617814838121847)
    ·
      refine ⟨48960552489926722257182771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32640368326617814838121847 48960552489926722257182771)
      ·
        refine ⟨73440828734890083385774157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48960552489926722257182771 73440828734890083385774157)
        ·
          refine ⟨27540310775583781269665309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73440828734890083385774157 27540310775583781269665309)
          ·
            refine ⟨10327616540843917976124491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27540310775583781269665309 10327616540843917976124491)
            ·
              refine ⟨15491424811265876964186737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327616540843917976124491 15491424811265876964186737)
              ·
                refine ⟨11618568608449407723140053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15491424811265876964186737 11618568608449407723140053)
                ·
                  refine ⟨272310201760532993511095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11618568608449407723140053 272310201760532993511095)
                  ·
                    rfl

theorem cell21_1193225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_1193225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193225 prefixEnd_1193225 := by exact prefixLift 1193225
  have htrace : WordTrace (prefixWord ++ tailWord_1193225) baseStart_1193225 baseEnd_1193225 := by
    simpa [prefixWord, tailWord_1193225, baseEnd_1193225] using wordTrace_append hprefix tailTrace_1193225
  have hstable : (prefixWord ++ tailWord_1193225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193225).length < 2 ^ (prefixWord ++ tailWord_1193225).sum := by decide
  have hdescent : baseEnd_1193225 < baseStart_1193225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193242 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1193242 : Nat := 118140960795 + 1193242 * 2 ^ 59
def prefixEnd_1193242 : Nat := 4983230072969 + 3 ^ 40 * 1193242 * 2
def baseEnd_1193242 : Nat := 272314081392144741727727

theorem tailTrace_1193242 : CollatzResearch.WordTrace tailWord_1193242 prefixEnd_1193242 272314081392144741727727 := by
  unfold tailWord_1193242
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880277785773874588549495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29014074095396998902798653 10880277785773874588549495)
  ·
    refine ⟨16320416678660811882824243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10880277785773874588549495 16320416678660811882824243)
    ·
      refine ⟨24480625017991217824236365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16320416678660811882824243 24480625017991217824236365)
      ·
        refine ⟨9180234381746706684088637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24480625017991217824236365 9180234381746706684088637)
        ·
          refine ⟨3442587893155015006533239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9180234381746706684088637 3442587893155015006533239)
          ·
            refine ⟨5163881839732522509799859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442587893155015006533239 5163881839732522509799859)
            ·
              refine ⟨7745822759598783764699789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163881839732522509799859 7745822759598783764699789)
              ·
                refine ⟨2904683534849543911762421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7745822759598783764699789 2904683534849543911762421)
                ·
                  refine ⟨272314081392144741727727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904683534849543911762421 272314081392144741727727)
                  ·
                    rfl

theorem cell21_1193242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1193242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193242 prefixEnd_1193242 := by exact prefixLift 1193242
  have htrace : WordTrace (prefixWord ++ tailWord_1193242) baseStart_1193242 baseEnd_1193242 := by
    simpa [prefixWord, tailWord_1193242, baseEnd_1193242] using wordTrace_append hprefix tailTrace_1193242
  have hstable : (prefixWord ++ tailWord_1193242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193242).length < 2 ^ (prefixWord ++ tailWord_1193242).sum := by decide
  have hdescent : baseEnd_1193242 < baseStart_1193242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193276 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_1193276 : Nat := 118140960795 + 1193276 * 2 ^ 59
def prefixEnd_1193276 : Nat := 4983230072969 + 3 ^ 40 * 1193276 * 2
def baseEnd_1193276 : Nat := 272321840655368238160991

theorem tailTrace_1193276 : CollatzResearch.WordTrace tailWord_1193276 prefixEnd_1193276 272321840655368238160991 := by
  unfold tailWord_1193276
  simp only [CollatzResearch.WordTrace]
  refine ⟨21761175612486161080467841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29014900816648214773957121 21761175612486161080467841)
  ·
    refine ⟨16320881709364620810350881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21761175612486161080467841 16320881709364620810350881)
    ·
      refine ⟨12240661282023465607763161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16320881709364620810350881 12240661282023465607763161)
      ·
        refine ⟨9180495961517599205822371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12240661282023465607763161 9180495961517599205822371)
        ·
          refine ⟨13770743942276398808733557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9180495961517599205822371 13770743942276398808733557)
          ·
            refine ⟨1291007244588412388318771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13770743942276398808733557 1291007244588412388318771)
            ·
              refine ⟨1936510866882618582478157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291007244588412388318771 1936510866882618582478157)
              ·
                refine ⟨726191575080981968429309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1936510866882618582478157 726191575080981968429309)
                ·
                  refine ⟨272321840655368238160991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726191575080981968429309 272321840655368238160991)
                  ·
                    rfl

theorem cell21_1193276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_1193276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193276 prefixEnd_1193276 := by exact prefixLift 1193276
  have htrace : WordTrace (prefixWord ++ tailWord_1193276) baseStart_1193276 baseEnd_1193276 := by
    simpa [prefixWord, tailWord_1193276, baseEnd_1193276] using wordTrace_append hprefix tailTrace_1193276
  have hstable : (prefixWord ++ tailWord_1193276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193276).length < 2 ^ (prefixWord ++ tailWord_1193276).sum := by decide
  have hdescent : baseEnd_1193276 < baseStart_1193276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193287 : List Nat := [1, 1, 4, 1, 2, 5, 7]
def baseStart_1193287 : Nat := 118140960795 + 1193287 * 2 ^ 59
def prefixEnd_1193287 : Nat := 4983230072969 + 3 ^ 40 * 1193287 * 2
def baseEnd_1193287 : Nat := 30258261222803851497515

theorem tailTrace_1193287 : CollatzResearch.WordTrace tailWord_1193287 prefixEnd_1193287 30258261222803851497515 := by
  unfold tailWord_1193287
  simp only [CollatzResearch.WordTrace]
  refine ⟨43522752427932471039586115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29015168285288314026390743 43522752427932471039586115)
  ·
    refine ⟨65284128641898706559379173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43522752427932471039586115 65284128641898706559379173)
    ·
      refine ⟨12240774120356007479883595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65284128641898706559379173 12240774120356007479883595)
      ·
        refine ⟨18361161180534011219825393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240774120356007479883595 18361161180534011219825393)
        ·
          refine ⟨13770870885400508414869045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18361161180534011219825393 13770870885400508414869045)
          ·
            refine ⟨1291019145506297663893973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13770870885400508414869045 1291019145506297663893973)
            ·
              refine ⟨30258261222803851497515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1291019145506297663893973 30258261222803851497515)
              ·
                rfl

theorem cell21_1193287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 7].length) (baseStart_1193287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193287 prefixEnd_1193287 := by exact prefixLift 1193287
  have htrace : WordTrace (prefixWord ++ tailWord_1193287) baseStart_1193287 baseEnd_1193287 := by
    simpa [prefixWord, tailWord_1193287, baseEnd_1193287] using wordTrace_append hprefix tailTrace_1193287
  have hstable : (prefixWord ++ tailWord_1193287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193287).length < 2 ^ (prefixWord ++ tailWord_1193287).sum := by decide
  have hdescent : baseEnd_1193287 < baseStart_1193287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193293 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1193293 : Nat := 118140960795 + 1193293 * 2 ^ 59
def prefixEnd_1193293 : Nat := 4983230072969 + 3 ^ 40 * 1193293 * 2
def baseEnd_1193293 : Nat := 272325720286979986377623

theorem tailTrace_1193293 : CollatzResearch.WordTrace tailWord_1193293 prefixEnd_1193293 272325720286979986377623 := by
  unfold tailWord_1193293
  simp only [CollatzResearch.WordTrace]
  refine ⟨43522971265910734064304533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29015314177273822709536355 43522971265910734064304533)
  ·
    refine ⟨2040139278089565659264275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43522971265910734064304533 2040139278089565659264275)
    ·
      refine ⟨3060208917134348488896413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040139278089565659264275 3060208917134348488896413)
      ·
        refine ⟨1147578343925380683336155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3060208917134348488896413 1147578343925380683336155)
        ·
          refine ⟨1721367515888071025004233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147578343925380683336155 1721367515888071025004233)
          ·
            refine ⟨1291025636916053268753175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721367515888071025004233 1291025636916053268753175)
            ·
              refine ⟨1936538455374079903129763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291025636916053268753175 1936538455374079903129763)
              ·
                refine ⟨2904807683061119854694645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936538455374079903129763 2904807683061119854694645)
                ·
                  refine ⟨272325720286979986377623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904807683061119854694645 272325720286979986377623)
                  ·
                    rfl

theorem cell21_1193293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1193293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193293 prefixEnd_1193293 := by exact prefixLift 1193293
  have htrace : WordTrace (prefixWord ++ tailWord_1193293) baseStart_1193293 baseEnd_1193293 := by
    simpa [prefixWord, tailWord_1193293, baseEnd_1193293] using wordTrace_append hprefix tailTrace_1193293
  have hstable : (prefixWord ++ tailWord_1193293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193293).length < 2 ^ (prefixWord ++ tailWord_1193293).sum := by decide
  have hdescent : baseEnd_1193293 < baseStart_1193293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193352 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_1193352 : Nat := 118140960795 + 1193352 * 2 ^ 59
def prefixEnd_1193352 : Nat := 4983230072969 + 3 ^ 40 * 1193352 * 2
def baseEnd_1193352 : Nat := 272339184890808994894169

theorem tailTrace_1193352 : CollatzResearch.WordTrace tailWord_1193352 prefixEnd_1193352 272339184890808994894169 := by
  unfold tailWord_1193352
  simp only [CollatzResearch.WordTrace]
  refine ⟨21762561586348493570351155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29016748781797991427134873 21762561586348493570351155)
  ·
    refine ⟨32643842379522740355526733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21762561586348493570351155 32643842379522740355526733)
    ·
      refine ⟨12241440892321027633322525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32643842379522740355526733 12241440892321027633322525)
      ·
        refine ⟨4590540334620385362495947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12241440892321027633322525 4590540334620385362495947)
        ·
          refine ⟨6885810501930578043743921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4590540334620385362495947 6885810501930578043743921)
          ·
            refine ⟨5164357876447933532807941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885810501930578043743921 5164357876447933532807941)
            ·
              refine ⟨968317101833987537401489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5164357876447933532807941 968317101833987537401489)
              ·
                refine ⟨726237826375490653051117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 968317101833987537401489 726237826375490653051117)
                ·
                  refine ⟨272339184890808994894169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726237826375490653051117 272339184890808994894169)
                  ·
                    rfl

theorem cell21_1193352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_1193352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193352 prefixEnd_1193352 := by exact prefixLift 1193352
  have htrace : WordTrace (prefixWord ++ tailWord_1193352) baseStart_1193352 baseEnd_1193352 := by
    simpa [prefixWord, tailWord_1193352, baseEnd_1193352] using wordTrace_append hprefix tailTrace_1193352
  have hstable : (prefixWord ++ tailWord_1193352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193352).length < 2 ^ (prefixWord ++ tailWord_1193352).sum := by decide
  have hdescent : baseEnd_1193352 < baseStart_1193352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193476 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1193476 : Nat := 118140960795 + 1193476 * 2 ^ 59
def prefixEnd_1193476 : Nat := 4983230072969 + 3 ^ 40 * 1193476 * 2
def baseEnd_1193476 : Nat := 272367483380212334827249

theorem tailTrace_1193476 : CollatzResearch.WordTrace tailWord_1193476 prefixEnd_1193476 272367483380212334827249 := by
  unfold tailWord_1193476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21764822912123878159108141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29019763882831837545477521 21764822912123878159108141)
  ·
    refine ⟨8161808592046454309665553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21764822912123878159108141 8161808592046454309665553)
    ·
      refine ⟨6121356444034840732249165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8161808592046454309665553 6121356444034840732249165)
      ·
        refine ⟨2295508666513065274593437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6121356444034840732249165 2295508666513065274593437)
        ·
          refine ⟨860815749942399477972539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2295508666513065274593437 860815749942399477972539)
          ·
            refine ⟨1291223624913599216958809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 860815749942399477972539 1291223624913599216958809)
            ·
              refine ⟨968417718685199412719107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1291223624913599216958809 968417718685199412719107)
              ·
                refine ⟨1452626578027799119078661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968417718685199412719107 1452626578027799119078661)
                ·
                  refine ⟨272367483380212334827249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452626578027799119078661 272367483380212334827249)
                  ·
                    rfl

theorem cell21_1193476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1193476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193476 prefixEnd_1193476 := by exact prefixLift 1193476
  have htrace : WordTrace (prefixWord ++ tailWord_1193476) baseStart_1193476 baseEnd_1193476 := by
    simpa [prefixWord, tailWord_1193476, baseEnd_1193476] using wordTrace_append hprefix tailTrace_1193476
  have hstable : (prefixWord ++ tailWord_1193476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193476).length < 2 ^ (prefixWord ++ tailWord_1193476).sum := by decide
  have hdescent : baseEnd_1193476 < baseStart_1193476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193518 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1193518 : Nat := 118140960795 + 1193518 * 2 ^ 59
def prefixEnd_1193518 : Nat := 4983230072969 + 3 ^ 40 * 1193518 * 2
def baseEnd_1193518 : Nat := 272377068352429595127163

theorem tailTrace_1193518 : CollatzResearch.WordTrace tailWord_1193518 prefixEnd_1193518 272377068352429595127163 := by
  unfold tailWord_1193518
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441397211261949686405651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29020785126730398327496805 5441397211261949686405651)
  ·
    refine ⟨8162095816892924529608477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441397211261949686405651 8162095816892924529608477)
    ·
      refine ⟨3060785931334846698603179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8162095816892924529608477 3060785931334846698603179)
      ·
        refine ⟨4591178897002270047904769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060785931334846698603179 4591178897002270047904769)
        ·
          refine ⟨3443384172751702535928577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591178897002270047904769 3443384172751702535928577)
          ·
            refine ⟨2582538129563776901946433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3443384172751702535928577 2582538129563776901946433)
            ·
              refine ⟨1936903597172832676459825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582538129563776901946433 1936903597172832676459825)
              ·
                refine ⟨1452677697879624507344869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936903597172832676459825 1452677697879624507344869)
                ·
                  refine ⟨272377068352429595127163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452677697879624507344869 272377068352429595127163)
                  ·
                    rfl

theorem cell21_1193518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1193518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193518 prefixEnd_1193518 := by exact prefixLift 1193518
  have htrace : WordTrace (prefixWord ++ tailWord_1193518) baseStart_1193518 baseEnd_1193518 := by
    simpa [prefixWord, tailWord_1193518, baseEnd_1193518] using wordTrace_append hprefix tailTrace_1193518
  have hstable : (prefixWord ++ tailWord_1193518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193518).length < 2 ^ (prefixWord ++ tailWord_1193518).sum := by decide
  have hdescent : baseEnd_1193518 < baseStart_1193518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193532 : List Nat := [2, 2, 2, 2, 4, 2, 1, 6]
def baseStart_1193532 : Nat := 118140960795 + 1193532 * 2 ^ 59
def prefixEnd_1193532 : Nat := 4983230072969 + 3 ^ 40 * 1193532 * 2
def baseEnd_1193532 : Nat := 90793421114389560631267

theorem tailTrace_1193532 : CollatzResearch.WordTrace tailWord_1193532 prefixEnd_1193532 90793421114389560631267 := by
  unfold tailWord_1193532
  simp only [CollatzResearch.WordTrace]
  refine ⟨21765844156022438941127425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29021125541363251921503233 21765844156022438941127425)
  ·
    refine ⟨16324383117016829205845569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21765844156022438941127425 16324383117016829205845569)
    ·
      refine ⟨12243287337762621904384177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16324383117016829205845569 12243287337762621904384177)
      ·
        refine ⟨9182465503321966428288133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12243287337762621904384177 9182465503321966428288133)
        ·
          refine ⟨1721712281872868705304025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9182465503321966428288133 1721712281872868705304025)
          ·
            refine ⟨1291284211404651528978019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1721712281872868705304025 1291284211404651528978019)
            ·
              refine ⟨1936926317106977293467029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1291284211404651528978019 1936926317106977293467029)
              ·
                refine ⟨90793421114389560631267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1936926317106977293467029 90793421114389560631267)
                ·
                  rfl

theorem cell21_1193532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_1193532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193532 prefixEnd_1193532 := by exact prefixLift 1193532
  have htrace : WordTrace (prefixWord ++ tailWord_1193532) baseStart_1193532 baseEnd_1193532 := by
    simpa [prefixWord, tailWord_1193532, baseEnd_1193532] using wordTrace_append hprefix tailTrace_1193532
  have hstable : (prefixWord ++ tailWord_1193532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193532).length < 2 ^ (prefixWord ++ tailWord_1193532).sum := by decide
  have hdescent : baseEnd_1193532 < baseStart_1193532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193549 : List Nat := [1, 6, 1, 1, 3, 1, 3, 5]
def baseStart_1193549 : Nat := 118140960795 + 1193549 * 2 ^ 59
def prefixEnd_1193549 : Nat := 4983230072969 + 3 ^ 40 * 1193549 * 2
def baseEnd_1193549 : Nat := 90794714324926810036811

theorem tailTrace_1193549 : CollatzResearch.WordTrace tailWord_1193549 prefixEnd_1193549 90794714324926810036811 := by
  unfold tailWord_1193549
  simp only [CollatzResearch.WordTrace]
  refine ⟨43532308352983289785623701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29021538901988859857082467 43532308352983289785623701)
  ·
    refine ⟨2040576954046091708701111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43532308352983289785623701 2040576954046091708701111)
    ·
      refine ⟨3060865431069137563051667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040576954046091708701111 3060865431069137563051667)
      ·
        refine ⟨4591298146603706344577501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060865431069137563051667 4591298146603706344577501)
        ·
          refine ⟨1721736804976389879216563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4591298146603706344577501 1721736804976389879216563)
          ·
            refine ⟨2582605207464584818824845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721736804976389879216563 2582605207464584818824845)
            ·
              refine ⟨968476952799219307059317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2582605207464584818824845 968476952799219307059317)
              ·
                refine ⟨90794714324926810036811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 968476952799219307059317 90794714324926810036811)
                ·
                  rfl

theorem cell21_1193549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 5].length) (baseStart_1193549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193549 prefixEnd_1193549 := by exact prefixLift 1193549
  have htrace : WordTrace (prefixWord ++ tailWord_1193549) baseStart_1193549 baseEnd_1193549 := by
    simpa [prefixWord, tailWord_1193549, baseEnd_1193549] using wordTrace_append hprefix tailTrace_1193549
  have hstable : (prefixWord ++ tailWord_1193549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193549).length < 2 ^ (prefixWord ++ tailWord_1193549).sum := by decide
  have hdescent : baseEnd_1193549 < baseStart_1193549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193605 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1193605 : Nat := 118140960795 + 1193605 * 2 ^ 59
def prefixEnd_1193605 : Nat := 4983230072969 + 3 ^ 40 * 1193605 * 2
def baseEnd_1193605 : Nat := 272396922937736777176985

theorem tailTrace_1193605 : CollatzResearch.WordTrace tailWord_1193605 prefixEnd_1193605 272396922937736777176985 := by
  unfold tailWord_1193605
  simp only [CollatzResearch.WordTrace]
  refine ⟨43534350840780411349662269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29022900560520274233108179 43534350840780411349662269)
  ·
    refine ⟨16325381565292654256123351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43534350840780411349662269 16325381565292654256123351)
    ·
      refine ⟨24488072347938981384185027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16325381565292654256123351 24488072347938981384185027)
      ·
        refine ⟨36732108521908472076277541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24488072347938981384185027 36732108521908472076277541)
        ·
          refine ⟨6887270347857838514302039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36732108521908472076277541 6887270347857838514302039)
          ·
            refine ⟨10330905521786757771453059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887270347857838514302039 10330905521786757771453059)
            ·
              refine ⟨15496358282680136657179589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10330905521786757771453059 15496358282680136657179589)
              ·
                refine ⟨2905567178002525623221173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15496358282680136657179589 2905567178002525623221173)
                ·
                  refine ⟨272396922937736777176985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2905567178002525623221173 272396922937736777176985)
                  ·
                    rfl

theorem cell21_1193605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1193605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193605 prefixEnd_1193605 := by exact prefixLift 1193605
  have htrace : WordTrace (prefixWord ++ tailWord_1193605) baseStart_1193605 baseEnd_1193605 := by
    simpa [prefixWord, tailWord_1193605, baseEnd_1193605] using wordTrace_append hprefix tailTrace_1193605
  have hstable : (prefixWord ++ tailWord_1193605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193605).length < 2 ^ (prefixWord ++ tailWord_1193605).sum := by decide
  have hdescent : baseEnd_1193605 < baseStart_1193605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193608 : List Nat := [2, 1, 3, 5, 1, 1, 1, 7]
def baseStart_1193608 : Nat := 118140960795 + 1193608 * 2 ^ 59
def prefixEnd_1193608 : Nat := 4983230072969 + 3 ^ 40 * 1193608 * 2
def baseEnd_1193608 : Nat := 90799202526203146208993

theorem tailTrace_1193608 : CollatzResearch.WordTrace tailWord_1193608 prefixEnd_1193608 90799202526203146208993 := by
  unfold tailWord_1193608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21767230129884771431010739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29022973506513028574680985 21767230129884771431010739)
  ·
    refine ⟨32650845194827157146516109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21767230129884771431010739 32650845194827157146516109)
    ·
      refine ⟨12244066948060183929943541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32650845194827157146516109 12244066948060183929943541)
      ·
        refine ⟨1147881276380642243432207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12244066948060183929943541 1147881276380642243432207)
        ·
          refine ⟨1721821914570963365148311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1147881276380642243432207 1721821914570963365148311)
          ·
            refine ⟨2582732871856445047722467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721821914570963365148311 2582732871856445047722467)
            ·
              refine ⟨3874099307784667571583701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582732871856445047722467 3874099307784667571583701)
              ·
                refine ⟨90799202526203146208993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3874099307784667571583701 90799202526203146208993)
                ·
                  rfl

theorem cell21_1193608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_1193608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193608 prefixEnd_1193608 := by exact prefixLift 1193608
  have htrace : WordTrace (prefixWord ++ tailWord_1193608) baseStart_1193608 baseEnd_1193608 := by
    simpa [prefixWord, tailWord_1193608, baseEnd_1193608] using wordTrace_append hprefix tailTrace_1193608
  have hstable : (prefixWord ++ tailWord_1193608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193608).length < 2 ^ (prefixWord ++ tailWord_1193608).sum := by decide
  have hdescent : baseEnd_1193608 < baseStart_1193608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193636 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_1193636 : Nat := 118140960795 + 1193636 * 2 ^ 59
def prefixEnd_1193636 : Nat := 4983230072969 + 3 ^ 40 * 1193636 * 2
def baseEnd_1193636 : Nat := 272403997560087612160255

theorem tailTrace_1193636 : CollatzResearch.WordTrace tailWord_1193636 prefixEnd_1193636 272403997560087612160255 := by
  unfold tailWord_1193636
  simp only [CollatzResearch.WordTrace]
  refine ⟨21767740751834051822020381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29023654335778735762693841 21767740751834051822020381)
  ·
    refine ⟨8162902781937769433257643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21767740751834051822020381 8162902781937769433257643)
    ·
      refine ⟨12244354172906654149886465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8162902781937769433257643 12244354172906654149886465)
      ·
        refine ⟨9183265629679990612414849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12244354172906654149886465 9183265629679990612414849)
        ·
          refine ⟨6887449222259992959311137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9183265629679990612414849 6887449222259992959311137)
          ·
            refine ⟨5165586916694994719483353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6887449222259992959311137 5165586916694994719483353)
            ·
              refine ⟨3874190187521246039612515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165586916694994719483353 3874190187521246039612515)
              ·
                refine ⟨5811285281281869059418773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874190187521246039612515 5811285281281869059418773)
                ·
                  refine ⟨272403997560087612160255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5811285281281869059418773 272403997560087612160255)
                  ·
                    rfl

theorem cell21_1193636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_1193636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193636 prefixEnd_1193636 := by exact prefixLift 1193636
  have htrace : WordTrace (prefixWord ++ tailWord_1193636) baseStart_1193636 baseEnd_1193636 := by
    simpa [prefixWord, tailWord_1193636, baseEnd_1193636] using wordTrace_append hprefix tailTrace_1193636
  have hstable : (prefixWord ++ tailWord_1193636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193636).length < 2 ^ (prefixWord ++ tailWord_1193636).sum := by decide
  have hdescent : baseEnd_1193636 < baseStart_1193636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193650 : List Nat := [3, 2, 1, 1, 1, 2, 3, 8]
def baseStart_1193650 : Nat := 118140960795 + 1193650 * 2 ^ 59
def prefixEnd_1193650 : Nat := 4983230072969 + 3 ^ 40 * 1193650 * 2
def baseEnd_1193650 : Nat := 90802397516942232975631

theorem tailTrace_1193650 : CollatzResearch.WordTrace tailWord_1193650 prefixEnd_1193650 90802397516942232975631 := by
  unfold tailWord_1193650
  simp only [CollatzResearch.WordTrace]
  refine ⟨10883998031404346008762601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29023994750411589356700269 10883998031404346008762601)
  ·
    refine ⟨8162998523553259506571951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10883998031404346008762601 8162998523553259506571951)
    ·
      refine ⟨12244497785329889259857927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8162998523553259506571951 12244497785329889259857927)
      ·
        refine ⟨18366746677994833889786891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12244497785329889259857927 18366746677994833889786891)
        ·
          refine ⟨27550120016992250834680337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18366746677994833889786891 27550120016992250834680337)
          ·
            refine ⟨20662590012744188126010253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27550120016992250834680337 20662590012744188126010253)
            ·
              refine ⟨7748471254779070547253845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20662590012744188126010253 7748471254779070547253845)
              ·
                refine ⟨90802397516942232975631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7748471254779070547253845 90802397516942232975631)
                ·
                  rfl

theorem cell21_1193650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_1193650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193650 prefixEnd_1193650 := by exact prefixLift 1193650
  have htrace : WordTrace (prefixWord ++ tailWord_1193650) baseStart_1193650 baseEnd_1193650 := by
    simpa [prefixWord, tailWord_1193650, baseEnd_1193650] using wordTrace_append hprefix tailTrace_1193650
  have hstable : (prefixWord ++ tailWord_1193650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193650).length < 2 ^ (prefixWord ++ tailWord_1193650).sum := by decide
  have hdescent : baseEnd_1193650 < baseStart_1193650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193746 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1193746 : Nat := 118140960795 + 1193746 * 2 ^ 59
def prefixEnd_1193746 : Nat := 4983230072969 + 3 ^ 40 * 1193746 * 2
def baseEnd_1193746 : Nat := 272429101058751865326697

theorem tailTrace_1193746 : CollatzResearch.WordTrace tailWord_1193746 prefixEnd_1193746 272429101058751865326697 := by
  unfold tailWord_1193746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10884873383317398107636273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29026329022179728287030061 10884873383317398107636273)
  ·
    refine ⟨8163655037488048580727205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10884873383317398107636273 8163655037488048580727205)
    ·
      refine ⟨1530685319529009108886351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8163655037488048580727205 1530685319529009108886351)
      ·
        refine ⟨2296027979293513663329527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1530685319529009108886351 2296027979293513663329527)
        ·
          refine ⟨3444041968940270494994291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296027979293513663329527 3444041968940270494994291)
          ·
            refine ⟨5166062953410405742491437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444041968940270494994291 5166062953410405742491437)
            ·
              refine ⟨1937273607528902153434289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5166062953410405742491437 1937273607528902153434289)
              ·
                refine ⟨1452955205646676615075717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937273607528902153434289 1452955205646676615075717)
                ·
                  refine ⟨272429101058751865326697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452955205646676615075717 272429101058751865326697)
                  ·
                    rfl

theorem cell21_1193746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1193746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193746 prefixEnd_1193746 := by exact prefixLift 1193746
  have htrace : WordTrace (prefixWord ++ tailWord_1193746) baseStart_1193746 baseEnd_1193746 := by
    simpa [prefixWord, tailWord_1193746, baseEnd_1193746] using wordTrace_append hprefix tailTrace_1193746
  have hstable : (prefixWord ++ tailWord_1193746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193746).length < 2 ^ (prefixWord ++ tailWord_1193746).sum := by decide
  have hdescent : baseEnd_1193746 < baseStart_1193746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193805 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1193805 : Nat := 118140960795 + 1193805 * 2 ^ 59
def prefixEnd_1193805 : Nat := 4983230072969 + 3 ^ 40 * 1193805 * 2
def baseEnd_1193805 : Nat := 272442565662580873843243

theorem tailTrace_1193805 : CollatzResearch.WordTrace tailWord_1193805 prefixEnd_1193805 272442565662580873843243 := by
  unfold tailWord_1193805
  simp only [CollatzResearch.WordTrace]
  refine ⟨43541645440055845506942869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29027763626703897004628579 43541645440055845506942869)
  ·
    refine ⟨2041014630002617758137947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43541645440055845506942869 2041014630002617758137947)
    ·
      refine ⟨3061521945003926637206921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041014630002617758137947 3061521945003926637206921)
      ·
        refine ⟨2296141458752944977905191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061521945003926637206921 2296141458752944977905191)
        ·
          refine ⟨3444212188129417466857787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296141458752944977905191 3444212188129417466857787)
          ·
            refine ⟨5166318282194126200286681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3444212188129417466857787 5166318282194126200286681)
            ·
              refine ⟨3874738711645594650215011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166318282194126200286681 3874738711645594650215011)
              ·
                refine ⟨5812108067468391975322517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874738711645594650215011 5812108067468391975322517)
                ·
                  refine ⟨272442565662580873843243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5812108067468391975322517 272442565662580873843243)
                  ·
                    rfl

theorem cell21_1193805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1193805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193805 prefixEnd_1193805 := by exact prefixLift 1193805
  have htrace : WordTrace (prefixWord ++ tailWord_1193805) baseStart_1193805 baseEnd_1193805 := by
    simpa [prefixWord, tailWord_1193805, baseEnd_1193805] using wordTrace_append hprefix tailTrace_1193805
  have hstable : (prefixWord ++ tailWord_1193805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193805).length < 2 ^ (prefixWord ++ tailWord_1193805).sum := by decide
  have hdescent : baseEnd_1193805 < baseStart_1193805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193968 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_1193968 : Nat := 118140960795 + 1193968 * 2 ^ 59
def prefixEnd_1193968 : Nat := 4983230072969 + 3 ^ 40 * 1193968 * 2
def baseEnd_1193968 : Nat := 272479764483328812626243

theorem tailTrace_1193968 : CollatzResearch.WordTrace tailWord_1193968 prefixEnd_1193968 272479764483328812626243 := by
  unfold tailWord_1193968
  simp only [CollatzResearch.WordTrace]
  refine ⟨21773795269232662172563279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29031727025643549563417705 21773795269232662172563279)
  ·
    refine ⟨32660692903848993258844919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21773795269232662172563279 32660692903848993258844919)
    ·
      refine ⟨48991039355773489888267379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32660692903848993258844919 48991039355773489888267379)
      ·
        refine ⟨73486559033660234832401069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48991039355773489888267379 73486559033660234832401069)
        ·
          refine ⟨27557459637622588062150401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73486559033660234832401069 27557459637622588062150401)
          ·
            refine ⟨20668094728216941046612801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27557459637622588062150401 20668094728216941046612801)
            ·
              refine ⟨15501071046162705784959601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20668094728216941046612801 15501071046162705784959601)
              ·
                refine ⟨11625803284622029338719701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15501071046162705784959601 11625803284622029338719701)
                ·
                  refine ⟨272479764483328812626243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11625803284622029338719701 272479764483328812626243)
                  ·
                    rfl

theorem cell21_1193968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_1193968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193968 prefixEnd_1193968 := by exact prefixLift 1193968
  have htrace : WordTrace (prefixWord ++ tailWord_1193968) baseStart_1193968 baseEnd_1193968 := by
    simpa [prefixWord, tailWord_1193968, baseEnd_1193968] using wordTrace_append hprefix tailTrace_1193968
  have hstable : (prefixWord ++ tailWord_1193968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193968).length < 2 ^ (prefixWord ++ tailWord_1193968).sum := by decide
  have hdescent : baseEnd_1193968 < baseStart_1193968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1193988 : List Nat := [2, 3, 2, 4, 1, 1, 2, 6]
def baseStart_1193988 : Nat := 118140960795 + 1193988 * 2 ^ 59
def prefixEnd_1193988 : Nat := 4983230072969 + 3 ^ 40 * 1193988 * 2
def baseEnd_1193988 : Nat := 90828109585271074097623

theorem tailTrace_1193988 : CollatzResearch.WordTrace tailWord_1193988 prefixEnd_1193988 90828109585271074097623 := by
  unfold tailWord_1193988
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774159999196433880427309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29032213332261911840569745 21774159999196433880427309)
  ·
    refine ⟨8165309999698662705160241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21774159999196433880427309 8165309999698662705160241)
    ·
      refine ⟨6123982499773997028870181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165309999698662705160241 6123982499773997028870181)
      ·
        refine ⟨1148246718707624442913159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6123982499773997028870181 1148246718707624442913159)
        ·
          refine ⟨1722370078061436664369739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1148246718707624442913159 1722370078061436664369739)
          ·
            refine ⟨2583555117092154996554609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722370078061436664369739 2583555117092154996554609)
            ·
              refine ⟨1937666337819116247415957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583555117092154996554609 1937666337819116247415957)
              ·
                refine ⟨90828109585271074097623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1937666337819116247415957 90828109585271074097623)
                ·
                  rfl

theorem cell21_1193988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_1193988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1193988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1193988 prefixEnd_1193988 := by exact prefixLift 1193988
  have htrace : WordTrace (prefixWord ++ tailWord_1193988) baseStart_1193988 baseEnd_1193988 := by
    simpa [prefixWord, tailWord_1193988, baseEnd_1193988] using wordTrace_append hprefix tailTrace_1193988
  have hstable : (prefixWord ++ tailWord_1193988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1193988).length < 2 ^ (prefixWord ++ tailWord_1193988).sum := by decide
  have hdescent : baseEnd_1193988 < baseStart_1193988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1193988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194030 : List Nat := [4, 1, 3, 1, 1, 11]
def baseStart_1194030 : Nat := 118140960795 + 1194030 * 2 ^ 59
def prefixEnd_1194030 : Nat := 4983230072969 + 3 ^ 40 * 1194030 * 2
def baseEnd_1194030 : Nat := 10092367175112240096029

theorem tailTrace_1194030 : CollatzResearch.WordTrace tailWord_1194030 prefixEnd_1194030 10092367175112240096029 := by
  unfold tailWord_1194030
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443731483030088616735443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29033234576160472622589029 5443731483030088616735443)
  ·
    refine ⟨8165597224545132925103165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443731483030088616735443 8165597224545132925103165)
    ·
      refine ⟨3062098959204424846913687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8165597224545132925103165 3062098959204424846913687)
      ·
        refine ⟨4593148438806637270370531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062098959204424846913687 4593148438806637270370531)
        ·
          refine ⟨6889722658209955905555797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4593148438806637270370531 6889722658209955905555797)
          ·
            refine ⟨10092367175112240096029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6889722658209955905555797 10092367175112240096029)
            ·
              rfl

theorem cell21_1194030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 11].length) (baseStart_1194030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194030 prefixEnd_1194030 := by exact prefixLift 1194030
  have htrace : WordTrace (prefixWord ++ tailWord_1194030) baseStart_1194030 baseEnd_1194030 := by
    simpa [prefixWord, tailWord_1194030, baseEnd_1194030] using wordTrace_append hprefix tailTrace_1194030
  have hstable : (prefixWord ++ tailWord_1194030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194030).length < 2 ^ (prefixWord ++ tailWord_1194030).sum := by decide
  have hdescent : baseEnd_1194030 < baseStart_1194030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194036 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_1194036 : Nat := 118140960795 + 1194036 * 2 ^ 59
def prefixEnd_1194036 : Nat := 4983230072969 + 3 ^ 40 * 1194036 * 2
def baseEnd_1194036 : Nat := 272495283009775805492771

theorem tailTrace_1194036 : CollatzResearch.WordTrace tailWord_1194036 prefixEnd_1194036 272495283009775805492771 := by
  unfold tailWord_1194036
  simp only [CollatzResearch.WordTrace]
  refine ⟨21775035351109485979300981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29033380468145981305734641 21775035351109485979300981)
  ·
    refine ⟨2041409564166514310559467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21775035351109485979300981 2041409564166514310559467)
    ·
      refine ⟨3062114346249771465839201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041409564166514310559467 3062114346249771465839201)
      ·
        refine ⟨2296585759687328599379401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3062114346249771465839201 2296585759687328599379401)
        ·
          refine ⟨1722439319765496449534551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296585759687328599379401 1722439319765496449534551)
          ·
            refine ⟨2583658979648244674301827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722439319765496449534551 2583658979648244674301827)
            ·
              refine ⟨3875488469472367011452741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583658979648244674301827 3875488469472367011452741)
              ·
                refine ⟨726654088026068814647389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3875488469472367011452741 726654088026068814647389)
                ·
                  refine ⟨272495283009775805492771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726654088026068814647389 272495283009775805492771)
                  ·
                    rfl

theorem cell21_1194036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_1194036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194036 prefixEnd_1194036 := by exact prefixLift 1194036
  have htrace : WordTrace (prefixWord ++ tailWord_1194036) baseStart_1194036 baseEnd_1194036 := by
    simpa [prefixWord, tailWord_1194036, baseEnd_1194036] using wordTrace_append hprefix tailTrace_1194036
  have hstable : (prefixWord ++ tailWord_1194036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194036).length < 2 ^ (prefixWord ++ tailWord_1194036).sum := by decide
  have hdescent : baseEnd_1194036 < baseStart_1194036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194089 : List Nat := [1, 2, 1, 1, 1, 5, 10]
def baseStart_1194089 : Nat := 118140960795 + 1194089 * 2 ^ 59
def prefixEnd_1194089 : Nat := 4983230072969 + 3 ^ 40 * 1194089 * 2
def baseEnd_1194089 : Nat := 30278597592428832345481

theorem tailTrace_1194089 : CollatzResearch.WordTrace tailWord_1194089 prefixEnd_1194089 30278597592428832345481 := by
  unfold tailWord_1194089
  simp only [CollatzResearch.WordTrace]
  refine ⟨43552003771026962010281321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29034669180684641340187547 43552003771026962010281321)
  ·
    refine ⟨32664002828270221507710991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43552003771026962010281321 32664002828270221507710991)
    ·
      refine ⟨48996004242405332261566487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32664002828270221507710991 48996004242405332261566487)
      ·
        refine ⟨73494006363607998392349731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48996004242405332261566487 73494006363607998392349731)
        ·
          refine ⟨110241009545411997588524597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73494006363607998392349731 110241009545411997588524597)
          ·
            refine ⟨10335094644882374773924181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110241009545411997588524597 10335094644882374773924181)
            ·
              refine ⟨30278597592428832345481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10335094644882374773924181 30278597592428832345481)
              ·
                rfl

theorem cell21_1194089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 10].length) (baseStart_1194089 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194089 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194089 prefixEnd_1194089 := by exact prefixLift 1194089
  have htrace : WordTrace (prefixWord ++ tailWord_1194089) baseStart_1194089 baseEnd_1194089 := by
    simpa [prefixWord, tailWord_1194089, baseEnd_1194089] using wordTrace_append hprefix tailTrace_1194089
  have hstable : (prefixWord ++ tailWord_1194089).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194089).length < 2 ^ (prefixWord ++ tailWord_1194089).sum := by decide
  have hdescent : baseEnd_1194089 < baseStart_1194089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194092 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_1194092 : Nat := 118140960795 + 1194092 * 2 ^ 59
def prefixEnd_1194092 : Nat := 4983230072969 + 3 ^ 40 * 1194092 * 2
def baseEnd_1194092 : Nat := 272508062972732152559323

theorem tailTrace_1194092 : CollatzResearch.WordTrace tailWord_1194092 prefixEnd_1194092 272508062972732152559323 := by
  unfold tailWord_1194092
  simp only [CollatzResearch.WordTrace]
  refine ⟨21776056595008046761320265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29034742126677395681760353 21776056595008046761320265)
  ·
    refine ⟨16332042446256035070990199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21776056595008046761320265 16332042446256035070990199)
    ·
      refine ⟨24498063669384052606485299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16332042446256035070990199 24498063669384052606485299)
      ·
        refine ⟨36747095504076078909727949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24498063669384052606485299 36747095504076078909727949)
        ·
          refine ⟨13780160814028529591147981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36747095504076078909727949 13780160814028529591147981)
          ·
            refine ⟨5167560305260698596680493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13780160814028529591147981 5167560305260698596680493)
            ·
              refine ⟨1937835114472761973755185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5167560305260698596680493 1937835114472761973755185)
              ·
                refine ⟨1453376335854571480316389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937835114472761973755185 1453376335854571480316389)
                ·
                  refine ⟨272508062972732152559323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453376335854571480316389 272508062972732152559323)
                  ·
                    rfl

theorem cell21_1194092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_1194092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194092 prefixEnd_1194092 := by exact prefixLift 1194092
  have htrace : WordTrace (prefixWord ++ tailWord_1194092) baseStart_1194092 baseEnd_1194092 := by
    simpa [prefixWord, tailWord_1194092, baseEnd_1194092] using wordTrace_append hprefix tailTrace_1194092
  have hstable : (prefixWord ++ tailWord_1194092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194092).length < 2 ^ (prefixWord ++ tailWord_1194092).sum := by decide
  have hdescent : baseEnd_1194092 < baseStart_1194092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194109 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1194109 : Nat := 118140960795 + 1194109 * 2 ^ 59
def prefixEnd_1194109 : Nat := 4983230072969 + 3 ^ 40 * 1194109 * 2
def baseEnd_1194109 : Nat := 272511942604343900775955

theorem tailTrace_1194109 : CollatzResearch.WordTrace tailWord_1194109 prefixEnd_1194109 272511942604343900775955 := by
  unfold tailWord_1194109
  simp only [CollatzResearch.WordTrace]
  refine ⟨43552733230954505426009381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29035155487303003617339587 43552733230954505426009381)
  ·
    refine ⟨8166137480803969767376759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43552733230954505426009381 8166137480803969767376759)
    ·
      refine ⟨12249206221205954651065139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8166137480803969767376759 12249206221205954651065139)
      ·
        refine ⟨18373809331808931976597709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12249206221205954651065139 18373809331808931976597709)
        ·
          refine ⟨6890178499428349491224141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18373809331808931976597709 6890178499428349491224141)
          ·
            refine ⟨2583816937285631059209053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6890178499428349491224141 2583816937285631059209053)
            ·
              refine ⟨968931351482111647203395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2583816937285631059209053 968931351482111647203395)
              ·
                refine ⟨1453397027223167470805093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 968931351482111647203395 1453397027223167470805093)
                ·
                  refine ⟨272511942604343900775955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453397027223167470805093 272511942604343900775955)
                  ·
                    rfl

theorem cell21_1194109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1194109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194109 prefixEnd_1194109 := by exact prefixLift 1194109
  have htrace : WordTrace (prefixWord ++ tailWord_1194109) baseStart_1194109 baseEnd_1194109 := by
    simpa [prefixWord, tailWord_1194109, baseEnd_1194109] using wordTrace_append hprefix tailTrace_1194109
  have hstable : (prefixWord ++ tailWord_1194109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194109).length < 2 ^ (prefixWord ++ tailWord_1194109).sum := by decide
  have hdescent : baseEnd_1194109 < baseStart_1194109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194227 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_1194227 : Nat := 118140960795 + 1194227 * 2 ^ 59
def prefixEnd_1194227 : Nat := 4983230072969 + 3 ^ 40 * 1194227 * 2
def baseEnd_1194227 : Nat := 272538871812001917809047

theorem tailTrace_1194227 : CollatzResearch.WordTrace tailWord_1194227 prefixEnd_1194227 272538871812001917809047 := by
  unfold tailWord_1194227
  simp only [CollatzResearch.WordTrace]
  refine ⟨43557037044527011578804935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29038024696351341052536623 43557037044527011578804935)
  ·
    refine ⟨65335555566790517368207403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43557037044527011578804935 65335555566790517368207403)
    ·
      refine ⟨98003333350185776052311105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65335555566790517368207403 98003333350185776052311105)
      ·
        refine ⟨73502500012639332039233329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98003333350185776052311105 73502500012639332039233329)
        ·
          refine ⟨55126875009479499029424997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73502500012639332039233329 55126875009479499029424997)
          ·
            refine ⟨10336289064277406068017187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55126875009479499029424997 10336289064277406068017187)
            ·
              refine ⟨15504433596416109102025781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10336289064277406068017187 15504433596416109102025781)
              ·
                refine ⟨1453540649664010228314917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15504433596416109102025781 1453540649664010228314917)
                ·
                  refine ⟨272538871812001917809047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453540649664010228314917 272538871812001917809047)
                  ·
                    rfl

theorem cell21_1194227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_1194227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194227 prefixEnd_1194227 := by exact prefixLift 1194227
  have htrace : WordTrace (prefixWord ++ tailWord_1194227) baseStart_1194227 baseEnd_1194227 := by
    simpa [prefixWord, tailWord_1194227, baseEnd_1194227] using wordTrace_append hprefix tailTrace_1194227
  have hstable : (prefixWord ++ tailWord_1194227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194227).length < 2 ^ (prefixWord ++ tailWord_1194227).sum := by decide
  have hdescent : baseEnd_1194227 < baseStart_1194227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194292 : List Nat := [2, 5, 1, 1, 1, 4, 2, 5]
def baseStart_1194292 : Nat := 118140960795 + 1194292 * 2 ^ 59
def prefixEnd_1194292 : Nat := 4983230072969 + 3 ^ 40 * 1194292 * 2
def baseEnd_1194292 : Nat := 90851235232525416408527

theorem tailTrace_1194292 : CollatzResearch.WordTrace tailWord_1194292 prefixEnd_1194292 90851235232525416408527 := by
  unfold tailWord_1194292
  simp only [CollatzResearch.WordTrace]
  refine ⟨21779703894645763839960565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29039605192861018453280753 21779703894645763839960565)
  ·
    refine ⟨2041847240123040359996303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21779703894645763839960565 2041847240123040359996303)
    ·
      refine ⟨3062770860184560539994455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041847240123040359996303 3062770860184560539994455)
      ·
        refine ⟨4594156290276840809991683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062770860184560539994455 4594156290276840809991683)
        ·
          refine ⟨6891234435415261214987525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594156290276840809991683 6891234435415261214987525)
          ·
            refine ⟨1292106456640361477810161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6891234435415261214987525 1292106456640361477810161)
            ·
              refine ⟨969079842480271108357621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1292106456640361477810161 969079842480271108357621)
              ·
                refine ⟨90851235232525416408527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 969079842480271108357621 90851235232525416408527)
                ·
                  rfl

theorem cell21_1194292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_1194292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194292 prefixEnd_1194292 := by exact prefixLift 1194292
  have htrace : WordTrace (prefixWord ++ tailWord_1194292) baseStart_1194292 baseEnd_1194292 := by
    simpa [prefixWord, tailWord_1194292, baseEnd_1194292] using wordTrace_append hprefix tailTrace_1194292
  have hstable : (prefixWord ++ tailWord_1194292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194292).length < 2 ^ (prefixWord ++ tailWord_1194292).sum := by decide
  have hdescent : baseEnd_1194292 < baseStart_1194292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194379 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_1194379 : Nat := 118140960795 + 1194379 * 2 ^ 59
def prefixEnd_1194379 : Nat := 4983230072969 + 3 ^ 40 * 1194379 * 2
def baseEnd_1194379 : Nat := 272573560282883431275403

theorem tailTrace_1194379 : CollatzResearch.WordTrace tailWord_1194379 prefixEnd_1194379 272573560282883431275403 := by
  unfold tailWord_1194379
  simp only [CollatzResearch.WordTrace]
  refine ⟨43562580939976341538338191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29041720626650894358892127 43562580939976341538338191)
  ·
    refine ⟨65343871409964512307507287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43562580939976341538338191 65343871409964512307507287)
    ·
      refine ⟨98015807114946768461260931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65343871409964512307507287 98015807114946768461260931)
      ·
        refine ⟨147023710672420152691891397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98015807114946768461260931 147023710672420152691891397)
        ·
          refine ⟨27566945751078778629729637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147023710672420152691891397 27566945751078778629729637)
          ·
            refine ⟨5168802328327270993074307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27566945751078778629729637 5168802328327270993074307)
            ·
              refine ⟨7753203492490906489611461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168802328327270993074307 7753203492490906489611461)
              ·
                refine ⟨1453725654842044966802149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7753203492490906489611461 1453725654842044966802149)
                ·
                  refine ⟨272573560282883431275403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453725654842044966802149 272573560282883431275403)
                  ·
                    rfl

theorem cell21_1194379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_1194379 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194379 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194379 prefixEnd_1194379 := by exact prefixLift 1194379
  have htrace : WordTrace (prefixWord ++ tailWord_1194379) baseStart_1194379 baseEnd_1194379 := by
    simpa [prefixWord, tailWord_1194379, baseEnd_1194379] using wordTrace_append hprefix tailTrace_1194379
  have hstable : (prefixWord ++ tailWord_1194379).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194379).length < 2 ^ (prefixWord ++ tailWord_1194379).sum := by decide
  have hdescent : baseEnd_1194379 < baseStart_1194379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194441 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 3]
def baseStart_1194441 : Nat := 118140960795 + 1194441 * 2 ^ 59
def prefixEnd_1194441 : Nat := 4983230072969 + 3 ^ 40 * 1194441 * 2
def baseEnd_1194441 : Nat := 272587709527585101241943

theorem tailTrace_1194441 : CollatzResearch.WordTrace tailWord_1194441 prefixEnd_1194441 272587709527585101241943 := by
  unfold tailWord_1194441
  simp only [CollatzResearch.WordTrace]
  refine ⟨43564842265751726127095177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29043228177167817418063451 43564842265751726127095177)
  ·
    refine ⟨32673631699313794595321383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43564842265751726127095177 32673631699313794595321383)
    ·
      refine ⟨49010447548970691892982075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32673631699313794595321383 49010447548970691892982075)
      ·
        refine ⟨73515671323456037839473113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49010447548970691892982075 73515671323456037839473113)
        ·
          refine ⟨55136753492592028379604835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73515671323456037839473113 55136753492592028379604835)
          ·
            refine ⟨82705130238888042569407253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55136753492592028379604835 82705130238888042569407253)
            ·
              refine ⟨3876802979947876995440965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82705130238888042569407253 3876802979947876995440965)
              ·
                refine ⟨726900558740226936645181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3876802979947876995440965 726900558740226936645181)
                ·
                  refine ⟨272587709527585101241943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726900558740226936645181 272587709527585101241943)
                  ·
                    rfl

theorem cell21_1194441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_1194441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194441 prefixEnd_1194441 := by exact prefixLift 1194441
  have htrace : WordTrace (prefixWord ++ tailWord_1194441) baseStart_1194441 baseEnd_1194441 := by
    simpa [prefixWord, tailWord_1194441, baseEnd_1194441] using wordTrace_append hprefix tailTrace_1194441
  have hstable : (prefixWord ++ tailWord_1194441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194441).length < 2 ^ (prefixWord ++ tailWord_1194441).sum := by decide
  have hdescent : baseEnd_1194441 < baseStart_1194441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194593 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 3]
def baseStart_1194593 : Nat := 118140960795 + 1194593 * 2 ^ 59
def prefixEnd_1194593 : Nat := 4983230072969 + 3 ^ 40 * 1194593 * 2
def baseEnd_1194593 : Nat := 272622397998466614708299

theorem tailTrace_1194593 : CollatzResearch.WordTrace tailWord_1194593 prefixEnd_1194593 272622397998466614708299 := by
  unfold tailWord_1194593
  simp only [CollatzResearch.WordTrace]
  refine ⟨43570386161201056086628433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29046924107467370724418955 43570386161201056086628433)
  ·
    refine ⟨32677789620900792064971325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43570386161201056086628433 32677789620900792064971325)
    ·
      refine ⟨12254171107837797024364247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32677789620900792064971325 12254171107837797024364247)
      ·
        refine ⟨18381256661756695536546371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12254171107837797024364247 18381256661756695536546371)
        ·
          refine ⟨27571884992635043304819557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18381256661756695536546371 27571884992635043304819557)
          ·
            refine ⟨5169728436119070619653667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27571884992635043304819557 5169728436119070619653667)
            ·
              refine ⟨7754592654178605929480501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5169728436119070619653667 7754592654178605929480501)
              ·
                refine ⟨726993061329244305888797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7754592654178605929480501 726993061329244305888797)
                ·
                  refine ⟨272622397998466614708299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 726993061329244305888797 272622397998466614708299)
                  ·
                    rfl

theorem cell21_1194593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_1194593 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194593 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194593 prefixEnd_1194593 := by exact prefixLift 1194593
  have htrace : WordTrace (prefixWord ++ tailWord_1194593) baseStart_1194593 baseEnd_1194593 := by
    simpa [prefixWord, tailWord_1194593, baseEnd_1194593] using wordTrace_append hprefix tailTrace_1194593
  have hstable : (prefixWord ++ tailWord_1194593).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194593).length < 2 ^ (prefixWord ++ tailWord_1194593).sum := by decide
  have hdescent : baseEnd_1194593 < baseStart_1194593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194607 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_1194607 : Nat := 118140960795 + 1194607 * 2 ^ 59
def prefixEnd_1194607 : Nat := 4983230072969 + 3 ^ 40 * 1194607 * 2
def baseEnd_1194607 : Nat := 272625592989205701474937

theorem tailTrace_1194607 : CollatzResearch.WordTrace tailWord_1194607 prefixEnd_1194607 272625592989205701474937 := by
  unfold tailWord_1194607
  simp only [CollatzResearch.WordTrace]
  refine ⟨43570896783150336477638075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29047264522100224318425383 43570896783150336477638075)
  ·
    refine ⟨65356345174725504716457113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43570896783150336477638075 65356345174725504716457113)
    ·
      refine ⟨49017258881044128537342835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65356345174725504716457113 49017258881044128537342835)
      ·
        refine ⟨73525888321566192806014253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49017258881044128537342835 73525888321566192806014253)
        ·
          refine ⟨27572208120587322302255345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73525888321566192806014253 27572208120587322302255345)
          ·
            refine ⟨20679156090440491726691509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27572208120587322302255345 20679156090440491726691509)
            ·
              refine ⟨1938670883478796099377329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20679156090440491726691509 1938670883478796099377329)
              ·
                refine ⟨1454003162609097074532997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1938670883478796099377329 1454003162609097074532997)
                ·
                  refine ⟨272625592989205701474937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454003162609097074532997 272625592989205701474937)
                  ·
                    rfl

theorem cell21_1194607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_1194607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194607 prefixEnd_1194607 := by exact prefixLift 1194607
  have htrace : WordTrace (prefixWord ++ tailWord_1194607) baseStart_1194607 baseEnd_1194607 := by
    simpa [prefixWord, tailWord_1194607, baseEnd_1194607] using wordTrace_append hprefix tailTrace_1194607
  have hstable : (prefixWord ++ tailWord_1194607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194607).length < 2 ^ (prefixWord ++ tailWord_1194607).sum := by decide
  have hdescent : baseEnd_1194607 < baseStart_1194607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194624 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_1194624 : Nat := 118140960795 + 1194624 * 2 ^ 59
def prefixEnd_1194624 : Nat := 4983230072969 + 3 ^ 40 * 1194624 * 2
def baseEnd_1194624 : Nat := 272629472620817449691569

theorem tailTrace_1194624 : CollatzResearch.WordTrace tailWord_1194624 prefixEnd_1194624 272629472620817449691569 := by
  unfold tailWord_1194624
  simp only [CollatzResearch.WordTrace]
  refine ⟨21785758412044374190503463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29047677882725832254004617 21785758412044374190503463)
  ·
    refine ⟨32678637618066561285755195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21785758412044374190503463 32678637618066561285755195)
    ·
      refine ⟨49017956427099841928632793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32678637618066561285755195 49017956427099841928632793)
      ·
        refine ⟨36763467320324881446474595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49017956427099841928632793 36763467320324881446474595)
        ·
          refine ⟨55145200980487322169711893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36763467320324881446474595 55145200980487322169711893)
          ·
            refine ⟨2584931295960343226705245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55145200980487322169711893 2584931295960343226705245)
            ·
              refine ⟨969349235985128710014467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2584931295960343226705245 969349235985128710014467)
              ·
                refine ⟨1454023853977693065021701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969349235985128710014467 1454023853977693065021701)
                ·
                  refine ⟨272629472620817449691569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454023853977693065021701 272629472620817449691569)
                  ·
                    rfl

theorem cell21_1194624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_1194624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194624 prefixEnd_1194624 := by exact prefixLift 1194624
  have htrace : WordTrace (prefixWord ++ tailWord_1194624) baseStart_1194624 baseEnd_1194624 := by
    simpa [prefixWord, tailWord_1194624, baseEnd_1194624] using wordTrace_append hprefix tailTrace_1194624
  have hstable : (prefixWord ++ tailWord_1194624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194624).length < 2 ^ (prefixWord ++ tailWord_1194624).sum := by decide
  have hdescent : baseEnd_1194624 < baseStart_1194624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194635 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_1194635 : Nat := 118140960795 + 1194635 * 2 ^ 59
def prefixEnd_1194635 : Nat := 4983230072969 + 3 ^ 40 * 1194635 * 2
def baseEnd_1194635 : Nat := 272631982970683875008213

theorem tailTrace_1194635 : CollatzResearch.WordTrace tailWord_1194635 prefixEnd_1194635 272631982970683875008213 := by
  unfold tailWord_1194635
  simp only [CollatzResearch.WordTrace]
  refine ⟨43571918027048897259657359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29047945351365931506438239 43571918027048897259657359)
  ·
    refine ⟨65357877040573345889486039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43571918027048897259657359 65357877040573345889486039)
    ·
      refine ⟨98036815560860018834229059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65357877040573345889486039 98036815560860018834229059)
      ·
        refine ⟨147055223341290028251343589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98036815560860018834229059 147055223341290028251343589)
        ·
          refine ⟨27572854376491880297126923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147055223341290028251343589 27572854376491880297126923)
          ·
            refine ⟨41359281564737820445690385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572854376491880297126923 41359281564737820445690385)
            ·
              refine ⟨31019461173553365334267789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41359281564737820445690385 31019461173553365334267789)
              ·
                refine ⟨11632297940082512000350421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31019461173553365334267789 11632297940082512000350421)
                ·
                  refine ⟨272631982970683875008213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11632297940082512000350421 272631982970683875008213)
                  ·
                    rfl

theorem cell21_1194635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_1194635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194635 prefixEnd_1194635 := by exact prefixLift 1194635
  have htrace : WordTrace (prefixWord ++ tailWord_1194635) baseStart_1194635 baseEnd_1194635 := by
    simpa [prefixWord, tailWord_1194635, baseEnd_1194635] using wordTrace_append hprefix tailTrace_1194635
  have hstable : (prefixWord ++ tailWord_1194635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194635).length < 2 ^ (prefixWord ++ tailWord_1194635).sum := by decide
  have hdescent : baseEnd_1194635 < baseStart_1194635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194669 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1194669 : Nat := 118140960795 + 1194669 * 2 ^ 59
def prefixEnd_1194669 : Nat := 4983230072969 + 3 ^ 40 * 1194669 * 2
def baseEnd_1194669 : Nat := 272639742233907371441477

theorem tailTrace_1194669 : CollatzResearch.WordTrace tailWord_1194669 prefixEnd_1194669 272639742233907371441477 := by
  unfold tailWord_1194669
  simp only [CollatzResearch.WordTrace]
  refine ⟨43573158108925721066395061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29048772072617147377596707 43573158108925721066395061)
  ·
    refine ⟨4084983572711786349974537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43573158108925721066395061 4084983572711786349974537)
    ·
      refine ⟨3063737679533839762480903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4084983572711786349974537 3063737679533839762480903)
      ·
        refine ⟨4595606519300759643721355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063737679533839762480903 4595606519300759643721355)
        ·
          refine ⟨6893409778951139465582033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595606519300759643721355 6893409778951139465582033)
          ·
            refine ⟨5170057334213354599186525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6893409778951139465582033 5170057334213354599186525)
            ·
              refine ⟨1938771500330007974694947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5170057334213354599186525 1938771500330007974694947)
              ·
                refine ⟨2908157250495011962042421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1938771500330007974694947 2908157250495011962042421)
                ·
                  refine ⟨272639742233907371441477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908157250495011962042421 272639742233907371441477)
                  ·
                    rfl

theorem cell21_1194669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1194669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194669 prefixEnd_1194669 := by exact prefixLift 1194669
  have htrace : WordTrace (prefixWord ++ tailWord_1194669) baseStart_1194669 baseEnd_1194669 := by
    simpa [prefixWord, tailWord_1194669, baseEnd_1194669] using wordTrace_append hprefix tailTrace_1194669
  have hstable : (prefixWord ++ tailWord_1194669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194669).length < 2 ^ (prefixWord ++ tailWord_1194669).sum := by decide
  have hdescent : baseEnd_1194669 < baseStart_1194669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194832 : List Nat := [2, 1, 1, 1, 1, 4, 11]
def baseStart_1194832 : Nat := 118140960795 + 1194832 * 2 ^ 59
def prefixEnd_1194832 : Nat := 4983230072969 + 3 ^ 40 * 1194832 * 2
def baseEnd_1194832 : Nat := 30297437894961701136053

theorem tailTrace_1194832 : CollatzResearch.WordTrace tailWord_1194832 prefixEnd_1194832 30297437894961701136053 := by
  unfold tailWord_1194832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789551603667599952289375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29052735471556799936385833 21789551603667599952289375)
  ·
    refine ⟨32684327405501399928434063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21789551603667599952289375 32684327405501399928434063)
    ·
      refine ⟨49026491108252099892651095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32684327405501399928434063 49026491108252099892651095)
      ·
        refine ⟨73539736662378149838976643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49026491108252099892651095 73539736662378149838976643)
        ·
          refine ⟨110309604993567224758464965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73539736662378149838976643 110309604993567224758464965)
          ·
            refine ⟨20683050936293854642212181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110309604993567224758464965 20683050936293854642212181)
            ·
              refine ⟨30297437894961701136053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20683050936293854642212181 30297437894961701136053)
              ·
                rfl

theorem cell21_1194832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 11].length) (baseStart_1194832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194832 prefixEnd_1194832 := by exact prefixLift 1194832
  have htrace : WordTrace (prefixWord ++ tailWord_1194832) baseStart_1194832 baseEnd_1194832 := by
    simpa [prefixWord, tailWord_1194832, baseEnd_1194832] using wordTrace_append hprefix tailTrace_1194832
  have hstable : (prefixWord ++ tailWord_1194832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194832).length < 2 ^ (prefixWord ++ tailWord_1194832).sum := by decide
  have hdescent : baseEnd_1194832 < baseStart_1194832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194852 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_1194852 : Nat := 118140960795 + 1194852 * 2 ^ 59
def prefixEnd_1194852 : Nat := 4983230072969 + 3 ^ 40 * 1194852 * 2
def baseEnd_1194852 : Nat := 272681505327139719891103

theorem tailTrace_1194852 : CollatzResearch.WordTrace tailWord_1194852 prefixEnd_1194852 272681505327139719891103 := by
  unfold tailWord_1194852
  simp only [CollatzResearch.WordTrace]
  refine ⟨21789916333631371660153405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29053221778175162213537873 21789916333631371660153405)
  ·
    refine ⟨8171218625111764372557527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21789916333631371660153405 8171218625111764372557527)
    ·
      refine ⟨12256827937667646558836291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8171218625111764372557527 12256827937667646558836291)
      ·
        refine ⟨18385241906501469838254437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12256827937667646558836291 18385241906501469838254437)
        ·
          refine ⟨3447232857469025594672707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18385241906501469838254437 3447232857469025594672707)
          ·
            refine ⟨5170849286203538392009061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447232857469025594672707 5170849286203538392009061)
            ·
              refine ⟨969534241163163448501699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5170849286203538392009061 969534241163163448501699)
              ·
                refine ⟨1454301361744745172752549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969534241163163448501699 1454301361744745172752549)
                ·
                  refine ⟨272681505327139719891103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454301361744745172752549 272681505327139719891103)
                  ·
                    rfl

theorem cell21_1194852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_1194852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194852 prefixEnd_1194852 := by exact prefixLift 1194852
  have htrace : WordTrace (prefixWord ++ tailWord_1194852) baseStart_1194852 baseEnd_1194852 := by
    simpa [prefixWord, tailWord_1194852, baseEnd_1194852] using wordTrace_append hprefix tailTrace_1194852
  have hstable : (prefixWord ++ tailWord_1194852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194852).length < 2 ^ (prefixWord ++ tailWord_1194852).sum := by decide
  have hdescent : baseEnd_1194852 < baseStart_1194852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194863 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 5]
def baseStart_1194863 : Nat := 118140960795 + 1194863 * 2 ^ 59
def prefixEnd_1194863 : Nat := 4983230072969 + 3 ^ 40 * 1194863 * 2
def baseEnd_1194863 : Nat := 272684015677006145207747

theorem tailTrace_1194863 : CollatzResearch.WordTrace tailWord_1194863 prefixEnd_1194863 272684015677006145207747 := by
  unfold tailWord_1194863
  simp only [CollatzResearch.WordTrace]
  refine ⟨43580233870222892198957243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29053489246815261465971495 43580233870222892198957243)
  ·
    refine ⟨65370350805334338298435865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43580233870222892198957243 65370350805334338298435865)
    ·
      refine ⟨49027763104000753723826899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65370350805334338298435865 49027763104000753723826899)
      ·
        refine ⟨73541644656001130585740349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49027763104000753723826899 73541644656001130585740349)
        ·
          refine ⟨27578116746000423969652631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73541644656001130585740349 27578116746000423969652631)
          ·
            refine ⟨41367175119000635954478947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27578116746000423969652631 41367175119000635954478947)
            ·
              refine ⟨62050762678500953931718421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41367175119000635954478947 62050762678500953931718421)
              ·
                refine ⟨2908629500554732215549301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62050762678500953931718421 2908629500554732215549301)
                ·
                  refine ⟨272684015677006145207747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908629500554732215549301 272684015677006145207747)
                  ·
                    rfl

theorem cell21_1194863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 5].length) (baseStart_1194863 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194863 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194863 prefixEnd_1194863 := by exact prefixLift 1194863
  have htrace : WordTrace (prefixWord ++ tailWord_1194863) baseStart_1194863 baseEnd_1194863 := by
    simpa [prefixWord, tailWord_1194863, baseEnd_1194863] using wordTrace_append hprefix tailTrace_1194863
  have hstable : (prefixWord ++ tailWord_1194863).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194863).length < 2 ^ (prefixWord ++ tailWord_1194863).sum := by decide
  have hdescent : baseEnd_1194863 < baseStart_1194863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194911 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 4]
def baseStart_1194911 : Nat := 118140960795 + 1194911 * 2 ^ 59
def prefixEnd_1194911 : Nat := 4983230072969 + 3 ^ 40 * 1194911 * 2
def baseEnd_1194911 : Nat := 272694969930968728407649

theorem tailTrace_1194911 : CollatzResearch.WordTrace tailWord_1194911 prefixEnd_1194911 272694969930968728407649 := by
  unfold tailWord_1194911
  simp only [CollatzResearch.WordTrace]
  refine ⟨43581984574048996396704587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29054656382699330931136391 43581984574048996396704587)
  ·
    refine ⟨65372976861073494595056881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43581984574048996396704587 65372976861073494595056881)
    ·
      refine ⟨49029732645805120946292661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65372976861073494595056881 49029732645805120946292661)
      ·
        refine ⟨4596537435544230088714937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49029732645805120946292661 4596537435544230088714937)
        ·
          refine ⟨3447403076658172566536203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4596537435544230088714937 3447403076658172566536203)
          ·
            refine ⟨5171104614987258849804305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3447403076658172566536203 5171104614987258849804305)
            ·
              refine ⟨3878328461240444137353229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5171104614987258849804305 3878328461240444137353229)
              ·
                refine ⟨1454373172965166551507461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3878328461240444137353229 1454373172965166551507461)
                ·
                  refine ⟨272694969930968728407649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454373172965166551507461 272694969930968728407649)
                  ·
                    rfl

theorem cell21_1194911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 4].length) (baseStart_1194911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194911 prefixEnd_1194911 := by exact prefixLift 1194911
  have htrace : WordTrace (prefixWord ++ tailWord_1194911) baseStart_1194911 baseEnd_1194911 := by
    simpa [prefixWord, tailWord_1194911, baseEnd_1194911] using wordTrace_append hprefix tailTrace_1194911
  have hstable : (prefixWord ++ tailWord_1194911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194911).length < 2 ^ (prefixWord ++ tailWord_1194911).sum := by decide
  have hdescent : baseEnd_1194911 < baseStart_1194911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1194956 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_1194956 : Nat := 118140960795 + 1194956 * 2 ^ 59
def prefixEnd_1194956 : Nat := 4983230072969 + 3 ^ 40 * 1194956 * 2
def baseEnd_1194956 : Nat := 272705239544058650157557

theorem tailTrace_1194956 : CollatzResearch.WordTrace tailWord_1194956 prefixEnd_1194956 272705239544058650157557 := by
  unfold tailWord_1194956
  simp only [CollatzResearch.WordTrace]
  refine ⟨21791812929442984541046361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29055750572590646054728481 21791812929442984541046361)
  ·
    refine ⟨16343859697082238405784771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21791812929442984541046361 16343859697082238405784771)
    ·
      refine ⟨24515789545623357608677157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16343859697082238405784771 24515789545623357608677157)
      ·
        refine ⟨4596710539804379551626967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24515789545623357608677157 4596710539804379551626967)
        ·
          refine ⟨6895065809706569327440451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4596710539804379551626967 6895065809706569327440451)
          ·
            refine ⟨10342598714559853991160677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6895065809706569327440451 10342598714559853991160677)
            ·
              refine ⟨1939237258979972623342627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10342598714559853991160677 1939237258979972623342627)
              ·
                refine ⟨2908855888469958935013941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939237258979972623342627 2908855888469958935013941)
                ·
                  refine ⟨272705239544058650157557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908855888469958935013941 272705239544058650157557)
                  ·
                    rfl

theorem cell21_1194956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_1194956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1194956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1194956 prefixEnd_1194956 := by exact prefixLift 1194956
  have htrace : WordTrace (prefixWord ++ tailWord_1194956) baseStart_1194956 baseEnd_1194956 := by
    simpa [prefixWord, tailWord_1194956, baseEnd_1194956] using wordTrace_append hprefix tailTrace_1194956
  have hstable : (prefixWord ++ tailWord_1194956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1194956).length < 2 ^ (prefixWord ++ tailWord_1194956).sum := by decide
  have hdescent : baseEnd_1194956 < baseStart_1194956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1194956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195122 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_1195122 : Nat := 118140960795 + 1195122 * 2 ^ 59
def prefixEnd_1195122 : Nat := 4983230072969 + 3 ^ 40 * 1195122 * 2
def baseEnd_1195122 : Nat := 272743123005679250390551

theorem tailTrace_1195122 : CollatzResearch.WordTrace tailWord_1195122 prefixEnd_1195122 272743123005679250390551 := by
  unfold tailWord_1195122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897420094071144858158905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29059786917523052955090413 10897420094071144858158905)
  ·
    refine ⟨8173065070553358643619179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10897420094071144858158905 8173065070553358643619179)
    ·
      refine ⟨12259597605830037965428769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8173065070553358643619179 12259597605830037965428769)
      ·
        refine ⟨9194698204372528474071577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12259597605830037965428769 9194698204372528474071577)
        ·
          refine ⟨6896023653279396355553683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9194698204372528474071577 6896023653279396355553683)
          ·
            refine ⟨10344035479919094533330525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6896023653279396355553683 10344035479919094533330525)
            ·
              refine ⟨3879013304969660449998947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10344035479919094533330525 3879013304969660449998947)
              ·
                refine ⟨5818519957454490674998421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3879013304969660449998947 5818519957454490674998421)
                ·
                  refine ⟨272743123005679250390551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5818519957454490674998421 272743123005679250390551)
                  ·
                    rfl

theorem cell21_1195122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_1195122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195122 prefixEnd_1195122 := by exact prefixLift 1195122
  have htrace : WordTrace (prefixWord ++ tailWord_1195122) baseStart_1195122 baseEnd_1195122 := by
    simpa [prefixWord, tailWord_1195122, baseEnd_1195122] using wordTrace_append hprefix tailTrace_1195122
  have hstable : (prefixWord ++ tailWord_1195122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195122).length < 2 ^ (prefixWord ++ tailWord_1195122).sum := by decide
  have hdescent : baseEnd_1195122 < baseStart_1195122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195139 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 4]
def baseStart_1195139 : Nat := 118140960795 + 1195139 * 2 ^ 59
def prefixEnd_1195139 : Nat := 4983230072969 + 3 ^ 40 * 1195139 * 2
def baseEnd_1195139 : Nat := 272747002637290998607183

theorem tailTrace_1195139 : CollatzResearch.WordTrace tailWord_1195139 prefixEnd_1195139 272747002637290998607183 := by
  unfold tailWord_1195139
  simp only [CollatzResearch.WordTrace]
  refine ⟨43590300417222991336004471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29060200278148660890669647 43590300417222991336004471)
  ·
    refine ⟨65385450625834487004006707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43590300417222991336004471 65385450625834487004006707)
    ·
      refine ⟨98078175938751730506010061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65385450625834487004006707 98078175938751730506010061)
      ·
        refine ⟨36779315977031898939753773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98078175938751730506010061 36779315977031898939753773)
        ·
          refine ⟨13792243491386962102407665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36779315977031898939753773 13792243491386962102407665)
          ·
            refine ⟨10344182618540221576805749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13792243491386962102407665 10344182618540221576805749)
            ·
              refine ⟨969767120488145772825539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10344182618540221576805749 969767120488145772825539)
              ·
                refine ⟨1454650680732218659238309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 969767120488145772825539 1454650680732218659238309)
                ·
                  refine ⟨272747002637290998607183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454650680732218659238309 272747002637290998607183)
                  ·
                    rfl

theorem cell21_1195139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 4].length) (baseStart_1195139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195139 prefixEnd_1195139 := by exact prefixLift 1195139
  have htrace : WordTrace (prefixWord ++ tailWord_1195139) baseStart_1195139 baseEnd_1195139 := by
    simpa [prefixWord, tailWord_1195139, baseEnd_1195139] using wordTrace_append hprefix tailTrace_1195139
  have hstable : (prefixWord ++ tailWord_1195139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195139).length < 2 ^ (prefixWord ++ tailWord_1195139).sum := by decide
  have hdescent : baseEnd_1195139 < baseStart_1195139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195170 : List Nat := [3, 3, 1, 3, 2, 2, 7]
def baseStart_1195170 : Nat := 118140960795 + 1195170 * 2 ^ 59
def prefixEnd_1195170 : Nat := 4983230072969 + 3 ^ 40 * 1195170 * 2
def baseEnd_1195170 : Nat := 30306008584404648176717

theorem tailTrace_1195170 : CollatzResearch.WordTrace tailWord_1195170 prefixEnd_1195170 30306008584404648176717 := by
  unfold tailWord_1195170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10897857770027670907595741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29060954053407122420255309 10897857770027670907595741)
  ·
    refine ⟨4086696663760376590348403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10897857770027670907595741 4086696663760376590348403)
    ·
      refine ⟨6130044995640564885522605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4086696663760376590348403 6130044995640564885522605)
      ·
        refine ⟨2298766873365211832070977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6130044995640564885522605 2298766873365211832070977)
        ·
          refine ⟨1724075155023908874053233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298766873365211832070977 1724075155023908874053233)
          ·
            refine ⟨1293056366267931655539925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1724075155023908874053233 1293056366267931655539925)
            ·
              refine ⟨30306008584404648176717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1293056366267931655539925 30306008584404648176717)
              ·
                rfl

theorem cell21_1195170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 7].length) (baseStart_1195170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195170 prefixEnd_1195170 := by exact prefixLift 1195170
  have htrace : WordTrace (prefixWord ++ tailWord_1195170) baseStart_1195170 baseEnd_1195170 := by
    simpa [prefixWord, tailWord_1195170, baseEnd_1195170] using wordTrace_append hprefix tailTrace_1195170
  have hstable : (prefixWord ++ tailWord_1195170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195170).length < 2 ^ (prefixWord ++ tailWord_1195170).sum := by decide
  have hdescent : baseEnd_1195170 < baseStart_1195170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195229 : List Nat := [1, 4, 3, 2, 2, 9]
def baseStart_1195229 : Nat := 118140960795 + 1195229 * 2 ^ 59
def prefixEnd_1195229 : Nat := 4983230072969 + 3 ^ 40 * 1195229 * 2
def baseEnd_1195229 : Nat := 10102501550498920078037

theorem tailTrace_1195229 : CollatzResearch.WordTrace tailWord_1195229 prefixEnd_1195229 10102501550498920078037 := by
  unfold tailWord_1195229
  simp only [CollatzResearch.WordTrace]
  refine ⟨43593582986896936706780741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29062388657931291137853827 43593582986896936706780741)
  ·
    refine ⟨8173796810043175632521389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43593582986896936706780741 8173796810043175632521389)
    ·
      refine ⟨3065173803766190862195521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8173796810043175632521389 3065173803766190862195521)
      ·
        refine ⟨2298880352824643146646641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3065173803766190862195521 2298880352824643146646641)
        ·
          refine ⟨1724160264618482359984981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298880352824643146646641 1724160264618482359984981)
          ·
            refine ⟨10102501550498920078037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1724160264618482359984981 10102501550498920078037)
            ·
              rfl

theorem cell21_1195229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 9].length) (baseStart_1195229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195229 prefixEnd_1195229 := by exact prefixLift 1195229
  have htrace : WordTrace (prefixWord ++ tailWord_1195229) baseStart_1195229 baseEnd_1195229 := by
    simpa [prefixWord, tailWord_1195229, baseEnd_1195229] using wordTrace_append hprefix tailTrace_1195229
  have hstable : (prefixWord ++ tailWord_1195229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195229).length < 2 ^ (prefixWord ++ tailWord_1195229).sum := by decide
  have hdescent : baseEnd_1195229 < baseStart_1195229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195260 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_1195260 : Nat := 118140960795 + 1195260 * 2 ^ 59
def prefixEnd_1195260 : Nat := 4983230072969 + 3 ^ 40 * 1195260 * 2
def baseEnd_1195260 : Nat := 272774616485821677090269

theorem tailTrace_1195260 : CollatzResearch.WordTrace tailWord_1195260 prefixEnd_1195260 272774616485821677090269 := by
  unfold tailWord_1195260
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797356824892314500579617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29063142433189752667439489 21797356824892314500579617)
  ·
    refine ⟨16348017618669235875434713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21797356824892314500579617 16348017618669235875434713)
    ·
      refine ⟨12261013214001926906576035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16348017618669235875434713 12261013214001926906576035)
      ·
        refine ⟨18391519821002890359864053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12261013214001926906576035 18391519821002890359864053)
        ·
          refine ⟨1724204983219020971237255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18391519821002890359864053 1724204983219020971237255)
          ·
            refine ⟨2586307474828531456855883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724204983219020971237255 2586307474828531456855883)
            ·
              refine ⟨3879461212242797185283825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586307474828531456855883 3879461212242797185283825)
              ·
                refine ⟨2909595909182097888962869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3879461212242797185283825 2909595909182097888962869)
                ·
                  refine ⟨272774616485821677090269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909595909182097888962869 272774616485821677090269)
                  ·
                    rfl

theorem cell21_1195260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_1195260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195260 prefixEnd_1195260 := by exact prefixLift 1195260
  have htrace : WordTrace (prefixWord ++ tailWord_1195260) baseStart_1195260 baseEnd_1195260 := by
    simpa [prefixWord, tailWord_1195260, baseEnd_1195260] using wordTrace_append hprefix tailTrace_1195260
  have hstable : (prefixWord ++ tailWord_1195260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195260).length < 2 ^ (prefixWord ++ tailWord_1195260).sum := by decide
  have hdescent : baseEnd_1195260 < baseStart_1195260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195288 : List Nat := [2, 1, 2, 3, 1, 4, 8]
def baseStart_1195288 : Nat := 118140960795 + 1195288 * 2 ^ 59
def prefixEnd_1195288 : Nat := 4983230072969 + 3 ^ 40 * 1195288 * 2
def baseEnd_1195288 : Nat := 30309000718588872291505

theorem tailTrace_1195288 : CollatzResearch.WordTrace tailWord_1195288 prefixEnd_1195288 30309000718588872291505 := by
  unfold tailWord_1195288
  simp only [CollatzResearch.WordTrace]
  refine ⟨21797867446841594891589259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29063823262455459855452345 21797867446841594891589259)
  ·
    refine ⟨32696801170262392337383889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21797867446841594891589259 32696801170262392337383889)
    ·
      refine ⟨24522600877696794253037917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32696801170262392337383889 24522600877696794253037917)
      ·
        refine ⟨9195975329136297844889219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24522600877696794253037917 9195975329136297844889219)
        ·
          refine ⟨13793962993704446767333829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9195975329136297844889219 13793962993704446767333829)
          ·
            refine ⟨2586368061319583768875093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13793962993704446767333829 2586368061319583768875093)
            ·
              refine ⟨30309000718588872291505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2586368061319583768875093 30309000718588872291505)
              ·
                rfl

theorem cell21_1195288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 8].length) (baseStart_1195288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195288 prefixEnd_1195288 := by exact prefixLift 1195288
  have htrace : WordTrace (prefixWord ++ tailWord_1195288) baseStart_1195288 baseEnd_1195288 := by
    simpa [prefixWord, tailWord_1195288, baseEnd_1195288] using wordTrace_append hprefix tailTrace_1195288
  have hstable : (prefixWord ++ tailWord_1195288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195288).length < 2 ^ (prefixWord ++ tailWord_1195288).sum := by decide
  have hdescent : baseEnd_1195288 < baseStart_1195288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195294 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1195294 : Nat := 118140960795 + 1195294 * 2 ^ 59
def prefixEnd_1195294 : Nat := 4983230072969 + 3 ^ 40 * 1195294 * 2
def baseEnd_1195294 : Nat := 272782375749045173523533

theorem tailTrace_1195294 : CollatzResearch.WordTrace tailWord_1195294 prefixEnd_1195294 272782375749045173523533 := by
  unfold tailWord_1195294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5449494216457681600987117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29063969154440968538597957 5449494216457681600987117)
  ·
    refine ⟨2043560331171630600370169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5449494216457681600987117 2043560331171630600370169)
    ·
      refine ⟨1532670248378722950277627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2043560331171630600370169 1532670248378722950277627)
      ·
        refine ⟨2299005372568084425416441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532670248378722950277627 2299005372568084425416441)
        ·
          refine ⟨1724254029426063319062331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299005372568084425416441 1724254029426063319062331)
          ·
            refine ⟨2586381044139094978593497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724254029426063319062331 2586381044139094978593497)
            ·
              refine ⟨1939785783104321233945123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2586381044139094978593497 1939785783104321233945123)
              ·
                refine ⟨2909678674656481850917685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1939785783104321233945123 2909678674656481850917685)
                ·
                  refine ⟨272782375749045173523533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2909678674656481850917685 272782375749045173523533)
                  ·
                    rfl

theorem cell21_1195294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1195294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195294 prefixEnd_1195294 := by exact prefixLift 1195294
  have htrace : WordTrace (prefixWord ++ tailWord_1195294) baseStart_1195294 baseEnd_1195294 := by
    simpa [prefixWord, tailWord_1195294, baseEnd_1195294] using wordTrace_append hprefix tailTrace_1195294
  have hstable : (prefixWord ++ tailWord_1195294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195294).length < 2 ^ (prefixWord ++ tailWord_1195294).sum := by decide
  have hdescent : baseEnd_1195294 < baseStart_1195294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195364 : List Nat := [2, 3, 1, 1, 3, 2, 1, 8]
def baseStart_1195364 : Nat := 118140960795 + 1195364 * 2 ^ 59
def prefixEnd_1195364 : Nat := 4983230072969 + 3 ^ 40 * 1195364 * 2
def baseEnd_1195364 : Nat := 90932783567580202452241

theorem tailTrace_1195364 : CollatzResearch.WordTrace tailWord_1195364 prefixEnd_1195364 90932783567580202452241 := by
  unfold tailWord_1195364
  simp only [CollatzResearch.WordTrace]
  refine ⟨21799253420703927381472573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29065671227605236508630097 21799253420703927381472573)
  ·
    refine ⟨8174720032763972768052215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21799253420703927381472573 8174720032763972768052215)
    ·
      refine ⟨12262080049145959152078323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8174720032763972768052215 12262080049145959152078323)
      ·
        refine ⟨18393120073718938728117485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12262080049145959152078323 18393120073718938728117485)
        ·
          refine ⟨6897420027644602023044057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18393120073718938728117485 6897420027644602023044057)
          ·
            refine ⟨5173065020733451517283043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6897420027644602023044057 5173065020733451517283043)
            ·
              refine ⟨7759597531100177275924565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5173065020733451517283043 7759597531100177275924565)
              ·
                refine ⟨90932783567580202452241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7759597531100177275924565 90932783567580202452241)
                ·
                  rfl

theorem cell21_1195364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_1195364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195364 prefixEnd_1195364 := by exact prefixLift 1195364
  have htrace : WordTrace (prefixWord ++ tailWord_1195364) baseStart_1195364 baseEnd_1195364 := by
    simpa [prefixWord, tailWord_1195364, baseEnd_1195364] using wordTrace_append hprefix tailTrace_1195364
  have hstable : (prefixWord ++ tailWord_1195364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195364).length < 2 ^ (prefixWord ++ tailWord_1195364).sum := by decide
  have hdescent : baseEnd_1195364 < baseStart_1195364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195367 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 4]
def baseStart_1195367 : Nat := 118140960795 + 1195367 * 2 ^ 59
def prefixEnd_1195367 : Nat := 4983230072969 + 3 ^ 40 * 1195367 * 2
def baseEnd_1195367 : Nat := 272799035343613268806717

theorem tailTrace_1195367 : CollatzResearch.WordTrace tailWord_1195367 prefixEnd_1195367 272799035343613268806717 := by
  unfold tailWord_1195367
  simp only [CollatzResearch.WordTrace]
  refine ⟨43598616260396986275304355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29065744173597990850202903 43598616260396986275304355)
  ·
    refine ⟨65397924390595479412956533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43598616260396986275304355 65397924390595479412956533)
    ·
      refine ⟨6131055411618326194964675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65397924390595479412956533 6131055411618326194964675)
      ·
        refine ⟨9196583117427489292447013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6131055411618326194964675 9196583117427489292447013)
        ·
          refine ⟨1724359334517654242333815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9196583117427489292447013 1724359334517654242333815)
          ·
            refine ⟨2586539001776481363500723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724359334517654242333815 2586539001776481363500723)
            ·
              refine ⟨3879808502664722045251085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2586539001776481363500723 3879808502664722045251085)
              ·
                refine ⟨1454928188499270766969157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3879808502664722045251085 1454928188499270766969157)
                ·
                  refine ⟨272799035343613268806717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1454928188499270766969157 272799035343613268806717)
                  ·
                    rfl

theorem cell21_1195367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 4].length) (baseStart_1195367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195367 prefixEnd_1195367 := by exact prefixLift 1195367
  have htrace : WordTrace (prefixWord ++ tailWord_1195367) baseStart_1195367 baseEnd_1195367 := by
    simpa [prefixWord, tailWord_1195367, baseEnd_1195367] using wordTrace_append hprefix tailTrace_1195367
  have hstable : (prefixWord ++ tailWord_1195367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195367).length < 2 ^ (prefixWord ++ tailWord_1195367).sum := by decide
  have hdescent : baseEnd_1195367 < baseStart_1195367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195460 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 4]
def baseStart_1195460 : Nat := 118140960795 + 1195460 * 2 ^ 59
def prefixEnd_1195460 : Nat := 4983230072969 + 3 ^ 40 * 1195460 * 2
def baseEnd_1195460 : Nat := 272820259210665773756527

theorem tailTrace_1195460 : CollatzResearch.WordTrace tailWord_1195460 prefixEnd_1195460 272820259210665773756527 := by
  unfold tailWord_1195460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21801004124530031579219917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29068005499373375438959889 21801004124530031579219917)
  ·
    refine ⟨8175376546698761842207469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21801004124530031579219917 8175376546698761842207469)
    ·
      refine ⟨3065766205012035690827801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8175376546698761842207469 3065766205012035690827801)
      ·
        refine ⟨2299324653759026768120851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3065766205012035690827801 2299324653759026768120851)
        ·
          refine ⟨3448986980638540152181277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299324653759026768120851 3448986980638540152181277)
          ·
            refine ⟨1293370117739452557067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3448986980638540152181277 1293370117739452557067979)
            ·
              refine ⟨1940055176609178835601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293370117739452557067979 1940055176609178835601969)
              ·
                refine ⟨1455041382456884126701477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940055176609178835601969 1455041382456884126701477)
                ·
                  refine ⟨272820259210665773756527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455041382456884126701477 272820259210665773756527)
                  ·
                    rfl

theorem cell21_1195460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 4].length) (baseStart_1195460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195460 prefixEnd_1195460 := by exact prefixLift 1195460
  have htrace : WordTrace (prefixWord ++ tailWord_1195460) baseStart_1195460 baseEnd_1195460 := by
    simpa [prefixWord, tailWord_1195460, baseEnd_1195460] using wordTrace_append hprefix tailTrace_1195460
  have hstable : (prefixWord ++ tailWord_1195460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195460).length < 2 ^ (prefixWord ++ tailWord_1195460).sum := by decide
  have hdescent : baseEnd_1195460 < baseStart_1195460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195505 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 3]
def baseStart_1195505 : Nat := 118140960795 + 1195505 * 2 ^ 59
def prefixEnd_1195505 : Nat := 4983230072969 + 3 ^ 40 * 1195505 * 2
def baseEnd_1195505 : Nat := 272830528823755695506435

theorem tailTrace_1195505 : CollatzResearch.WordTrace tailWord_1195505 prefixEnd_1195505 272830528823755695506435 := by
  unfold tailWord_1195505
  simp only [CollatzResearch.WordTrace]
  refine ⟨43603649533897035843827969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29069099689264690562551979 43603649533897035843827969)
  ·
    refine ⟨32702737150422776882870977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43603649533897035843827969 32702737150422776882870977)
    ·
      refine ⟨24527052862817082662153233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32702737150422776882870977 24527052862817082662153233)
      ·
        refine ⟨18395289647112811996614925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24527052862817082662153233 18395289647112811996614925)
        ·
          refine ⟨6898233617667304498730597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18395289647112811996614925 6898233617667304498730597)
          ·
            refine ⟨1293418803312619593511987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6898233617667304498730597 1293418803312619593511987)
            ·
              refine ⟨1940128204968929390267981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1293418803312619593511987 1940128204968929390267981)
              ·
                refine ⟨727548076863348521350493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1940128204968929390267981 727548076863348521350493)
                ·
                  refine ⟨272830528823755695506435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727548076863348521350493 272830528823755695506435)
                  ·
                    rfl

theorem cell21_1195505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_1195505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195505 prefixEnd_1195505 := by exact prefixLift 1195505
  have htrace : WordTrace (prefixWord ++ tailWord_1195505) baseStart_1195505 baseEnd_1195505 := by
    simpa [prefixWord, tailWord_1195505, baseEnd_1195505] using wordTrace_append hprefix tailTrace_1195505
  have hstable : (prefixWord ++ tailWord_1195505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195505).length < 2 ^ (prefixWord ++ tailWord_1195505).sum := by decide
  have hdescent : baseEnd_1195505 < baseStart_1195505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195575 : List Nat := [1, 1, 3, 1, 2, 13]
def baseStart_1195575 : Nat := 118140960795 + 1195575 * 2 ^ 59
def prefixEnd_1195575 : Nat := 4983230072969 + 3 ^ 40 * 1195575 * 2
def baseEnd_1195575 : Nat := 10105426065831523308875

theorem tailTrace_1195575 : CollatzResearch.WordTrace tailWord_1195575 prefixEnd_1195575 10105426065831523308875 := by
  unfold tailWord_1195575
  simp only [CollatzResearch.WordTrace]
  refine ⟨43606202643643437798876179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29070801762428958532584119 43606202643643437798876179)
  ·
    refine ⟨65409303965465156698314269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43606202643643437798876179 65409303965465156698314269)
    ·
      refine ⟨24528488987049433761867851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65409303965465156698314269 24528488987049433761867851)
      ·
        refine ⟨36792733480574150642801777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24528488987049433761867851 36792733480574150642801777)
        ·
          refine ⟨27594550110430612982101333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36792733480574150642801777 27594550110430612982101333)
          ·
            refine ⟨10105426065831523308875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 27594550110430612982101333 10105426065831523308875)
            ·
              rfl

theorem cell21_1195575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 13].length) (baseStart_1195575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195575 prefixEnd_1195575 := by exact prefixLift 1195575
  have htrace : WordTrace (prefixWord ++ tailWord_1195575) baseStart_1195575 baseEnd_1195575 := by
    simpa [prefixWord, tailWord_1195575, baseEnd_1195575] using wordTrace_append hprefix tailTrace_1195575
  have hstable : (prefixWord ++ tailWord_1195575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195575).length < 2 ^ (prefixWord ++ tailWord_1195575).sum := by decide
  have hdescent : baseEnd_1195575 < baseStart_1195575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195578 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_1195578 : Nat := 118140960795 + 1195578 * 2 ^ 59
def prefixEnd_1195578 : Nat := 4983230072969 + 3 ^ 40 * 1195578 * 2
def baseEnd_1195578 : Nat := 272847188418323790789619

theorem tailTrace_1195578 : CollatzResearch.WordTrace tailWord_1195578 prefixEnd_1195578 272847188418323790789619 := by
  unfold tailWord_1195578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10901578015658142327808847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29070874708421712874156925 10901578015658142327808847)
  ·
    refine ⟨16352367023487213491713271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10901578015658142327808847 16352367023487213491713271)
    ·
      refine ⟨24528550535230820237569907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16352367023487213491713271 24528550535230820237569907)
      ·
        refine ⟨36792825802846230356354861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24528550535230820237569907 36792825802846230356354861)
        ·
          refine ⟨13797309676067336383633073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36792825802846230356354861 13797309676067336383633073)
          ·
            refine ⟨10347982257050502287724805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13797309676067336383633073 10347982257050502287724805)
            ·
              refine ⟨1940246673196969178948401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10347982257050502287724805 1940246673196969178948401)
              ·
                refine ⟨1455185004897726884211301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940246673196969178948401 1455185004897726884211301)
                ·
                  refine ⟨272847188418323790789619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455185004897726884211301 272847188418323790789619)
                  ·
                    rfl

theorem cell21_1195578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_1195578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195578 prefixEnd_1195578 := by exact prefixLift 1195578
  have htrace : WordTrace (prefixWord ++ tailWord_1195578) baseStart_1195578 baseEnd_1195578 := by
    simpa [prefixWord, tailWord_1195578, baseEnd_1195578] using wordTrace_append hprefix tailTrace_1195578
  have hstable : (prefixWord ++ tailWord_1195578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195578).length < 2 ^ (prefixWord ++ tailWord_1195578).sum := by decide
  have hdescent : baseEnd_1195578 < baseStart_1195578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195581 : List Nat := [1, 4, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1195581 : Nat := 118140960795 + 1195581 * 2 ^ 59
def prefixEnd_1195581 : Nat := 4983230072969 + 3 ^ 40 * 1195581 * 2
def baseEnd_1195581 : Nat := 272847873059196452239613

theorem tailTrace_1195581 : CollatzResearch.WordTrace tailWord_1195581 prefixEnd_1195581 272847873059196452239613 := by
  unfold tailWord_1195581
  simp only [CollatzResearch.WordTrace]
  refine ⟨43606421481621700823594597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29070947654414467215729731 43606421481621700823594597)
  ·
    refine ⟨8176204027804068904423987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43606421481621700823594597 8176204027804068904423987)
    ·
      refine ⟨12264306041706103356635981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8176204027804068904423987 12264306041706103356635981)
      ·
        refine ⟨4599114765639788758738493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12264306041706103356635981 4599114765639788758738493)
        ·
          refine ⟨1724668037114920784526935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4599114765639788758738493 1724668037114920784526935)
          ·
            refine ⟨2587002055672381176790403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724668037114920784526935 2587002055672381176790403)
            ·
              refine ⟨3880503083508571765185605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2587002055672381176790403 3880503083508571765185605)
              ·
                refine ⟨727594328157857205972301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3880503083508571765185605 727594328157857205972301)
                ·
                  refine ⟨272847873059196452239613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727594328157857205972301 272847873059196452239613)
                  ·
                    rfl

theorem cell21_1195581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1195581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195581 prefixEnd_1195581 := by exact prefixLift 1195581
  have htrace : WordTrace (prefixWord ++ tailWord_1195581) baseStart_1195581 baseEnd_1195581 := by
    simpa [prefixWord, tailWord_1195581, baseEnd_1195581] using wordTrace_append hprefix tailTrace_1195581
  have hstable : (prefixWord ++ tailWord_1195581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195581).length < 2 ^ (prefixWord ++ tailWord_1195581).sum := by decide
  have hdescent : baseEnd_1195581 < baseStart_1195581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195651 : List Nat := [1, 1, 1, 3, 3, 1, 1, 10]
def baseStart_1195651 : Nat := 118140960795 + 1195651 * 2 ^ 59
def prefixEnd_1195651 : Nat := 4983230072969 + 3 ^ 40 * 1195651 * 2
def baseEnd_1195651 : Nat := 90954616004297295357601

theorem tailTrace_1195651 : CollatzResearch.WordTrace tailWord_1195651 prefixEnd_1195651 90954616004297295357601 := by
  unfold tailWord_1195651
  simp only [CollatzResearch.WordTrace]
  refine ⟨43608974591368102778642807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29072649727578735185761871 43608974591368102778642807)
  ·
    refine ⟨65413461887052154167964211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43608974591368102778642807 65413461887052154167964211)
    ·
      refine ⟨98120192830578231251946317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65413461887052154167964211 98120192830578231251946317)
      ·
        refine ⟨36795072311466836719479869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98120192830578231251946317 36795072311466836719479869)
        ·
          refine ⟨13798152116800063769804951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36795072311466836719479869 13798152116800063769804951)
          ·
            refine ⟨20697228175200095654707427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13798152116800063769804951 20697228175200095654707427)
            ·
              refine ⟨31045842262800143482061141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20697228175200095654707427 31045842262800143482061141)
              ·
                refine ⟨90954616004297295357601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31045842262800143482061141 90954616004297295357601)
                ·
                  rfl

theorem cell21_1195651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_1195651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195651 prefixEnd_1195651 := by exact prefixLift 1195651
  have htrace : WordTrace (prefixWord ++ tailWord_1195651) baseStart_1195651 baseEnd_1195651 := by
    simpa [prefixWord, tailWord_1195651, baseEnd_1195651] using wordTrace_append hprefix tailTrace_1195651
  have hstable : (prefixWord ++ tailWord_1195651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195651).length < 2 ^ (prefixWord ++ tailWord_1195651).sum := by decide
  have hdescent : baseEnd_1195651 < baseStart_1195651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195702 : List Nat := [5, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1195702 : Nat := 118140960795 + 1195702 * 2 ^ 59
def prefixEnd_1195702 : Nat := 4983230072969 + 3 ^ 40 * 1195702 * 2
def baseEnd_1195702 : Nat := 90958495635909043574233

theorem tailTrace_1195702 : CollatzResearch.WordTrace tailWord_1195702 prefixEnd_1195702 90958495635909043574233 := by
  unfold tailWord_1195702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2725677169636458655546835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29073889809455558992499573 2725677169636458655546835)
  ·
    refine ⟨4088515754454687983320253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2725677169636458655546835 4088515754454687983320253)
    ·
      refine ⟨1533193407920507993745095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4088515754454687983320253 1533193407920507993745095)
      ·
        refine ⟨2299790111880761990617643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533193407920507993745095 2299790111880761990617643)
        ·
          refine ⟨3449685167821142985926465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299790111880761990617643 3449685167821142985926465)
          ·
            refine ⟨2587263875865857239444849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3449685167821142985926465 2587263875865857239444849)
            ·
              refine ⟨1940447906899392929583637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587263875865857239444849 1940447906899392929583637)
              ·
                refine ⟨90958495635909043574233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1940447906899392929583637 90958495635909043574233)
                ·
                  rfl

theorem cell21_1195702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1195702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195702 prefixEnd_1195702 := by exact prefixLift 1195702
  have htrace : WordTrace (prefixWord ++ tailWord_1195702) baseStart_1195702 baseEnd_1195702 := by
    simpa [prefixWord, tailWord_1195702, baseEnd_1195702] using wordTrace_append hprefix tailTrace_1195702
  have hstable : (prefixWord ++ tailWord_1195702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195702).length < 2 ^ (prefixWord ++ tailWord_1195702).sum := by decide
  have hdescent : baseEnd_1195702 < baseStart_1195702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195747 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 4]
def baseStart_1195747 : Nat := 118140960795 + 1195747 * 2 ^ 59
def prefixEnd_1195747 : Nat := 4983230072969 + 3 ^ 40 * 1195747 * 2
def baseEnd_1195747 : Nat := 272885756520817052472607

theorem tailTrace_1195747 : CollatzResearch.WordTrace tailWord_1195747 prefixEnd_1195747 272885756520817052472607 := by
  unfold tailWord_1195747
  simp only [CollatzResearch.WordTrace]
  refine ⟨43612475999020311174137495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29074983999346874116091663 43612475999020311174137495)
  ·
    refine ⟨65418713998530466761206243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43612475999020311174137495 65418713998530466761206243)
    ·
      refine ⟨98128070997795700141809365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65418713998530466761206243 98128070997795700141809365)
      ·
        refine ⟨2299876664010836722073657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 98128070997795700141809365 2299876664010836722073657)
        ·
          refine ⟨1724907498008127541555243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2299876664010836722073657 1724907498008127541555243)
          ·
            refine ⟨2587361247012191312332865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1724907498008127541555243 2587361247012191312332865)
            ·
              refine ⟨1940520935259143484249649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2587361247012191312332865 1940520935259143484249649)
              ·
                refine ⟨1455390701444357613187237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1940520935259143484249649 1455390701444357613187237)
                ·
                  refine ⟨272885756520817052472607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455390701444357613187237 272885756520817052472607)
                  ·
                    rfl

theorem cell21_1195747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 4].length) (baseStart_1195747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195747 prefixEnd_1195747 := by exact prefixLift 1195747
  have htrace : WordTrace (prefixWord ++ tailWord_1195747) baseStart_1195747 baseEnd_1195747 := by
    simpa [prefixWord, tailWord_1195747, baseEnd_1195747] using wordTrace_append hprefix tailTrace_1195747
  have hstable : (prefixWord ++ tailWord_1195747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195747).length < 2 ^ (prefixWord ++ tailWord_1195747).sum := by decide
  have hdescent : baseEnd_1195747 < baseStart_1195747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195764 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1195764 : Nat := 118140960795 + 1195764 * 2 ^ 59
def prefixEnd_1195764 : Nat := 4983230072969 + 3 ^ 40 * 1195764 * 2
def baseEnd_1195764 : Nat := 272889636152428800689239

theorem tailTrace_1195764 : CollatzResearch.WordTrace tailWord_1195764 prefixEnd_1195764 272889636152428800689239 := by
  unfold tailWord_1195764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21806548019979361538753173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29075397359972482051670897 21806548019979361538753173)
  ·
    refine ⟨1022181938436532572129055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21806548019979361538753173 1022181938436532572129055)
    ·
      refine ⟨1533272907654798858193583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1022181938436532572129055 1533272907654798858193583)
      ·
        refine ⟨2299909361482198287290375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1533272907654798858193583 2299909361482198287290375)
        ·
          refine ⟨3449864042223297430935563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2299909361482198287290375 3449864042223297430935563)
          ·
            refine ⟨5174796063334946146403345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3449864042223297430935563 5174796063334946146403345)
            ·
              refine ⟨3881097047501209609802509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5174796063334946146403345 3881097047501209609802509)
              ·
                refine ⟨1455411392812953603675941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3881097047501209609802509 1455411392812953603675941)
                ·
                  refine ⟨272889636152428800689239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455411392812953603675941 272889636152428800689239)
                  ·
                    rfl

theorem cell21_1195764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1195764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195764 prefixEnd_1195764 := by exact prefixLift 1195764
  have htrace : WordTrace (prefixWord ++ tailWord_1195764) baseStart_1195764 baseEnd_1195764 := by
    simpa [prefixWord, tailWord_1195764, baseEnd_1195764] using wordTrace_append hprefix tailTrace_1195764
  have hstable : (prefixWord ++ tailWord_1195764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195764).length < 2 ^ (prefixWord ++ tailWord_1195764).sum := by decide
  have hdescent : baseEnd_1195764 < baseStart_1195764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195837 : List Nat := [1, 4, 1, 4, 1, 1, 4, 5]
def baseStart_1195837 : Nat := 118140960795 + 1195837 * 2 ^ 59
def prefixEnd_1195837 : Nat := 4983230072969 + 3 ^ 40 * 1195837 * 2
def baseEnd_1195837 : Nat := 90968765248998965324141

theorem tailTrace_1195837 : CollatzResearch.WordTrace tailWord_1195837 prefixEnd_1195837 90968765248998965324141 := by
  unfold tailWord_1195837
  simp only [CollatzResearch.WordTrace]
  refine ⟨43615758568694256544913765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29077172379129504363275843 43615758568694256544913765)
  ·
    refine ⟨8177954731630173102171331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43615758568694256544913765 8177954731630173102171331)
    ·
      refine ⟨12266932097445259653256997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8177954731630173102171331 12266932097445259653256997)
      ·
        refine ⟨2300049768270986184985687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12266932097445259653256997 2300049768270986184985687)
        ·
          refine ⟨3450074652406479277478531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2300049768270986184985687 3450074652406479277478531)
          ·
            refine ⟨5175111978609718916217797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3450074652406479277478531 5175111978609718916217797)
            ·
              refine ⟨970333495989322296790837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5175111978609718916217797 970333495989322296790837)
              ·
                refine ⟨90968765248998965324141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 970333495989322296790837 90968765248998965324141)
                ·
                  rfl

theorem cell21_1195837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 5].length) (baseStart_1195837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195837 prefixEnd_1195837 := by exact prefixLift 1195837
  have htrace : WordTrace (prefixWord ++ tailWord_1195837) baseStart_1195837 baseEnd_1195837 := by
    simpa [prefixWord, tailWord_1195837, baseEnd_1195837] using wordTrace_append hprefix tailTrace_1195837
  have hstable : (prefixWord ++ tailWord_1195837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195837).length < 2 ^ (prefixWord ++ tailWord_1195837).sum := by decide
  have hdescent : baseEnd_1195837 < baseStart_1195837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1195865 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 4]
def baseStart_1195865 : Nat := 118140960795 + 1195865 * 2 ^ 59
def prefixEnd_1195865 : Nat := 4983230072969 + 3 ^ 40 * 1195865 * 2
def baseEnd_1195865 : Nat := 272912685728475069505699

theorem tailTrace_1195865 : CollatzResearch.WordTrace tailWord_1195865 prefixEnd_1195865 272912685728475069505699 := by
  unfold tailWord_1195865
  simp only [CollatzResearch.WordTrace]
  refine ⟨43616779812592817326933049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29077853208395211551288699 43616779812592817326933049)
  ·
    refine ⟨32712584859444612995199787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43616779812592817326933049 32712584859444612995199787)
    ·
      refine ⟨49068877289166919492799681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32712584859444612995199787 49068877289166919492799681)
      ·
        refine ⟨36801657966875189619599761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49068877289166919492799681 36801657966875189619599761)
        ·
          refine ⟨27601243475156392214699821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36801657966875189619599761 27601243475156392214699821)
          ·
            refine ⟨10350466303183647080512433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27601243475156392214699821 10350466303183647080512433)
            ·
              refine ⟨7762849727387735310384325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10350466303183647080512433 7762849727387735310384325)
              ·
                refine ⟨1455534323885200370697061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7762849727387735310384325 1455534323885200370697061)
                ·
                  refine ⟨272912685728475069505699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455534323885200370697061 272912685728475069505699)
                  ·
                    rfl

theorem cell21_1195865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_1195865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1195865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1195865 prefixEnd_1195865 := by exact prefixLift 1195865
  have htrace : WordTrace (prefixWord ++ tailWord_1195865) baseStart_1195865 baseEnd_1195865 := by
    simpa [prefixWord, tailWord_1195865, baseEnd_1195865] using wordTrace_append hprefix tailTrace_1195865
  have hstable : (prefixWord ++ tailWord_1195865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1195865).length < 2 ^ (prefixWord ++ tailWord_1195865).sum := by decide
  have hdescent : baseEnd_1195865 < baseStart_1195865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1195865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196076 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_1196076 : Nat := 118140960795 + 1196076 * 2 ^ 59
def prefixEnd_1196076 : Nat := 4983230072969 + 3 ^ 40 * 1196076 * 2
def baseEnd_1196076 : Nat := 272960838803185591488601

theorem tailTrace_1196076 : CollatzResearch.WordTrace tailWord_1196076 prefixEnd_1196076 272960838803185591488601 := by
  unfold tailWord_1196076
  simp only [CollatzResearch.WordTrace]
  refine ⟨21812237807414200181432041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29082983743218933575242721 21812237807414200181432041)
  ·
    refine ⟨16359178355560650136074031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21812237807414200181432041 16359178355560650136074031)
    ·
      refine ⟨24538767533340975204111047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16359178355560650136074031 24538767533340975204111047)
      ·
        refine ⟨36808151300011462806166571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24538767533340975204111047 36808151300011462806166571)
        ·
          refine ⟨55212226950017194209249857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36808151300011462806166571 55212226950017194209249857)
          ·
            refine ⟨41409170212512895656937393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55212226950017194209249857 41409170212512895656937393)
            ·
              refine ⟨31056877659384671742703045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41409170212512895656937393 31056877659384671742703045)
              ·
                refine ⟨5823164561134625951756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31056877659384671742703045 5823164561134625951756821)
                ·
                  refine ⟨272960838803185591488601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5823164561134625951756821 272960838803185591488601)
                  ·
                    rfl

theorem cell21_1196076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_1196076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196076 prefixEnd_1196076 := by exact prefixLift 1196076
  have htrace : WordTrace (prefixWord ++ tailWord_1196076) baseStart_1196076 baseEnd_1196076 := by
    simpa [prefixWord, tailWord_1196076, baseEnd_1196076] using wordTrace_append hprefix tailTrace_1196076
  have hstable : (prefixWord ++ tailWord_1196076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196076).length < 2 ^ (prefixWord ++ tailWord_1196076).sum := by decide
  have hdescent : baseEnd_1196076 < baseStart_1196076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196096 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_1196096 : Nat := 118140960795 + 1196096 * 2 ^ 59
def prefixEnd_1196096 : Nat := 4983230072969 + 3 ^ 40 * 1196096 * 2
def baseEnd_1196096 : Nat := 272965403075670001155227

theorem tailTrace_1196096 : CollatzResearch.WordTrace tailWord_1196096 prefixEnd_1196096 272965403075670001155227 := by
  unfold tailWord_1196096
  simp only [CollatzResearch.WordTrace]
  refine ⟨21812602537377971889296071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29083470049837295852394761 21812602537377971889296071)
  ·
    refine ⟨32718903806066957833944107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21812602537377971889296071 32718903806066957833944107)
    ·
      refine ⟨49078355709100436750916161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32718903806066957833944107 49078355709100436750916161)
      ·
        refine ⟨36808766781825327563187121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49078355709100436750916161 36808766781825327563187121)
        ·
          refine ⟨27606575086368995672390341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36808766781825327563187121 27606575086368995672390341)
          ·
            refine ⟨5176232828694186688573189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27606575086368995672390341 5176232828694186688573189)
            ·
              refine ⟨970543655380160004107473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5176232828694186688573189 970543655380160004107473)
              ·
                refine ⟨727907741535120003080605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 970543655380160004107473 727907741535120003080605)
                ·
                  refine ⟨272965403075670001155227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 727907741535120003080605 272965403075670001155227)
                  ·
                    rfl

theorem cell21_1196096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_1196096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196096 prefixEnd_1196096 := by exact prefixLift 1196096
  have htrace : WordTrace (prefixWord ++ tailWord_1196096) baseStart_1196096 baseEnd_1196096 := by
    simpa [prefixWord, tailWord_1196096, baseEnd_1196096] using wordTrace_append hprefix tailTrace_1196096
  have hstable : (prefixWord ++ tailWord_1196096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196096).length < 2 ^ (prefixWord ++ tailWord_1196096).sum := by decide
  have hdescent : baseEnd_1196096 < baseStart_1196096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196206 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 5]
def baseStart_1196206 : Nat := 118140960795 + 1196206 * 2 ^ 59
def prefixEnd_1196206 : Nat := 4983230072969 + 3 ^ 40 * 1196206 * 2
def baseEnd_1196206 : Nat := 272990506574334254321669

theorem tailTrace_1196206 : CollatzResearch.WordTrace tailWord_1196206 prefixEnd_1196206 272990506574334254321669 := by
  unfold tailWord_1196206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453652138044679070637059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29086144736238288376730981 5453652138044679070637059)
  ·
    refine ⟨8180478207067018605955589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453652138044679070637059 8180478207067018605955589)
    ·
      refine ⟨1533839663825065988616673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8180478207067018605955589 1533839663825065988616673)
      ·
        refine ⟨1150379747868799491462505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1533839663825065988616673 1150379747868799491462505)
        ·
          refine ⟨862784810901599618596879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1150379747868799491462505 862784810901599618596879)
          ·
            refine ⟨1294177216352399427895319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862784810901599618596879 1294177216352399427895319)
            ·
              refine ⟨1941265824528599141842979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294177216352399427895319 1941265824528599141842979)
              ·
                refine ⟨2911898736792898712764469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1941265824528599141842979 2911898736792898712764469)
                ·
                  refine ⟨272990506574334254321669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2911898736792898712764469 272990506574334254321669)
                  ·
                    rfl

theorem cell21_1196206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 5].length) (baseStart_1196206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196206 prefixEnd_1196206 := by exact prefixLift 1196206
  have htrace : WordTrace (prefixWord ++ tailWord_1196206) baseStart_1196206 baseEnd_1196206 := by
    simpa [prefixWord, tailWord_1196206, baseEnd_1196206] using wordTrace_append hprefix tailTrace_1196206
  have hstable : (prefixWord ++ tailWord_1196206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196206).length < 2 ^ (prefixWord ++ tailWord_1196206).sum := by decide
  have hdescent : baseEnd_1196206 < baseStart_1196206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196220 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 4]
def baseStart_1196220 : Nat := 118140960795 + 1196220 * 2 ^ 59
def prefixEnd_1196220 : Nat := 4983230072969 + 3 ^ 40 * 1196220 * 2
def baseEnd_1196220 : Nat := 272993701565073341088307

theorem tailTrace_1196220 : CollatzResearch.WordTrace tailWord_1196220 prefixEnd_1196220 272993701565073341088307 := by
  unfold tailWord_1196220
  simp only [CollatzResearch.WordTrace]
  refine ⟨21814863863153356478053057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29086485150871141970737409 21814863863153356478053057)
  ·
    refine ⟨16361147897365017358539793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21814863863153356478053057 16361147897365017358539793)
    ·
      refine ⟨12270860923023763018904845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16361147897365017358539793 12270860923023763018904845)
      ·
        refine ⟨4601572846133911132089317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12270860923023763018904845 4601572846133911132089317)
        ·
          refine ⟨862794908650108337266747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4601572846133911132089317 862794908650108337266747)
          ·
            refine ⟨1294192362975162505900121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862794908650108337266747 1294192362975162505900121)
            ·
              refine ⟨970644272231371879425091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1294192362975162505900121 970644272231371879425091)
              ·
                refine ⟨1455966408347057819137637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 970644272231371879425091 1455966408347057819137637)
                ·
                  refine ⟨272993701565073341088307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1455966408347057819137637 272993701565073341088307)
                  ·
                    rfl

theorem cell21_1196220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_1196220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196220 prefixEnd_1196220 := by exact prefixLift 1196220
  have htrace : WordTrace (prefixWord ++ tailWord_1196220) baseStart_1196220 baseEnd_1196220 := by
    simpa [prefixWord, tailWord_1196220, baseEnd_1196220] using wordTrace_append hprefix tailTrace_1196220
  have hstable : (prefixWord ++ tailWord_1196220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196220).length < 2 ^ (prefixWord ++ tailWord_1196220).sum := by decide
  have hdescent : baseEnd_1196220 < baseStart_1196220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196259 : List Nat := [1, 1, 1, 8, 10]
def baseStart_1196259 : Nat := 118140960795 + 1196259 * 2 ^ 59
def prefixEnd_1196259 : Nat := 4983230072969 + 3 ^ 40 * 1196259 * 2
def baseEnd_1196259 : Nat := 3370402492548369628867

theorem tailTrace_1196259 : CollatzResearch.WordTrace tailWord_1196259 prefixEnd_1196259 3370402492548369628867 := by
  unfold tailWord_1196259
  simp only [CollatzResearch.WordTrace]
  refine ⟨43631150173165422616775831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29087433448776948411183887 43631150173165422616775831)
  ·
    refine ⟨65446725259748133925163747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43631150173165422616775831 65446725259748133925163747)
    ·
      refine ⟨98170087889622200887745621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65446725259748133925163747 98170087889622200887745621)
      ·
        refine ⟨1150430717456510166653269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 98170087889622200887745621 1150430717456510166653269)
        ·
          refine ⟨3370402492548369628867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1150430717456510166653269 3370402492548369628867)
          ·
            rfl

theorem cell21_1196259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 10].length) (baseStart_1196259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196259 prefixEnd_1196259 := by exact prefixLift 1196259
  have htrace : WordTrace (prefixWord ++ tailWord_1196259) baseStart_1196259 baseEnd_1196259 := by
    simpa [prefixWord, tailWord_1196259, baseEnd_1196259] using wordTrace_append hprefix tailTrace_1196259
  have hstable : (prefixWord ++ tailWord_1196259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196259).length < 2 ^ (prefixWord ++ tailWord_1196259).sum := by decide
  have hdescent : baseEnd_1196259 < baseStart_1196259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196321 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 4]
def baseStart_1196321 : Nat := 118140960795 + 1196321 * 2 ^ 59
def prefixEnd_1196321 : Nat := 4983230072969 + 3 ^ 40 * 1196321 * 2
def baseEnd_1196321 : Nat := 273016751141119609904767

theorem tailTrace_1196321 : CollatzResearch.WordTrace tailWord_1196321 prefixEnd_1196321 273016751141119609904767 := by
  unfold tailWord_1196321
  simp only [CollatzResearch.WordTrace]
  refine ⟨43633411498940807205532817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29088940999293871470355211 43633411498940807205532817)
  ·
    refine ⟨32725058624205605404149613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43633411498940807205532817 32725058624205605404149613)
    ·
      refine ⟨12271896984077102026556105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32725058624205605404149613 12271896984077102026556105)
      ·
        refine ⟨9203922738057826519917079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12271896984077102026556105 9203922738057826519917079)
        ·
          refine ⟨13805884107086739779875619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9203922738057826519917079 13805884107086739779875619)
          ·
            refine ⟨20708826160630109669813429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13805884107086739779875619 20708826160630109669813429)
            ·
              refine ⟨1941452452559072781545009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20708826160630109669813429 1941452452559072781545009)
              ·
                refine ⟨1456089339419304586158757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1941452452559072781545009 1456089339419304586158757)
                ·
                  refine ⟨273016751141119609904767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456089339419304586158757 273016751141119609904767)
                  ·
                    rfl

theorem cell21_1196321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_1196321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196321 prefixEnd_1196321 := by exact prefixLift 1196321
  have htrace : WordTrace (prefixWord ++ tailWord_1196321) baseStart_1196321 baseEnd_1196321 := by
    simpa [prefixWord, tailWord_1196321, baseEnd_1196321] using wordTrace_append hprefix tailTrace_1196321
  have hstable : (prefixWord ++ tailWord_1196321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196321).length < 2 ^ (prefixWord ++ tailWord_1196321).sum := by decide
  have hdescent : baseEnd_1196321 < baseStart_1196321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196397 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1196397 : Nat := 118140960795 + 1196397 * 2 ^ 59
def prefixEnd_1196397 : Nat := 4983230072969 + 3 ^ 40 * 1196397 * 2
def baseEnd_1196397 : Nat := 273034095376560366637945

theorem tailTrace_1196397 : CollatzResearch.WordTrace tailWord_1196397 prefixEnd_1196397 273034095376560366637945 := by
  unfold tailWord_1196397
  simp only [CollatzResearch.WordTrace]
  refine ⟨43636183446665472185299445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29090788964443648123532963 43636183446665472185299445)
  ·
    refine ⟨4090892198124888017371823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43636183446665472185299445 4090892198124888017371823)
    ·
      refine ⟨6136338297187332026057735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4090892198124888017371823 6136338297187332026057735)
      ·
        refine ⟨9204507445780998039086603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6136338297187332026057735 9204507445780998039086603)
        ·
          refine ⟨13806761168671497058629905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9204507445780998039086603 13806761168671497058629905)
          ·
            refine ⟨10355070876503622793972429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13806761168671497058629905 10355070876503622793972429)
            ·
              refine ⟨3883151578688858547739661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10355070876503622793972429 3883151578688858547739661)
              ·
                refine ⟨1456181842008321955402373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3883151578688858547739661 1456181842008321955402373)
                ·
                  refine ⟨273034095376560366637945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456181842008321955402373 273034095376560366637945)
                  ·
                    rfl

theorem cell21_1196397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1196397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196397 prefixEnd_1196397 := by exact prefixLift 1196397
  have htrace : WordTrace (prefixWord ++ tailWord_1196397) baseStart_1196397 baseEnd_1196397 := by
    simpa [prefixWord, tailWord_1196397, baseEnd_1196397] using wordTrace_append hprefix tailTrace_1196397
  have hstable : (prefixWord ++ tailWord_1196397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196397).length < 2 ^ (prefixWord ++ tailWord_1196397).sum := by decide
  have hdescent : baseEnd_1196397 < baseStart_1196397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196445 : List Nat := [1, 4, 2, 1, 5, 1, 1, 6]
def baseStart_1196445 : Nat := 118140960795 + 1196445 * 2 ^ 59
def prefixEnd_1196445 : Nat := 4983230072969 + 3 ^ 40 * 1196445 * 2
def baseEnd_1196445 : Nat := 91015016543507649945949

theorem tailTrace_1196445 : CollatzResearch.WordTrace tailWord_1196445 prefixEnd_1196445 91015016543507649945949 := by
  unfold tailWord_1196445
  simp only [CollatzResearch.WordTrace]
  refine ⟨43637934150491576383046789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29091956100327717588697859 43637934150491576383046789)
  ·
    refine ⟨8182112653217170571821273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43637934150491576383046789 8182112653217170571821273)
    ·
      refine ⟨6136584489912877928865955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8182112653217170571821273 6136584489912877928865955)
      ·
        refine ⟨9204876734869316893298933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6136584489912877928865955 9204876734869316893298933)
        ·
          refine ⟨862957193893998458746775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9204876734869316893298933 862957193893998458746775)
          ·
            refine ⟨1294435790840997688120163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 862957193893998458746775 1294435790840997688120163)
            ·
              refine ⟨1941653686261496532180245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294435790840997688120163 1941653686261496532180245)
              ·
                refine ⟨91015016543507649945949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1941653686261496532180245 91015016543507649945949)
                ·
                  rfl

theorem cell21_1196445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 6].length) (baseStart_1196445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196445 prefixEnd_1196445 := by exact prefixLift 1196445
  have htrace : WordTrace (prefixWord ++ tailWord_1196445) baseStart_1196445 baseEnd_1196445 := by
    simpa [prefixWord, tailWord_1196445, baseEnd_1196445] using wordTrace_append hprefix tailTrace_1196445
  have hstable : (prefixWord ++ tailWord_1196445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196445).length < 2 ^ (prefixWord ++ tailWord_1196445).sum := by decide
  have hdescent : baseEnd_1196445 < baseStart_1196445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196476 : List Nat := [2, 2, 2, 4, 1, 2, 2, 3, 3]
def baseStart_1196476 : Nat := 118140960795 + 1196476 * 2 ^ 59
def prefixEnd_1196476 : Nat := 4983230072969 + 3 ^ 40 * 1196476 * 2
def baseEnd_1196476 : Nat := 273052124252873784821117

theorem tailTrace_1196476 : CollatzResearch.WordTrace tailWord_1196476 prefixEnd_1196476 273052124252873784821117 := by
  unfold tailWord_1196476
  simp only [CollatzResearch.WordTrace]
  refine ⟨21819532406689634338712641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29092709875586179118283521 21819532406689634338712641)
  ·
    refine ⟨16364649305017225754034481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21819532406689634338712641 16364649305017225754034481)
    ·
      refine ⟨12273486978762919315525861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16364649305017225754034481 12273486978762919315525861)
      ·
        refine ⟨2301278808518047371661099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12273486978762919315525861 2301278808518047371661099)
        ·
          refine ⟨3451918212777071057491649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2301278808518047371661099 3451918212777071057491649)
          ·
            refine ⟨2588938659582803293118737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3451918212777071057491649 2588938659582803293118737)
            ·
              refine ⟨1941703994687102469839053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2588938659582803293118737 1941703994687102469839053)
              ·
                refine ⟨728138998007663426189645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1941703994687102469839053 728138998007663426189645)
                ·
                  refine ⟨273052124252873784821117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728138998007663426189645 273052124252873784821117)
                  ·
                    rfl

theorem cell21_1196476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 3, 3].length) (baseStart_1196476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196476 prefixEnd_1196476 := by exact prefixLift 1196476
  have htrace : WordTrace (prefixWord ++ tailWord_1196476) baseStart_1196476 baseEnd_1196476 := by
    simpa [prefixWord, tailWord_1196476, baseEnd_1196476] using wordTrace_append hprefix tailTrace_1196476
  have hstable : (prefixWord ++ tailWord_1196476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196476).length < 2 ^ (prefixWord ++ tailWord_1196476).sum := by decide
  have hdescent : baseEnd_1196476 < baseStart_1196476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196577 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 7]
def baseStart_1196577 : Nat := 118140960795 + 1196577 * 2 ^ 59
def prefixEnd_1196577 : Nat := 4983230072969 + 3 ^ 40 * 1196577 * 2
def baseEnd_1196577 : Nat := 273075173828920053637577

theorem tailTrace_1196577 : CollatzResearch.WordTrace tailWord_1196577 prefixEnd_1196577 273075173828920053637577 := by
  unfold tailWord_1196577
  simp only [CollatzResearch.WordTrace]
  refine ⟨43642748586013362926851985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29095165724008908617901323 43642748586013362926851985)
  ·
    refine ⟨32732061439510022195138989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43642748586013362926851985 32732061439510022195138989)
    ·
      refine ⟨12274523039816258323177121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32732061439510022195138989 12274523039816258323177121)
      ·
        refine ⟨9205892279862193742382841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12274523039816258323177121 9205892279862193742382841)
        ·
          refine ⟨6904419209896645306787131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9205892279862193742382841 6904419209896645306787131)
          ·
            refine ⟨10356628814844967960180697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6904419209896645306787131 10356628814844967960180697)
            ·
              refine ⟨7767471611133725970135523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10356628814844967960180697 7767471611133725970135523)
              ·
                refine ⟨11651207416700588955203285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7767471611133725970135523 11651207416700588955203285)
                ·
                  refine ⟨273075173828920053637577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11651207416700588955203285 273075173828920053637577)
                  ·
                    rfl

theorem cell21_1196577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_1196577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196577 prefixEnd_1196577 := by exact prefixLift 1196577
  have htrace : WordTrace (prefixWord ++ tailWord_1196577) baseStart_1196577 baseEnd_1196577 := by
    simpa [prefixWord, tailWord_1196577, baseEnd_1196577] using wordTrace_append hprefix tailTrace_1196577
  have hstable : (prefixWord ++ tailWord_1196577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196577).length < 2 ^ (prefixWord ++ tailWord_1196577).sum := by decide
  have hdescent : baseEnd_1196577 < baseStart_1196577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196608 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_1196608 : Nat := 118140960795 + 1196608 * 2 ^ 59
def prefixEnd_1196608 : Nat := 4983230072969 + 3 ^ 40 * 1196608 * 2
def baseEnd_1196608 : Nat := 273082248451270888620847

theorem tailTrace_1196608 : CollatzResearch.WordTrace tailWord_1196608 prefixEnd_1196608 273082248451270888620847 := by
  unfold tailWord_1196608
  simp only [CollatzResearch.WordTrace]
  refine ⟨21821939624450527610615239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29095919499267370147486985 21821939624450527610615239)
  ·
    refine ⟨32732909436675791415922859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21821939624450527610615239 32732909436675791415922859)
    ·
      refine ⟨49099364155013687123884289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32732909436675791415922859 49099364155013687123884289)
      ·
        refine ⟨36824523116260265342913217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49099364155013687123884289 36824523116260265342913217)
        ·
          refine ⟨27618392337195199007184913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36824523116260265342913217 27618392337195199007184913)
          ·
            refine ⟨20713794252896399255388685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27618392337195199007184913 20713794252896399255388685)
            ·
              refine ⟨7767672844836149720770757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20713794252896399255388685 7767672844836149720770757)
              ·
                refine ⟨1456438658406778072644517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7767672844836149720770757 1456438658406778072644517)
                ·
                  refine ⟨273082248451270888620847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456438658406778072644517 273082248451270888620847)
                  ·
                    rfl

theorem cell21_1196608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_1196608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196608 prefixEnd_1196608 := by exact prefixLift 1196608
  have htrace : WordTrace (prefixWord ++ tailWord_1196608) baseStart_1196608 baseEnd_1196608 := by
    simpa [prefixWord, tailWord_1196608, baseEnd_1196608] using wordTrace_append hprefix tailTrace_1196608
  have hstable : (prefixWord ++ tailWord_1196608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196608).length < 2 ^ (prefixWord ++ tailWord_1196608).sum := by decide
  have hdescent : baseEnd_1196608 < baseStart_1196608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196704 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_1196704 : Nat := 118140960795 + 1196704 * 2 ^ 59
def prefixEnd_1196704 : Nat := 4983230072969 + 3 ^ 40 * 1196704 * 2
def baseEnd_1196704 : Nat := 273104156959196055020651

theorem tailTrace_1196704 : CollatzResearch.WordTrace tailWord_1196704 prefixEnd_1196704 273104156959196055020651 := by
  unfold tailWord_1196704
  simp only [CollatzResearch.WordTrace]
  refine ⟨21823690328276631808362583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29098253771035509077816777 21823690328276631808362583)
  ·
    refine ⟨32735535492414947712543875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21823690328276631808362583 32735535492414947712543875)
    ·
      refine ⟨49103303238622421568815813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32735535492414947712543875 49103303238622421568815813)
      ·
        refine ⟨9206869357241704044152965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49103303238622421568815813 9206869357241704044152965)
        ·
          refine ⟨1726288004482819508278681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9206869357241704044152965 1726288004482819508278681)
          ·
            refine ⟨1294716003362114631209011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1726288004482819508278681 1294716003362114631209011)
            ·
              refine ⟨1942074005043171946813517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1294716003362114631209011 1942074005043171946813517)
              ·
                refine ⟨728277751891189480055069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1942074005043171946813517 728277751891189480055069)
                ·
                  refine ⟨273104156959196055020651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728277751891189480055069 273104156959196055020651)
                  ·
                    rfl

theorem cell21_1196704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_1196704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196704 prefixEnd_1196704 := by exact prefixLift 1196704
  have htrace : WordTrace (prefixWord ++ tailWord_1196704) baseStart_1196704 baseEnd_1196704 := by
    simpa [prefixWord, tailWord_1196704, baseEnd_1196704] using wordTrace_append hprefix tailTrace_1196704
  have hstable : (prefixWord ++ tailWord_1196704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196704).length < 2 ^ (prefixWord ++ tailWord_1196704).sum := by decide
  have hdescent : baseEnd_1196704 < baseStart_1196704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196721 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 3]
def baseStart_1196721 : Nat := 118140960795 + 1196721 * 2 ^ 59
def prefixEnd_1196721 : Nat := 4983230072969 + 3 ^ 40 * 1196721 * 2
def baseEnd_1196721 : Nat := 273108036590807803237283

theorem tailTrace_1196721 : CollatzResearch.WordTrace tailWord_1196721 prefixEnd_1196721 273108036590807803237283 := by
  unfold tailWord_1196721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43648000697491675520094017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29098667131661117013396011 43648000697491675520094017)
  ·
    refine ⟨32736000523118756640070513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43648000697491675520094017 32736000523118756640070513)
    ·
      refine ⟨24552000392339067480052885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32736000523118756640070513 24552000392339067480052885)
      ·
        refine ⟨1150875018390893788127479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24552000392339067480052885 1150875018390893788127479)
        ·
          refine ⟨1726312527586340682191219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1150875018390893788127479 1726312527586340682191219)
          ·
            refine ⟨2589468791379511023286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726312527586340682191219 2589468791379511023286829)
            ·
              refine ⟨971050796767316633732561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2589468791379511023286829 971050796767316633732561)
              ·
                refine ⟨728288097575487475299421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971050796767316633732561 728288097575487475299421)
                ·
                  refine ⟨273108036590807803237283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728288097575487475299421 273108036590807803237283)
                  ·
                    rfl

theorem cell21_1196721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_1196721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196721 prefixEnd_1196721 := by exact prefixLift 1196721
  have htrace : WordTrace (prefixWord ++ tailWord_1196721) baseStart_1196721 baseEnd_1196721 := by
    simpa [prefixWord, tailWord_1196721, baseEnd_1196721] using wordTrace_append hprefix tailTrace_1196721
  have hstable : (prefixWord ++ tailWord_1196721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196721).length < 2 ^ (prefixWord ++ tailWord_1196721).sum := by decide
  have hdescent : baseEnd_1196721 < baseStart_1196721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196743 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_1196743 : Nat := 118140960795 + 1196743 * 2 ^ 59
def prefixEnd_1196743 : Nat := 4983230072969 + 3 ^ 40 * 1196743 * 2
def baseEnd_1196743 : Nat := 273113057290540653870571

theorem tailTrace_1196743 : CollatzResearch.WordTrace tailWord_1196743 prefixEnd_1196743 273113057290540653870571 := by
  unfold tailWord_1196743
  simp only [CollatzResearch.WordTrace]
  refine ⟨43648803103411973277394883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29099202068941315518263255 43648803103411973277394883)
  ·
    refine ⟨65473204655117959916092325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43648803103411973277394883 65473204655117959916092325)
    ·
      refine ⟨12276225872834617484267311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65473204655117959916092325 12276225872834617484267311)
      ·
        refine ⟨18414338809251926226400967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12276225872834617484267311 18414338809251926226400967)
        ·
          refine ⟨27621508213877889339601451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18414338809251926226400967 27621508213877889339601451)
          ·
            refine ⟨41432262320816834009402177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27621508213877889339601451 41432262320816834009402177)
            ·
              refine ⟨31074196740612625507051633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41432262320816834009402177 31074196740612625507051633)
              ·
                refine ⟨23305647555459469130288725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31074196740612625507051633 23305647555459469130288725)
                ·
                  refine ⟨273113057290540653870571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23305647555459469130288725 273113057290540653870571)
                  ·
                    rfl

theorem cell21_1196743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_1196743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196743 prefixEnd_1196743 := by exact prefixLift 1196743
  have htrace : WordTrace (prefixWord ++ tailWord_1196743) baseStart_1196743 baseEnd_1196743 := by
    simpa [prefixWord, tailWord_1196743, baseEnd_1196743] using wordTrace_append hprefix tailTrace_1196743
  have hstable : (prefixWord ++ tailWord_1196743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196743).length < 2 ^ (prefixWord ++ tailWord_1196743).sum := by decide
  have hdescent : baseEnd_1196743 < baseStart_1196743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196819 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 6]
def baseStart_1196819 : Nat := 118140960795 + 1196819 * 2 ^ 59
def prefixEnd_1196819 : Nat := 4983230072969 + 3 ^ 40 * 1196819 * 2
def baseEnd_1196819 : Nat := 273130401525981410603749

theorem tailTrace_1196819 : CollatzResearch.WordTrace tailWord_1196819 prefixEnd_1196819 273130401525981410603749 := by
  unfold tailWord_1196819
  simp only [CollatzResearch.WordTrace]
  refine ⟨43651575051136638257161511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29101050034091092171441007 43651575051136638257161511)
  ·
    refine ⟨65477362576704957385742267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43651575051136638257161511 65477362576704957385742267)
    ·
      refine ⟨98216043865057436078613401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65477362576704957385742267 98216043865057436078613401)
      ·
        refine ⟨73662032898793077058960051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98216043865057436078613401 73662032898793077058960051)
        ·
          refine ⟨110493049348189615588440077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73662032898793077058960051 110493049348189615588440077)
          ·
            refine ⟨41434893505571105845665029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110493049348189615588440077 41434893505571105845665029)
            ·
              refine ⟨7769042532294582346062193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41434893505571105845665029 7769042532294582346062193)
              ·
                refine ⟨5826781899220936759546645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7769042532294582346062193 5826781899220936759546645)
                ·
                  refine ⟨273130401525981410603749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5826781899220936759546645 273130401525981410603749)
                  ·
                    rfl

theorem cell21_1196819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 6].length) (baseStart_1196819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196819 prefixEnd_1196819 := by exact prefixLift 1196819
  have htrace : WordTrace (prefixWord ++ tailWord_1196819) baseStart_1196819 baseEnd_1196819 := by
    simpa [prefixWord, tailWord_1196819, baseEnd_1196819] using wordTrace_append hprefix tailTrace_1196819
  have hstable : (prefixWord ++ tailWord_1196819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196819).length < 2 ^ (prefixWord ++ tailWord_1196819).sum := by decide
  have hdescent : baseEnd_1196819 < baseStart_1196819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196850 : List Nat := [3, 2, 1, 1, 3, 1, 2, 8]
def baseStart_1196850 : Nat := 118140960795 + 1196850 * 2 ^ 59
def prefixEnd_1196850 : Nat := 4983230072969 + 3 ^ 40 * 1196850 * 2
def baseEnd_1196850 : Nat := 91045825382777415195673

theorem tailTrace_1196850 : CollatzResearch.WordTrace tailWord_1196850 prefixEnd_1196850 91045825382777415195673 := by
  unfold tailWord_1196850
  simp only [CollatzResearch.WordTrace]
  refine ⟨10913176428506082637885001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29101803809349553701026669 10913176428506082637885001)
  ·
    refine ⟨8184882321379561978413751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10913176428506082637885001 8184882321379561978413751)
    ·
      refine ⟨12277323482069342967620627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8184882321379561978413751 12277323482069342967620627)
      ·
        refine ⟨18415985223104014451430941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12277323482069342967620627 18415985223104014451430941)
        ·
          refine ⟨6905994458664005419286603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18415985223104014451430941 6905994458664005419286603)
          ·
            refine ⟨10358991687996008128929905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6905994458664005419286603 10358991687996008128929905)
            ·
              refine ⟨7769243765997006096697429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10358991687996008128929905 7769243765997006096697429)
              ·
                refine ⟨91045825382777415195673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7769243765997006096697429 91045825382777415195673)
                ·
                  rfl

theorem cell21_1196850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_1196850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196850 prefixEnd_1196850 := by exact prefixLift 1196850
  have htrace : WordTrace (prefixWord ++ tailWord_1196850) baseStart_1196850 baseEnd_1196850 := by
    simpa [prefixWord, tailWord_1196850, baseEnd_1196850] using wordTrace_append hprefix tailTrace_1196850
  have hstable : (prefixWord ++ tailWord_1196850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196850).length < 2 ^ (prefixWord ++ tailWord_1196850).sum := by decide
  have hdescent : baseEnd_1196850 < baseStart_1196850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196884 : List Nat := [2, 4, 1, 1, 5, 1, 7]
def baseStart_1196884 : Nat := 118140960795 + 1196884 * 2 ^ 59
def prefixEnd_1196884 : Nat := 4983230072969 + 3 ^ 40 * 1196884 * 2
def baseEnd_1196884 : Nat := 30349470601283971335587

theorem tailTrace_1196884 : CollatzResearch.WordTrace tailWord_1196884 prefixEnd_1196884 30349470601283971335587 := by
  unfold tailWord_1196884
  simp only [CollatzResearch.WordTrace]
  refine ⟨21826972897950577179138853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29102630530600769572185137 21826972897950577179138853)
  ·
    refine ⟨4092557418365733221088535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21826972897950577179138853 4092557418365733221088535)
    ·
      refine ⟨6138836127548599831632803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4092557418365733221088535 6138836127548599831632803)
      ·
        refine ⟨9208254191322899747449205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6138836127548599831632803 9208254191322899747449205)
        ·
          refine ⟨863273830436521851323363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9208254191322899747449205 863273830436521851323363)
          ·
            refine ⟨1294910745654782776985045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863273830436521851323363 1294910745654782776985045)
            ·
              refine ⟨30349470601283971335587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1294910745654782776985045 30349470601283971335587)
              ·
                rfl

theorem cell21_1196884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 7].length) (baseStart_1196884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196884 prefixEnd_1196884 := by exact prefixLift 1196884
  have htrace : WordTrace (prefixWord ++ tailWord_1196884) baseStart_1196884 baseEnd_1196884 := by
    simpa [prefixWord, tailWord_1196884, baseEnd_1196884] using wordTrace_append hprefix tailTrace_1196884
  have hstable : (prefixWord ++ tailWord_1196884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196884).length < 2 ^ (prefixWord ++ tailWord_1196884).sum := by decide
  have hdescent : baseEnd_1196884 < baseStart_1196884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196895 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 6]
def baseStart_1196895 : Nat := 118140960795 + 1196895 * 2 ^ 59
def prefixEnd_1196895 : Nat := 4983230072969 + 3 ^ 40 * 1196895 * 2
def baseEnd_1196895 : Nat := 273147745761422167336927

theorem tailTrace_1196895 : CollatzResearch.WordTrace tailWord_1196895 prefixEnd_1196895 273147745761422167336927 := by
  unfold tailWord_1196895
  simp only [CollatzResearch.WordTrace]
  refine ⟨43654346998861303236928139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29102897999240868824618759 43654346998861303236928139)
  ·
    refine ⟨65481520498291954855392209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43654346998861303236928139 65481520498291954855392209)
    ·
      refine ⟨49111140373718966141544157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65481520498291954855392209 49111140373718966141544157)
      ·
        refine ⟨18416677640144612303079059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49111140373718966141544157 18416677640144612303079059)
        ·
          refine ⟨27625016460216918454618589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18416677640144612303079059 27625016460216918454618589)
          ·
            refine ⟨10359381172581344420481971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27625016460216918454618589 10359381172581344420481971)
            ·
              refine ⟨15539071758872016630722957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10359381172581344420481971 15539071758872016630722957)
              ·
                refine ⟨5827151909577006236521109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15539071758872016630722957 5827151909577006236521109)
                ·
                  refine ⟨273147745761422167336927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5827151909577006236521109 273147745761422167336927)
                  ·
                    rfl

theorem cell21_1196895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_1196895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196895 prefixEnd_1196895 := by exact prefixLift 1196895
  have htrace : WordTrace (prefixWord ++ tailWord_1196895) baseStart_1196895 baseEnd_1196895 := by
    simpa [prefixWord, tailWord_1196895, baseEnd_1196895] using wordTrace_append hprefix tailTrace_1196895
  have hstable : (prefixWord ++ tailWord_1196895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196895).length < 2 ^ (prefixWord ++ tailWord_1196895).sum := by decide
  have hdescent : baseEnd_1196895 < baseStart_1196895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196946 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 4]
def baseStart_1196946 : Nat := 118140960795 + 1196946 * 2 ^ 59
def prefixEnd_1196946 : Nat := 4983230072969 + 3 ^ 40 * 1196946 * 2
def baseEnd_1196946 : Nat := 273159384656257411986823

theorem tailTrace_1196946 : CollatzResearch.WordTrace tailWord_1196946 prefixEnd_1196946 273159384656257411986823 := by
  unfold tailWord_1196946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10914051780419134736758673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29104138081117692631356461 10914051780419134736758673)
  ·
    refine ⟨8185538835314351052569005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10914051780419134736758673 8185538835314351052569005)
    ·
      refine ⟨3069577063242881644713377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8185538835314351052569005 3069577063242881644713377)
      ·
        refine ⟨2302182797432161233535033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3069577063242881644713377 2302182797432161233535033)
        ·
          refine ⟨1726637098074120925151275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2302182797432161233535033 1726637098074120925151275)
          ·
            refine ⟨2589955647111181387726913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726637098074120925151275 2589955647111181387726913)
            ·
              refine ⟨1942466735333386040795185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2589955647111181387726913 1942466735333386040795185)
              ·
                refine ⟨1456850051500039530596389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1942466735333386040795185 1456850051500039530596389)
                ·
                  refine ⟨273159384656257411986823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1456850051500039530596389 273159384656257411986823)
                  ·
                    rfl

theorem cell21_1196946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_1196946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196946 prefixEnd_1196946 := by exact prefixLift 1196946
  have htrace : WordTrace (prefixWord ++ tailWord_1196946) baseStart_1196946 baseEnd_1196946 := by
    simpa [prefixWord, tailWord_1196946, baseEnd_1196946] using wordTrace_append hprefix tailTrace_1196946
  have hstable : (prefixWord ++ tailWord_1196946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196946).length < 2 ^ (prefixWord ++ tailWord_1196946).sum := by decide
  have hdescent : baseEnd_1196946 < baseStart_1196946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1196957 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1196957 : Nat := 118140960795 + 1196957 * 2 ^ 59
def prefixEnd_1196957 : Nat := 4983230072969 + 3 ^ 40 * 1196957 * 2
def baseEnd_1196957 : Nat := 273161895006123837303467

theorem tailTrace_1196957 : CollatzResearch.WordTrace tailWord_1196957 prefixEnd_1196957 273161895006123837303467 := by
  unfold tailWord_1196957
  simp only [CollatzResearch.WordTrace]
  refine ⟨43656608324636687825685125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29104405549757791883790083 43656608324636687825685125)
  ·
    refine ⟨8185614060869378967315961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43656608324636687825685125 8185614060869378967315961)
    ·
      refine ⟨6139210545652034225486971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8185614060869378967315961 6139210545652034225486971)
      ·
        refine ⟨9208815818478051338230457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6139210545652034225486971 9208815818478051338230457)
        ·
          refine ⟨6906611863858538503672843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9208815818478051338230457 6906611863858538503672843)
          ·
            refine ⟨10359917795787807755509265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6906611863858538503672843 10359917795787807755509265)
            ·
              refine ⟨7769938346840855816631949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10359917795787807755509265 7769938346840855816631949)
              ·
                refine ⟨2913726880065320931236981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7769938346840855816631949 2913726880065320931236981)
                ·
                  refine ⟨273161895006123837303467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2913726880065320931236981 273161895006123837303467)
                  ·
                    rfl

theorem cell21_1196957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1196957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1196957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1196957 prefixEnd_1196957 := by exact prefixLift 1196957
  have htrace : WordTrace (prefixWord ++ tailWord_1196957) baseStart_1196957 baseEnd_1196957 := by
    simpa [prefixWord, tailWord_1196957, baseEnd_1196957] using wordTrace_append hprefix tailTrace_1196957
  have hstable : (prefixWord ++ tailWord_1196957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1196957).length < 2 ^ (prefixWord ++ tailWord_1196957).sum := by decide
  have hdescent : baseEnd_1196957 < baseStart_1196957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1196957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197067 : List Nat := [1, 1, 1, 1, 6, 3, 3, 2, 3]
def baseStart_1197067 : Nat := 118140960795 + 1197067 * 2 ^ 59
def prefixEnd_1197067 : Nat := 4983230072969 + 3 ^ 40 * 1197067 * 2
def baseEnd_1197067 : Nat := 273186998504788090469909

theorem tailTrace_1197067 : CollatzResearch.WordTrace tailWord_1197067 prefixEnd_1197067 273186998504788090469909 := by
  unfold tailWord_1197067
  simp only [CollatzResearch.WordTrace]
  refine ⟨43660620354238176612189455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29107080236158784408126303 43660620354238176612189455)
  ·
    refine ⟨65490930531357264918284183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43660620354238176612189455 65490930531357264918284183)
    ·
      refine ⟨98236395797035897377426275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65490930531357264918284183 98236395797035897377426275)
      ·
        refine ⟨147354593695553846066139413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98236395797035897377426275 147354593695553846066139413)
        ·
          refine ⟨6907246579479086534350285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 147354593695553846066139413 6907246579479086534350285)
          ·
            refine ⟨2590217467304657450381357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6907246579479086534350285 2590217467304657450381357)
            ·
              refine ⟨971331550239246543893009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2590217467304657450381357 971331550239246543893009)
              ·
                refine ⟨728498662679434907919757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971331550239246543893009 728498662679434907919757)
                ·
                  refine ⟨273186998504788090469909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728498662679434907919757 273186998504788090469909)
                  ·
                    rfl

theorem cell21_1197067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3].length) (baseStart_1197067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197067 prefixEnd_1197067 := by exact prefixLift 1197067
  have htrace : WordTrace (prefixWord ++ tailWord_1197067) baseStart_1197067 baseEnd_1197067 := by
    simpa [prefixWord, tailWord_1197067, baseEnd_1197067] using wordTrace_append hprefix tailTrace_1197067
  have hstable : (prefixWord ++ tailWord_1197067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197067).length < 2 ^ (prefixWord ++ tailWord_1197067).sum := by decide
  have hdescent : baseEnd_1197067 < baseStart_1197067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197095 : List Nat := [1, 1, 7, 1, 1, 1, 2, 7]
def baseStart_1197095 : Nat := 118140960795 + 1197095 * 2 ^ 59
def prefixEnd_1197095 : Nat := 4983230072969 + 3 ^ 40 * 1197095 * 2
def baseEnd_1197095 : Nat := 91064462828755421334395

theorem tailTrace_1197095 : CollatzResearch.WordTrace tailWord_1197095 prefixEnd_1197095 91064462828755421334395 := by
  unfold tailWord_1197095
  simp only [CollatzResearch.WordTrace]
  refine ⟨43661641598136737394208739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29107761065424491596139159 43661641598136737394208739)
  ·
    refine ⟨65492462397205106091313109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43661641598136737394208739 65492462397205106091313109)
    ·
      refine ⟨1534979587434494674015151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 65492462397205106091313109 1534979587434494674015151)
      ·
        refine ⟨2302469381151742011022727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1534979587434494674015151 2302469381151742011022727)
        ·
          refine ⟨3453704071727613016534091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302469381151742011022727 3453704071727613016534091)
          ·
            refine ⟨5180556107591419524801137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453704071727613016534091 5180556107591419524801137)
            ·
              refine ⟨3885417080693564643600853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5180556107591419524801137 3885417080693564643600853)
              ·
                refine ⟨91064462828755421334395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3885417080693564643600853 91064462828755421334395)
                ·
                  rfl

theorem cell21_1197095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 7].length) (baseStart_1197095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197095 prefixEnd_1197095 := by exact prefixLift 1197095
  have htrace : WordTrace (prefixWord ++ tailWord_1197095) baseStart_1197095 baseEnd_1197095 := by
    simpa [prefixWord, tailWord_1197095, baseEnd_1197095] using wordTrace_append hprefix tailTrace_1197095
  have hstable : (prefixWord ++ tailWord_1197095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197095).length < 2 ^ (prefixWord ++ tailWord_1197095).sum := by decide
  have hdescent : baseEnd_1197095 < baseStart_1197095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197140 : List Nat := [2, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1197140 : Nat := 118140960795 + 1197140 * 2 ^ 59
def prefixEnd_1197140 : Nat := 4983230072969 + 3 ^ 40 * 1197140 * 2
def baseEnd_1197140 : Nat := 273203658099356185753093

theorem tailTrace_1197140 : CollatzResearch.WordTrace tailWord_1197140 prefixEnd_1197140 273203658099356185753093 := by
  unfold tailWord_1197140
  simp only [CollatzResearch.WordTrace]
  refine ⟨21831641441486855039798437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29108855255315806719731249 21831641441486855039798437)
  ·
    refine ⟨4093432770278785319962207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21831641441486855039798437 4093432770278785319962207)
    ·
      refine ⟨6140149155418177979943311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4093432770278785319962207 6140149155418177979943311)
      ·
        refine ⟨9210223733127266969914967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6140149155418177979943311 9210223733127266969914967)
        ·
          refine ⟨13815335599690900454872451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9210223733127266969914967 13815335599690900454872451)
          ·
            refine ⟨20723003399536350682308677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13815335599690900454872451 20723003399536350682308677)
            ·
              refine ⟨3885563137413065752932877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20723003399536350682308677 3885563137413065752932877)
              ·
                refine ⟨1457086176529899657349829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3885563137413065752932877 1457086176529899657349829)
                ·
                  refine ⟨273203658099356185753093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457086176529899657349829 273203658099356185753093)
                  ·
                    rfl

theorem cell21_1197140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1197140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197140 prefixEnd_1197140 := by exact prefixLift 1197140
  have htrace : WordTrace (prefixWord ++ tailWord_1197140) baseStart_1197140 baseEnd_1197140 := by
    simpa [prefixWord, tailWord_1197140, baseEnd_1197140] using wordTrace_append hprefix tailTrace_1197140
  have hstable : (prefixWord ++ tailWord_1197140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197140).length < 2 ^ (prefixWord ++ tailWord_1197140).sum := by decide
  have hdescent : baseEnd_1197140 < baseStart_1197140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197160 : List Nat := [2, 1, 4, 4, 1, 1, 2, 3, 3]
def baseStart_1197160 : Nat := 118140960795 + 1197160 * 2 ^ 59
def prefixEnd_1197160 : Nat := 4983230072969 + 3 ^ 40 * 1197160 * 2
def baseEnd_1197160 : Nat := 273208222371840595419719

theorem tailTrace_1197160 : CollatzResearch.WordTrace tailWord_1197160 prefixEnd_1197160 273208222371840595419719 := by
  unfold tailWord_1197160
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832006171450626747662467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29109341561934168996883289 21832006171450626747662467)
  ·
    refine ⟨32748009257175940121493701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832006171450626747662467 32748009257175940121493701)
    ·
      refine ⟨6140251735720488772780069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32748009257175940121493701 6140251735720488772780069)
      ·
        refine ⟨1151297200447591644896263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6140251735720488772780069 1151297200447591644896263)
        ·
          refine ⟨1726945800671387467344395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1151297200447591644896263 1726945800671387467344395)
          ·
            refine ⟨2590418701007081201016593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1726945800671387467344395 2590418701007081201016593)
            ·
              refine ⟨1942814025755310900762445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590418701007081201016593 1942814025755310900762445)
              ·
                refine ⟨728555259658241587785917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1942814025755310900762445 728555259658241587785917)
                ·
                  refine ⟨273208222371840595419719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728555259658241587785917 273208222371840595419719)
                  ·
                    rfl

theorem cell21_1197160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 3, 3].length) (baseStart_1197160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197160 prefixEnd_1197160 := by exact prefixLift 1197160
  have htrace : WordTrace (prefixWord ++ tailWord_1197160) baseStart_1197160 baseEnd_1197160 := by
    simpa [prefixWord, tailWord_1197160, baseEnd_1197160] using wordTrace_append hprefix tailTrace_1197160
  have hstable : (prefixWord ++ tailWord_1197160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197160).length < 2 ^ (prefixWord ++ tailWord_1197160).sum := by decide
  have hdescent : baseEnd_1197160 < baseStart_1197160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197168 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 7]
def baseStart_1197168 : Nat := 118140960795 + 1197168 * 2 ^ 59
def prefixEnd_1197168 : Nat := 4983230072969 + 3 ^ 40 * 1197168 * 2
def baseEnd_1197168 : Nat := 273210048080834359286369

theorem tailTrace_1197168 : CollatzResearch.WordTrace tailWord_1197168 prefixEnd_1197168 273210048080834359286369 := by
  unfold tailWord_1197168
  simp only [CollatzResearch.WordTrace]
  refine ⟨21832152063436135430808079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29109536084581513907744105 21832152063436135430808079)
  ·
    refine ⟨32748228095154203146212119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21832152063436135430808079 32748228095154203146212119)
    ·
      refine ⟨49122342142731304719318179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32748228095154203146212119 49122342142731304719318179)
      ·
        refine ⟨73683513214096957078977269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49122342142731304719318179 73683513214096957078977269)
        ·
          refine ⟨6907829363821589726154119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73683513214096957078977269 6907829363821589726154119)
          ·
            refine ⟨10361744045732384589231179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6907829363821589726154119 10361744045732384589231179)
            ·
              refine ⟨15542616068598576883846769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10361744045732384589231179 15542616068598576883846769)
              ·
                refine ⟨11656962051448932662885077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15542616068598576883846769 11656962051448932662885077)
                ·
                  refine ⟨273210048080834359286369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11656962051448932662885077 273210048080834359286369)
                  ·
                    rfl

theorem cell21_1197168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 7].length) (baseStart_1197168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197168 prefixEnd_1197168 := by exact prefixLift 1197168
  have htrace : WordTrace (prefixWord ++ tailWord_1197168) baseStart_1197168 baseEnd_1197168 := by
    simpa [prefixWord, tailWord_1197168, baseEnd_1197168] using wordTrace_append hprefix tailTrace_1197168
  have hstable : (prefixWord ++ tailWord_1197168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197168).length < 2 ^ (prefixWord ++ tailWord_1197168).sum := by decide
  have hdescent : baseEnd_1197168 < baseStart_1197168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197185 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 5]
def baseStart_1197185 : Nat := 118140960795 + 1197185 * 2 ^ 59
def prefixEnd_1197185 : Nat := 4983230072969 + 3 ^ 40 * 1197185 * 2
def baseEnd_1197185 : Nat := 273213927712446107503001

theorem tailTrace_1197185 : CollatzResearch.WordTrace tailWord_1197185 prefixEnd_1197185 273213927712446107503001 := by
  unfold tailWord_1197185
  simp only [CollatzResearch.WordTrace]
  refine ⟨43664924167810682764985009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29109949445207121843323339 43664924167810682764985009)
  ·
    refine ⟨32748693125858012073738757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43664924167810682764985009 32748693125858012073738757)
    ·
      refine ⟨6140379961098377263826017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32748693125858012073738757 6140379961098377263826017)
      ·
        refine ⟨4605284970823782947869513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6140379961098377263826017 4605284970823782947869513)
        ·
          refine ⟨3453963728117837210902135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4605284970823782947869513 3453963728117837210902135)
          ·
            refine ⟨5180945592176755816353203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3453963728117837210902135 5180945592176755816353203)
            ·
              refine ⟨7771418388265133724529805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5180945592176755816353203 7771418388265133724529805)
              ·
                refine ⟨2914281895599425146698677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7771418388265133724529805 2914281895599425146698677)
                ·
                  refine ⟨273213927712446107503001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914281895599425146698677 273213927712446107503001)
                  ·
                    rfl

theorem cell21_1197185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_1197185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197185 prefixEnd_1197185 := by exact prefixLift 1197185
  have htrace : WordTrace (prefixWord ++ tailWord_1197185) baseStart_1197185 baseEnd_1197185 := by
    simpa [prefixWord, tailWord_1197185, baseEnd_1197185] using wordTrace_append hprefix tailTrace_1197185
  have hstable : (prefixWord ++ tailWord_1197185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197185).length < 2 ^ (prefixWord ++ tailWord_1197185).sum := by decide
  have hdescent : baseEnd_1197185 < baseStart_1197185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197292 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1197292 : Nat := 118140960795 + 1197292 * 2 ^ 59
def prefixEnd_1197292 : Nat := 4983230072969 + 3 ^ 40 * 1197292 * 2
def baseEnd_1197292 : Nat := 273238346570237699219449

theorem tailTrace_1197292 : CollatzResearch.WordTrace tailWord_1197292 prefixEnd_1197292 273238346570237699219449 := by
  unfold tailWord_1197292
  simp only [CollatzResearch.WordTrace]
  refine ⟨21834413389211520019565065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29112551185615360026086753 21834413389211520019565065)
  ·
    refine ⟨16375810041908640014673799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21834413389211520019565065 16375810041908640014673799)
    ·
      refine ⟨24563715062862960022010699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16375810041908640014673799 24563715062862960022010699)
      ·
        refine ⟨36845572594294440033016049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24563715062862960022010699 36845572594294440033016049)
        ·
          refine ⟨27634179445720830024762037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36845572594294440033016049 27634179445720830024762037)
          ·
            refine ⟨2590704323036327814821441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27634179445720830024762037 2590704323036327814821441)
            ·
              refine ⟨1943028242277245861116081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590704323036327814821441 1943028242277245861116081)
              ·
                refine ⟨1457271181707934395837061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943028242277245861116081 1457271181707934395837061)
                ·
                  refine ⟨273238346570237699219449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457271181707934395837061 273238346570237699219449)
                  ·
                    rfl

theorem cell21_1197292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1197292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197292 prefixEnd_1197292 := by exact prefixLift 1197292
  have htrace : WordTrace (prefixWord ++ tailWord_1197292) baseStart_1197292 baseEnd_1197292 := by
    simpa [prefixWord, tailWord_1197292, baseEnd_1197292] using wordTrace_append hprefix tailTrace_1197292
  have hstable : (prefixWord ++ tailWord_1197292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197292).length < 2 ^ (prefixWord ++ tailWord_1197292).sum := by decide
  have hdescent : baseEnd_1197292 < baseStart_1197292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197354 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 5]
def baseStart_1197354 : Nat := 118140960795 + 1197354 * 2 ^ 59
def prefixEnd_1197354 : Nat := 4983230072969 + 3 ^ 40 * 1197354 * 2
def baseEnd_1197354 : Nat := 273252495814939369185989

theorem tailTrace_1197354 : CollatzResearch.WordTrace tailWord_1197354 prefixEnd_1197354 273252495814939369185989 := by
  unfold tailWord_1197354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10917772026049606156971779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29114058736132283085258077 10917772026049606156971779)
  ·
    refine ⟨16376658039074409235457669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10917772026049606156971779 16376658039074409235457669)
    ·
      refine ⟨3070623382326451731648313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16376658039074409235457669 3070623382326451731648313)
      ·
        refine ⟨2302967536744838798736235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3070623382326451731648313 2302967536744838798736235)
        ·
          refine ⟨3454451305117258198104353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2302967536744838798736235 3454451305117258198104353)
          ·
            refine ⟨2590838478837943648578265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3454451305117258198104353 2590838478837943648578265)
            ·
              refine ⟨1943128859128457736433699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2590838478837943648578265 1943128859128457736433699)
              ·
                refine ⟨2914693288692686604650549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943128859128457736433699 2914693288692686604650549)
                ·
                  refine ⟨273252495814939369185989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914693288692686604650549 273252495814939369185989)
                  ·
                    rfl

theorem cell21_1197354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_1197354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197354 prefixEnd_1197354 := by exact prefixLift 1197354
  have htrace : WordTrace (prefixWord ++ tailWord_1197354) baseStart_1197354 baseEnd_1197354 := by
    simpa [prefixWord, tailWord_1197354, baseEnd_1197354] using wordTrace_append hprefix tailTrace_1197354
  have hstable : (prefixWord ++ tailWord_1197354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197354).length < 2 ^ (prefixWord ++ tailWord_1197354).sum := by decide
  have hdescent : baseEnd_1197354 < baseStart_1197354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197405 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1197405 : Nat := 118140960795 + 1197405 * 2 ^ 59
def prefixEnd_1197405 : Nat := 4983230072969 + 3 ^ 40 * 1197405 * 2
def baseEnd_1197405 : Nat := 273264134709774613835885

theorem tailTrace_1197405 : CollatzResearch.WordTrace tailWord_1197405 prefixEnd_1197405 273264134709774613835885 := by
  unfold tailWord_1197405
  simp only [CollatzResearch.WordTrace]
  refine ⟨43672948227013660337993669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29115298818009106891995779 43672948227013660337993669)
  ·
    refine ⟨8188677792565061313373813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43672948227013660337993669 8188677792565061313373813)
    ·
      refine ⟨767688543052974498128795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8188677792565061313373813 767688543052974498128795)
      ·
        refine ⟨1151532814579461747193193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 767688543052974498128795 1151532814579461747193193)
        ·
          refine ⟨863649610934596310394895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1151532814579461747193193 863649610934596310394895)
          ·
            refine ⟨1295474416401894465592343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 863649610934596310394895 1295474416401894465592343)
            ·
              refine ⟨1943211624602841698388515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295474416401894465592343 1943211624602841698388515)
              ·
                refine ⟨2914817436904262547582773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943211624602841698388515 2914817436904262547582773)
                ·
                  refine ⟨273264134709774613835885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914817436904262547582773 273264134709774613835885)
                  ·
                    rfl

theorem cell21_1197405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1197405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197405 prefixEnd_1197405 := by exact prefixLift 1197405
  have htrace : WordTrace (prefixWord ++ tailWord_1197405) baseStart_1197405 baseEnd_1197405 := by
    simpa [prefixWord, tailWord_1197405, baseEnd_1197405] using wordTrace_append hprefix tailTrace_1197405
  have hstable : (prefixWord ++ tailWord_1197405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197405).length < 2 ^ (prefixWord ++ tailWord_1197405).sum := by decide
  have hdescent : baseEnd_1197405 < baseStart_1197405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197458 : List Nat := [3, 2, 3, 3, 10]
def baseStart_1197458 : Nat := 118140960795 + 1197458 * 2 ^ 59
def prefixEnd_1197458 : Nat := 4983230072969 + 3 ^ 40 * 1197458 * 2
def baseEnd_1197458 : Nat := 3373780617677262956203

theorem tailTrace_1197458 : CollatzResearch.WordTrace tailWord_1197458 prefixEnd_1197458 3373780617677262956203 := by
  unfold tailWord_1197458
  simp only [CollatzResearch.WordTrace]
  refine ⟨10918720323955412597418257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29116587530547766926448685 10918720323955412597418257)
  ·
    refine ⟨8189040242966559448063693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10918720323955412597418257 8189040242966559448063693)
    ·
      refine ⟨3070890091112459793023885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8189040242966559448063693 3070890091112459793023885)
      ·
        refine ⟨1151583784167172422383957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3070890091112459793023885 1151583784167172422383957)
        ·
          refine ⟨3373780617677262956203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1151583784167172422383957 3373780617677262956203)
          ·
            rfl

theorem cell21_1197458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 10].length) (baseStart_1197458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197458 prefixEnd_1197458 := by exact prefixLift 1197458
  have htrace : WordTrace (prefixWord ++ tailWord_1197458) baseStart_1197458 baseEnd_1197458 := by
    simpa [prefixWord, tailWord_1197458, baseEnd_1197458] using wordTrace_append hprefix tailTrace_1197458
  have hstable : (prefixWord ++ tailWord_1197458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197458).length < 2 ^ (prefixWord ++ tailWord_1197458).sum := by decide
  have hdescent : baseEnd_1197458 < baseStart_1197458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197464 : List Nat := [2, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_1197464 : Nat := 118140960795 + 1197464 * 2 ^ 59
def prefixEnd_1197464 : Nat := 4983230072969 + 3 ^ 40 * 1197464 * 2
def baseEnd_1197464 : Nat := 273277599313603622352431

theorem tailTrace_1197464 : CollatzResearch.WordTrace tailWord_1197464 prefixEnd_1197464 273277599313603622352431 := by
  unfold tailWord_1197464
  simp only [CollatzResearch.WordTrace]
  refine ⟨21837550066899956707195723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29116733422533275609594297 21837550066899956707195723)
  ·
    refine ⟨32756325100349935060793585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21837550066899956707195723 32756325100349935060793585)
    ·
      refine ⟨24567243825262451295595189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32756325100349935060793585 24567243825262451295595189)
      ·
        refine ⟨2303179108618354808962049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24567243825262451295595189 2303179108618354808962049)
        ·
          refine ⟨1727384331463766106721537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303179108618354808962049 1727384331463766106721537)
          ·
            refine ⟨1295538248597824580041153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727384331463766106721537 1295538248597824580041153)
            ·
              refine ⟨971653686448368435030865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1295538248597824580041153 971653686448368435030865)
              ·
                refine ⟨728740264836276326273149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971653686448368435030865 728740264836276326273149)
                ·
                  refine ⟨273277599313603622352431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728740264836276326273149 273277599313603622352431)
                  ·
                    rfl

theorem cell21_1197464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_1197464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197464 prefixEnd_1197464 := by exact prefixLift 1197464
  have htrace : WordTrace (prefixWord ++ tailWord_1197464) baseStart_1197464 baseEnd_1197464 := by
    simpa [prefixWord, tailWord_1197464, baseEnd_1197464] using wordTrace_append hprefix tailTrace_1197464
  have hstable : (prefixWord ++ tailWord_1197464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197464).length < 2 ^ (prefixWord ++ tailWord_1197464).sum := by decide
  have hdescent : baseEnd_1197464 < baseStart_1197464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197472 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_1197472 : Nat := 118140960795 + 1197472 * 2 ^ 59
def prefixEnd_1197472 : Nat := 4983230072969 + 3 ^ 40 * 1197472 * 2
def baseEnd_1197472 : Nat := 273279425022597386219081

theorem tailTrace_1197472 : CollatzResearch.WordTrace tailWord_1197472 prefixEnd_1197472 273279425022597386219081 := by
  unfold tailWord_1197472
  simp only [CollatzResearch.WordTrace]
  refine ⟨21837695958885465390341335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29116927945180620520455113 21837695958885465390341335)
  ·
    refine ⟨32756543938328198085512003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21837695958885465390341335 32756543938328198085512003)
    ·
      refine ⟨49134815907492297128268005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32756543938328198085512003 49134815907492297128268005)
      ·
        refine ⟨9212777982654805711550251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49134815907492297128268005 9212777982654805711550251)
        ·
          refine ⟨13819166973982208567325377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9212777982654805711550251 13819166973982208567325377)
          ·
            refine ⟨10364375230486656425494033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13819166973982208567325377 10364375230486656425494033)
            ·
              refine ⟨7773281422864992319120525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10364375230486656425494033 7773281422864992319120525)
              ·
                refine ⟨2914980533574372119670197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7773281422864992319120525 2914980533574372119670197)
                ·
                  refine ⟨273279425022597386219081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2914980533574372119670197 273279425022597386219081)
                  ·
                    rfl

theorem cell21_1197472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_1197472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197472 prefixEnd_1197472 := by exact prefixLift 1197472
  have htrace : WordTrace (prefixWord ++ tailWord_1197472) baseStart_1197472 baseEnd_1197472 := by
    simpa [prefixWord, tailWord_1197472, baseEnd_1197472] using wordTrace_append hprefix tailTrace_1197472
  have hstable : (prefixWord ++ tailWord_1197472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197472).length < 2 ^ (prefixWord ++ tailWord_1197472).sum := by decide
  have hdescent : baseEnd_1197472 < baseStart_1197472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197562 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1197562 : Nat := 118140960795 + 1197562 * 2 ^ 59
def prefixEnd_1197562 : Nat := 4983230072969 + 3 ^ 40 * 1197562 * 2
def baseEnd_1197562 : Nat := 273299964248777229718897

theorem tailTrace_1197562 : CollatzResearch.WordTrace tailWord_1197562 prefixEnd_1197562 273299964248777229718897 := by
  unfold tailWord_1197562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10919668621861219037864735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29119116324963250767639293 10919668621861219037864735)
  ·
    refine ⟨16379502932791828556797103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10919668621861219037864735 16379502932791828556797103)
    ·
      refine ⟨24569254399187742835195655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16379502932791828556797103 24569254399187742835195655)
      ·
        refine ⟨36853881598781614252793483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24569254399187742835195655 36853881598781614252793483)
        ·
          refine ⟨55280822398172421379190225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36853881598781614252793483 55280822398172421379190225)
          ·
            refine ⟨41460616798629316034392669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55280822398172421379190225 41460616798629316034392669)
            ·
              refine ⟨15547731299485993512897251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41460616798629316034392669 15547731299485993512897251)
              ·
                refine ⟨23321596949228990269345877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15547731299485993512897251 23321596949228990269345877)
                ·
                  refine ⟨273299964248777229718897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23321596949228990269345877 273299964248777229718897)
                  ·
                    rfl

theorem cell21_1197562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1197562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197562 prefixEnd_1197562 := by exact prefixLift 1197562
  have htrace : WordTrace (prefixWord ++ tailWord_1197562) baseStart_1197562 baseEnd_1197562 := by
    simpa [prefixWord, tailWord_1197562, baseEnd_1197562] using wordTrace_append hprefix tailTrace_1197562
  have hstable : (prefixWord ++ tailWord_1197562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197562).length < 2 ^ (prefixWord ++ tailWord_1197562).sum := by decide
  have hdescent : baseEnd_1197562 < baseStart_1197562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197574 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1197574 : Nat := 118140960795 + 1197574 * 2 ^ 59
def prefixEnd_1197574 : Nat := 4983230072969 + 3 ^ 40 * 1197574 * 2
def baseEnd_1197574 : Nat := 273302702812267875518873

theorem tailTrace_1197574 : CollatzResearch.WordTrace tailWord_1197574 prefixEnd_1197574 273302702812267875518873 := by
  unfold tailWord_1197574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1364972255106293818777993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29119408108934268133930517 1364972255106293818777993)
  ·
    refine ⟨1023729191329720364083495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1364972255106293818777993 1023729191329720364083495)
    ·
      refine ⟨1535593786994580546125243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1023729191329720364083495 1535593786994580546125243)
      ·
        refine ⟨2303390680491870819187865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1535593786994580546125243 2303390680491870819187865)
        ·
          refine ⟨1727543010368903114390899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303390680491870819187865 1727543010368903114390899)
          ·
            refine ⟨2591314515553354671586349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727543010368903114390899 2591314515553354671586349)
            ·
              refine ⟨971742943332508001844881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2591314515553354671586349 971742943332508001844881)
              ·
                refine ⟨728807207499381001383661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 971742943332508001844881 728807207499381001383661)
                ·
                  refine ⟨273302702812267875518873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 728807207499381001383661 273302702812267875518873)
                  ·
                    rfl

theorem cell21_1197574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1197574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197574 prefixEnd_1197574 := by exact prefixLift 1197574
  have htrace : WordTrace (prefixWord ++ tailWord_1197574) baseStart_1197574 baseEnd_1197574 := by
    simpa [prefixWord, tailWord_1197574, baseEnd_1197574] using wordTrace_append hprefix tailTrace_1197574
  have hstable : (prefixWord ++ tailWord_1197574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197574).length < 2 ^ (prefixWord ++ tailWord_1197574).sum := by decide
  have hdescent : baseEnd_1197574 < baseStart_1197574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197582 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1197582 : Nat := 118140960795 + 1197582 * 2 ^ 59
def prefixEnd_1197582 : Nat := 4983230072969 + 3 ^ 40 * 1197582 * 2
def baseEnd_1197582 : Nat := 273304528521261639385523

theorem tailTrace_1197582 : CollatzResearch.WordTrace tailWord_1197582 prefixEnd_1197582 273304528521261639385523 := by
  unfold tailWord_1197582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459925493421552445898375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29119602631581613044791333 5459925493421552445898375)
  ·
    refine ⟨8189888240132328668847563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459925493421552445898375 8189888240132328668847563)
    ·
      refine ⟨12284832360198493003271345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189888240132328668847563 12284832360198493003271345)
      ·
        refine ⟨9213624270148869752453509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12284832360198493003271345 9213624270148869752453509)
        ·
          refine ⟨1727554550652913078585033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9213624270148869752453509 1727554550652913078585033)
          ·
            refine ⟨1295665912989684808938775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1727554550652913078585033 1295665912989684808938775)
            ·
              refine ⟨1943498869484527213408163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1295665912989684808938775 1943498869484527213408163)
              ·
                refine ⟨2915248304226790820112245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1943498869484527213408163 2915248304226790820112245)
                ·
                  refine ⟨273304528521261639385523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2915248304226790820112245 273304528521261639385523)
                  ·
                    rfl

theorem cell21_1197582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1197582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197582 prefixEnd_1197582 := by exact prefixLift 1197582
  have htrace : WordTrace (prefixWord ++ tailWord_1197582) baseStart_1197582 baseEnd_1197582 := by
    simpa [prefixWord, tailWord_1197582, baseEnd_1197582] using wordTrace_append hprefix tailTrace_1197582
  have hstable : (prefixWord ++ tailWord_1197582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197582).length < 2 ^ (prefixWord ++ tailWord_1197582).sum := by decide
  have hdescent : baseEnd_1197582 < baseStart_1197582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197655 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 4]
def baseStart_1197655 : Nat := 118140960795 + 1197655 * 2 ^ 59
def prefixEnd_1197655 : Nat := 4983230072969 + 3 ^ 40 * 1197655 * 2
def baseEnd_1197655 : Nat := 273321188115829734668707

theorem tailTrace_1197655 : CollatzResearch.WordTrace tailWord_1197655 prefixEnd_1197655 273321188115829734668707 := by
  unfold tailWord_1197655
  simp only [CollatzResearch.WordTrace]
  refine ⟨43682066476107953034594419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29121377650738635356396279 43682066476107953034594419)
  ·
    refine ⟨65523099714161929551891629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43682066476107953034594419 65523099714161929551891629)
    ·
      refine ⟨24571162392810723581959361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65523099714161929551891629 24571162392810723581959361)
      ·
        refine ⟨18428371794608042686469521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24571162392810723581959361 18428371794608042686469521)
        ·
          refine ⟨13821278845956032014852141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18428371794608042686469521 13821278845956032014852141)
          ·
            refine ⟨5182979567233512005569553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13821278845956032014852141 5182979567233512005569553)
            ·
              refine ⟨3887234675425134004177165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5182979567233512005569553 3887234675425134004177165)
              ·
                refine ⟨1457713003284425251566437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3887234675425134004177165 1457713003284425251566437)
                ·
                  refine ⟨273321188115829734668707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457713003284425251566437 273321188115829734668707)
                  ·
                    rfl

theorem cell21_1197655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 4].length) (baseStart_1197655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197655 prefixEnd_1197655 := by exact prefixLift 1197655
  have htrace : WordTrace (prefixWord ++ tailWord_1197655) baseStart_1197655 baseEnd_1197655 := by
    simpa [prefixWord, tailWord_1197655, baseEnd_1197655] using wordTrace_append hprefix tailTrace_1197655
  have hstable : (prefixWord ++ tailWord_1197655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197655).length < 2 ^ (prefixWord ++ tailWord_1197655).sum := by decide
  have hdescent : baseEnd_1197655 < baseStart_1197655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197686 : List Nat := [5, 1, 1, 2, 2, 2, 8]
def baseStart_1197686 : Nat := 118140960795 + 1197686 * 2 ^ 59
def prefixEnd_1197686 : Nat := 4983230072969 + 3 ^ 40 * 1197686 * 2
def baseEnd_1197686 : Nat := 30369806970908952183553

theorem tailTrace_1197686 : CollatzResearch.WordTrace tailWord_1197686 prefixEnd_1197686 30369806970908952183553 := by
  unfold tailWord_1197686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2730199821187227833060807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29122131425997096885981941 2730199821187227833060807)
  ·
    refine ⟨4095299731780841749591211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2730199821187227833060807 4095299731780841749591211)
    ·
      refine ⟨6142949597671262624386817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4095299731780841749591211 6142949597671262624386817)
      ·
        refine ⟨4607212198253446968290113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6142949597671262624386817 4607212198253446968290113)
        ·
          refine ⟨3455409148690085226217585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4607212198253446968290113 3455409148690085226217585)
          ·
            refine ⟨2591556861517563919663189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3455409148690085226217585 2591556861517563919663189)
            ·
              refine ⟨30369806970908952183553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2591556861517563919663189 30369806970908952183553)
              ·
                rfl

theorem cell21_1197686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 8].length) (baseStart_1197686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197686 prefixEnd_1197686 := by exact prefixLift 1197686
  have htrace : WordTrace (prefixWord ++ tailWord_1197686) baseStart_1197686 baseEnd_1197686 := by
    simpa [prefixWord, tailWord_1197686, baseEnd_1197686] using wordTrace_append hprefix tailTrace_1197686
  have hstable : (prefixWord ++ tailWord_1197686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197686).length < 2 ^ (prefixWord ++ tailWord_1197686).sum := by decide
  have hdescent : baseEnd_1197686 < baseStart_1197686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197807 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 4]
def baseStart_1197807 : Nat := 118140960795 + 1197807 * 2 ^ 59
def prefixEnd_1197807 : Nat := 4983230072969 + 3 ^ 40 * 1197807 * 2
def baseEnd_1197807 : Nat := 273355876586711248135063

theorem tailTrace_1197807 : CollatzResearch.WordTrace tailWord_1197807 prefixEnd_1197807 273355876586711248135063 := by
  unfold tailWord_1197807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43687610371557282994127675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29125073581038188662751783 43687610371557282994127675)
  ·
    refine ⟨65531415557335924491191513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43687610371557282994127675 65531415557335924491191513)
    ·
      refine ⟨49148561668001943368393635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65531415557335924491191513 49148561668001943368393635)
      ·
        refine ⟨73722842502002915052590453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49148561668001943368393635 73722842502002915052590453)
        ·
          refine ⟨6911516484562773286180355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73722842502002915052590453 6911516484562773286180355)
          ·
            refine ⟨10367274726844159929270533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6911516484562773286180355 10367274726844159929270533)
            ·
              refine ⟨1943864011283279986738225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10367274726844159929270533 1943864011283279986738225)
              ·
                refine ⟨1457898008462459990053669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1943864011283279986738225 1457898008462459990053669)
                ·
                  refine ⟨273355876586711248135063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1457898008462459990053669 273355876586711248135063)
                  ·
                    rfl

theorem cell21_1197807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_1197807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197807 prefixEnd_1197807 := by exact prefixLift 1197807
  have htrace : WordTrace (prefixWord ++ tailWord_1197807) baseStart_1197807 baseEnd_1197807 := by
    simpa [prefixWord, tailWord_1197807, baseEnd_1197807] using wordTrace_append hprefix tailTrace_1197807
  have hstable : (prefixWord ++ tailWord_1197807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197807).length < 2 ^ (prefixWord ++ tailWord_1197807).sum := by decide
  have hdescent : baseEnd_1197807 < baseStart_1197807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197835 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 7]
def baseStart_1197835 : Nat := 118140960795 + 1197835 * 2 ^ 59
def prefixEnd_1197835 : Nat := 4983230072969 + 3 ^ 40 * 1197835 * 2
def baseEnd_1197835 : Nat := 273362266568189421668339

theorem tailTrace_1197835 : CollatzResearch.WordTrace tailWord_1197835 prefixEnd_1197835 273362266568189421668339 := by
  unfold tailWord_1197835
  simp only [CollatzResearch.WordTrace]
  refine ⟨43688631615455843776146959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29125754410303895850764639 43688631615455843776146959)
  ·
    refine ⟨65532947423183765664220439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43688631615455843776146959 65532947423183765664220439)
    ·
      refine ⟨98299421134775648496330659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65532947423183765664220439 98299421134775648496330659)
      ·
        refine ⟨147449131702163472744495989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98299421134775648496330659 147449131702163472744495989)
        ·
          refine ⟨13823356097077825569796499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 147449131702163472744495989 13823356097077825569796499)
          ·
            refine ⟨20735034145616738354694749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13823356097077825569796499 20735034145616738354694749)
            ·
              refine ⟨7775637804606276883010531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20735034145616738354694749 7775637804606276883010531)
              ·
                refine ⟨11663456706909415324515797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7775637804606276883010531 11663456706909415324515797)
                ·
                  refine ⟨273362266568189421668339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11663456706909415324515797 273362266568189421668339)
                  ·
                    rfl

theorem cell21_1197835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 7].length) (baseStart_1197835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197835 prefixEnd_1197835 := by exact prefixLift 1197835
  have htrace : WordTrace (prefixWord ++ tailWord_1197835) baseStart_1197835 baseEnd_1197835 := by
    simpa [prefixWord, tailWord_1197835, baseEnd_1197835] using wordTrace_append hprefix tailTrace_1197835
  have hstable : (prefixWord ++ tailWord_1197835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197835).length < 2 ^ (prefixWord ++ tailWord_1197835).sum := by decide
  have hdescent : baseEnd_1197835 < baseStart_1197835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1197987 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 5]
def baseStart_1197987 : Nat := 118140960795 + 1197987 * 2 ^ 59
def prefixEnd_1197987 : Nat := 4983230072969 + 3 ^ 40 * 1197987 * 2
def baseEnd_1197987 : Nat := 273396955039070935134695

theorem tailTrace_1197987 : CollatzResearch.WordTrace tailWord_1197987 prefixEnd_1197987 273396955039070935134695 := by
  unfold tailWord_1197987
  simp only [CollatzResearch.WordTrace]
  refine ⟨43694175510905173735680215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29129450340603449157120143 43694175510905173735680215)
  ·
    refine ⟨65541263266357760603520323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43694175510905173735680215 65541263266357760603520323)
    ·
      refine ⟨98311894899536640905280485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65541263266357760603520323 98311894899536640905280485)
      ·
        refine ⟨18433480293663120169740091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98311894899536640905280485 18433480293663120169740091)
        ·
          refine ⟨27650220440494680254610137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18433480293663120169740091 27650220440494680254610137)
          ·
            refine ⟨20737665330371010190957603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27650220440494680254610137 20737665330371010190957603)
            ·
              refine ⟨31106497995556515286436405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20737665330371010190957603 31106497995556515286436405)
              ·
                refine ⟨2916234187083423308103413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31106497995556515286436405 2916234187083423308103413)
                ·
                  refine ⟨273396955039070935134695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916234187083423308103413 273396955039070935134695)
                  ·
                    rfl

theorem cell21_1197987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_1197987 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1197987 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1197987 prefixEnd_1197987 := by exact prefixLift 1197987
  have htrace : WordTrace (prefixWord ++ tailWord_1197987) baseStart_1197987 baseEnd_1197987 := by
    simpa [prefixWord, tailWord_1197987, baseEnd_1197987] using wordTrace_append hprefix tailTrace_1197987
  have hstable : (prefixWord ++ tailWord_1197987).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1197987).length < 2 ^ (prefixWord ++ tailWord_1197987).sum := by decide
  have hdescent : baseEnd_1197987 < baseStart_1197987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1197987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198038 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1198038 : Nat := 118140960795 + 1198038 * 2 ^ 59
def prefixEnd_1198038 : Nat := 4983230072969 + 3 ^ 40 * 1198038 * 2
def baseEnd_1198038 : Nat := 273408593933906179784591

theorem tailTrace_1198038 : CollatzResearch.WordTrace tailWord_1198038 prefixEnd_1198038 273408593933906179784591 := by
  unfold tailWord_1198038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731002227107525590361673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29130690422480272963857845 2731002227107525590361673)
  ·
    refine ⟨2048251670330644192771255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2731002227107525590361673 2048251670330644192771255)
    ·
      refine ⟨3072377505495966289156883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048251670330644192771255 3072377505495966289156883)
      ·
        refine ⟨4608566258243949433735325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3072377505495966289156883 4608566258243949433735325)
        ·
          refine ⟨1728212346841481037650747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4608566258243949433735325 1728212346841481037650747)
          ·
            refine ⟨2592318520262221556476121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1728212346841481037650747 2592318520262221556476121)
            ·
              refine ⟨1944238890196666167357091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2592318520262221556476121 1944238890196666167357091)
              ·
                refine ⟨2916358335294999251035637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1944238890196666167357091 2916358335294999251035637)
                ·
                  refine ⟨273408593933906179784591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916358335294999251035637 273408593933906179784591)
                  ·
                    rfl

theorem cell21_1198038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1198038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198038 prefixEnd_1198038 := by exact prefixLift 1198038
  have htrace : WordTrace (prefixWord ++ tailWord_1198038) baseStart_1198038 baseEnd_1198038 := by
    simpa [prefixWord, tailWord_1198038, baseEnd_1198038] using wordTrace_append hprefix tailTrace_1198038
  have hstable : (prefixWord ++ tailWord_1198038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198038).length < 2 ^ (prefixWord ++ tailWord_1198038).sum := by decide
  have hdescent : baseEnd_1198038 < baseStart_1198038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198063 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 5]
def baseStart_1198063 : Nat := 118140960795 + 1198063 * 2 ^ 59
def prefixEnd_1198063 : Nat := 4983230072969 + 3 ^ 40 * 1198063 * 2
def baseEnd_1198063 : Nat := 273414299274511691867873

theorem tailTrace_1198063 : CollatzResearch.WordTrace tailWord_1198063 prefixEnd_1198063 273414299274511691867873 := by
  unfold tailWord_1198063
  simp only [CollatzResearch.WordTrace]
  refine ⟨43696947458629838715446843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29131298305753225810297895 43696947458629838715446843)
  ·
    refine ⟨65545421187944758073170265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43696947458629838715446843 65545421187944758073170265)
    ·
      refine ⟨49159065890958568554877699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65545421187944758073170265 49159065890958568554877699)
      ·
        refine ⟨73738598836437852832316549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49159065890958568554877699 73738598836437852832316549)
        ·
          refine ⟨13825987281832097406059353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73738598836437852832316549 13825987281832097406059353)
          ·
            refine ⟨10369490461374073054544515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13825987281832097406059353 10369490461374073054544515)
            ·
              refine ⟨15554235692061109581816773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10369490461374073054544515 15554235692061109581816773)
              ·
                refine ⟨2916419192261458046590645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15554235692061109581816773 2916419192261458046590645)
                ·
                  refine ⟨273414299274511691867873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916419192261458046590645 273414299274511691867873)
                  ·
                    rfl

theorem cell21_1198063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 5].length) (baseStart_1198063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198063 prefixEnd_1198063 := by exact prefixLift 1198063
  have htrace : WordTrace (prefixWord ++ tailWord_1198063) baseStart_1198063 baseEnd_1198063 := by
    simpa [prefixWord, tailWord_1198063, baseEnd_1198063] using wordTrace_append hprefix tailTrace_1198063
  have hstable : (prefixWord ++ tailWord_1198063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198063).length < 2 ^ (prefixWord ++ tailWord_1198063).sum := by decide
  have hdescent : baseEnd_1198063 < baseStart_1198063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198080 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 3]
def baseStart_1198080 : Nat := 118140960795 + 1198080 * 2 ^ 59
def prefixEnd_1198080 : Nat := 4983230072969 + 3 ^ 40 * 1198080 * 2
def baseEnd_1198080 : Nat := 273418178906123440084505

theorem tailTrace_1198080 : CollatzResearch.WordTrace tailWord_1198080 prefixEnd_1198080 273418178906123440084505 := by
  unfold tailWord_1198080
  simp only [CollatzResearch.WordTrace]
  refine ⟨21848783749784125309407847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29131711666378833745877129 21848783749784125309407847)
  ·
    refine ⟨32773175624676187964111771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21848783749784125309407847 32773175624676187964111771)
    ·
      refine ⟨49159763437014281946167657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32773175624676187964111771 49159763437014281946167657)
      ·
        refine ⟨36869822577760711459625743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49159763437014281946167657 36869822577760711459625743)
        ·
          refine ⟨55304733866641067189438615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36869822577760711459625743 55304733866641067189438615)
          ·
            refine ⟨82957100799961600784157923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55304733866641067189438615 82957100799961600784157923)
            ·
              refine ⟨124435651199942401176236885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82957100799961600784157923 124435651199942401176236885)
              ·
                refine ⟨729115143749662506892013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 124435651199942401176236885 729115143749662506892013)
                ·
                  refine ⟨273418178906123440084505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729115143749662506892013 273418178906123440084505)
                  ·
                    rfl

theorem cell21_1198080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 3].length) (baseStart_1198080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198080 prefixEnd_1198080 := by exact prefixLift 1198080
  have htrace : WordTrace (prefixWord ++ tailWord_1198080) baseStart_1198080 baseEnd_1198080 := by
    simpa [prefixWord, tailWord_1198080, baseEnd_1198080] using wordTrace_append hprefix tailTrace_1198080
  have hstable : (prefixWord ++ tailWord_1198080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198080).length < 2 ^ (prefixWord ++ tailWord_1198080).sum := by decide
  have hdescent : baseEnd_1198080 < baseStart_1198080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198094 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1198094 : Nat := 118140960795 + 1198094 * 2 ^ 59
def prefixEnd_1198094 : Nat := 4983230072969 + 3 ^ 40 * 1198094 * 2
def baseEnd_1198094 : Nat := 273421373896862526851143

theorem tailTrace_1198094 : CollatzResearch.WordTrace tailWord_1198094 prefixEnd_1198094 273421373896862526851143 := by
  unfold tailWord_1198094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462259765189691376228167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29132052081011687339883557 5462259765189691376228167)
  ·
    refine ⟨8193389647784537064342251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5462259765189691376228167 8193389647784537064342251)
    ·
      refine ⟨12290084471676805596513377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8193389647784537064342251 12290084471676805596513377)
      ·
        refine ⟨9217563353757604197385033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12290084471676805596513377 9217563353757604197385033)
        ·
          refine ⟨6913172515318203148038775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9217563353757604197385033 6913172515318203148038775)
          ·
            refine ⟨10369758772977304722058163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6913172515318203148038775 10369758772977304722058163)
            ·
              refine ⟨15554638159465957083087245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10369758772977304722058163 15554638159465957083087245)
              ·
                refine ⟨5832989309799733906157717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15554638159465957083087245 5832989309799733906157717)
                ·
                  refine ⟨273421373896862526851143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5832989309799733906157717 273421373896862526851143)
                  ·
                    rfl

theorem cell21_1198094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1198094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198094 prefixEnd_1198094 := by exact prefixLift 1198094
  have htrace : WordTrace (prefixWord ++ tailWord_1198094) baseStart_1198094 baseEnd_1198094 := by
    simpa [prefixWord, tailWord_1198094, baseEnd_1198094] using wordTrace_append hprefix tailTrace_1198094
  have hstable : (prefixWord ++ tailWord_1198094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198094).length < 2 ^ (prefixWord ++ tailWord_1198094).sum := by decide
  have hdescent : baseEnd_1198094 < baseStart_1198094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198142 : List Nat := [4, 2, 1, 3, 3, 8]
def baseStart_1198142 : Nat := 118140960795 + 1198142 * 2 ^ 59
def prefixEnd_1198142 : Nat := 4983230072969 + 3 ^ 40 * 1198142 * 2
def baseEnd_1198142 : Nat := 10127123264845374446335

theorem tailTrace_1198142 : CollatzResearch.WordTrace tailWord_1198142 prefixEnd_1198142 10127123264845374446335 := by
  unfold tailWord_1198142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5462478603167954400946585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29133219216895756805048453 5462478603167954400946585)
  ·
    refine ⟨4096858952375965800709939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5462478603167954400946585 4096858952375965800709939)
    ·
      refine ⟨6145288428563948701064909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4096858952375965800709939 6145288428563948701064909)
      ·
        refine ⟨2304483160711480762899341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6145288428563948701064909 2304483160711480762899341)
        ·
          refine ⟨864181185266805286087253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2304483160711480762899341 864181185266805286087253)
          ·
            refine ⟨10127123264845374446335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 864181185266805286087253 10127123264845374446335)
            ·
              rfl

theorem cell21_1198142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 8].length) (baseStart_1198142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198142 prefixEnd_1198142 := by exact prefixLift 1198142
  have htrace : WordTrace (prefixWord ++ tailWord_1198142) baseStart_1198142 baseEnd_1198142 := by
    simpa [prefixWord, tailWord_1198142, baseEnd_1198142] using wordTrace_append hprefix tailTrace_1198142
  have hstable : (prefixWord ++ tailWord_1198142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198142).length < 2 ^ (prefixWord ++ tailWord_1198142).sum := by decide
  have hdescent : baseEnd_1198142 < baseStart_1198142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198170 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 4]
def baseStart_1198170 : Nat := 118140960795 + 1198170 * 2 ^ 59
def prefixEnd_1198170 : Nat := 4983230072969 + 3 ^ 40 * 1198170 * 2
def baseEnd_1198170 : Nat := 273438718132303283584321

theorem tailTrace_1198170 : CollatzResearch.WordTrace tailWord_1198170 prefixEnd_1198170 273438718132303283584321 := by
  unfold tailWord_1198170
  simp only [CollatzResearch.WordTrace]
  refine ⟨10925212517310548997397991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29133900046161463993061309 10925212517310548997397991)
  ·
    refine ⟨16387818775965823496096987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10925212517310548997397991 16387818775965823496096987)
    ·
      refine ⟨24581728163948735244145481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16387818775965823496096987 24581728163948735244145481)
      ·
        refine ⟨18436296122961551433109111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24581728163948735244145481 18436296122961551433109111)
        ·
          refine ⟨27654444184442327149663667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18436296122961551433109111 27654444184442327149663667)
          ·
            refine ⟨41481666276663490724495501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27654444184442327149663667 41481666276663490724495501)
            ·
              refine ⟨15555624853748809021685813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41481666276663490724495501 15555624853748809021685813)
              ·
                refine ⟨1458339830038950845783045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15555624853748809021685813 1458339830038950845783045)
                ·
                  refine ⟨273438718132303283584321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458339830038950845783045 273438718132303283584321)
                  ·
                    rfl

theorem cell21_1198170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_1198170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198170 prefixEnd_1198170 := by exact prefixLift 1198170
  have htrace : WordTrace (prefixWord ++ tailWord_1198170) baseStart_1198170 baseEnd_1198170 := by
    simpa [prefixWord, tailWord_1198170, baseEnd_1198170] using wordTrace_append hprefix tailTrace_1198170
  have hstable : (prefixWord ++ tailWord_1198170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198170).length < 2 ^ (prefixWord ++ tailWord_1198170).sum := by decide
  have hdescent : baseEnd_1198170 < baseStart_1198170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198173 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1198173 : Nat := 118140960795 + 1198173 * 2 ^ 59
def prefixEnd_1198173 : Nat := 4983230072969 + 3 ^ 40 * 1198173 * 2
def baseEnd_1198173 : Nat := 273439402773175945034315

theorem tailTrace_1198173 : CollatzResearch.WordTrace tailWord_1198173 prefixEnd_1198173 273439402773175945034315 := by
  unfold tailWord_1198173
  simp only [CollatzResearch.WordTrace]
  refine ⟨43700959488231327501951173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29133972992154218334634115 43700959488231327501951173)
  ·
    refine ⟨8193929904043373906615845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43700959488231327501951173 8193929904043373906615845)
    ·
      refine ⟨1536361857008132607490471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8193929904043373906615845 1536361857008132607490471)
      ·
        refine ⟨2304542785512198911235707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536361857008132607490471 2304542785512198911235707)
        ·
          refine ⟨3456814178268298366853561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304542785512198911235707 3456814178268298366853561)
          ·
            refine ⟨2592610633701223775140171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3456814178268298366853561 2592610633701223775140171)
            ·
              refine ⟨3888915950551835662710257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2592610633701223775140171 3888915950551835662710257)
              ·
                refine ⟨2916686962913876747032693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3888915950551835662710257 2916686962913876747032693)
                ·
                  refine ⟨273439402773175945034315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916686962913876747032693 273439402773175945034315)
                  ·
                    rfl

theorem cell21_1198173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1198173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198173 prefixEnd_1198173 := by exact prefixLift 1198173
  have htrace : WordTrace (prefixWord ++ tailWord_1198173) baseStart_1198173 baseEnd_1198173 := by
    simpa [prefixWord, tailWord_1198173, baseEnd_1198173] using wordTrace_append hprefix tailTrace_1198173
  have hstable : (prefixWord ++ tailWord_1198173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198173).length < 2 ^ (prefixWord ++ tailWord_1198173).sum := by decide
  have hdescent : baseEnd_1198173 < baseStart_1198173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198215 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 5]
def baseStart_1198215 : Nat := 118140960795 + 1198215 * 2 ^ 59
def prefixEnd_1198215 : Nat := 4983230072969 + 3 ^ 40 * 1198215 * 2
def baseEnd_1198215 : Nat := 273448987745393205334229

theorem tailTrace_1198215 : CollatzResearch.WordTrace tailWord_1198215 prefixEnd_1198215 273448987745393205334229 := by
  unfold tailWord_1198215
  simp only [CollatzResearch.WordTrace]
  refine ⟨43702491354079168674980099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29134994236052779116653399 43702491354079168674980099)
  ·
    refine ⟨65553737031118753012470149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43702491354079168674980099 65553737031118753012470149)
    ·
      refine ⟨12291325693334766189838153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65553737031118753012470149 12291325693334766189838153)
      ·
        refine ⟨9218494270001074642378615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12291325693334766189838153 9218494270001074642378615)
        ·
          refine ⟨13827741405001611963567923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9218494270001074642378615 13827741405001611963567923)
          ·
            refine ⟨20741612107502417945351885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13827741405001611963567923 20741612107502417945351885)
            ·
              refine ⟨7778104540313406729506957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20741612107502417945351885 7778104540313406729506957)
              ·
                refine ⟨2916789202617527523565109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7778104540313406729506957 2916789202617527523565109)
                ·
                  refine ⟨273448987745393205334229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2916789202617527523565109 273448987745393205334229)
                  ·
                    rfl

theorem cell21_1198215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_1198215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198215 prefixEnd_1198215 := by exact prefixLift 1198215
  have htrace : WordTrace (prefixWord ++ tailWord_1198215) baseStart_1198215 baseEnd_1198215 := by
    simpa [prefixWord, tailWord_1198215, baseEnd_1198215] using wordTrace_append hprefix tailTrace_1198215
  have hstable : (prefixWord ++ tailWord_1198215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198215).length < 2 ^ (prefixWord ++ tailWord_1198215).sum := by decide
  have hdescent : baseEnd_1198215 < baseStart_1198215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198294 : List Nat := [5, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1198294 : Nat := 118140960795 + 1198294 * 2 ^ 59
def prefixEnd_1198294 : Nat := 4983230072969 + 3 ^ 40 * 1198294 * 2
def baseEnd_1198294 : Nat := 91155672207235541172467

theorem tailTrace_1198294 : CollatzResearch.WordTrace tailWord_1198294 prefixEnd_1198294 91155672207235541172467 := by
  unfold tailWord_1198294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2731585795049560322944121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29136915147195310111403957 2731585795049560322944121)
  ·
    refine ⟨2048689346287170242208091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2731585795049560322944121 2048689346287170242208091)
    ·
      refine ⟨3073034019430755363312137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2048689346287170242208091 3073034019430755363312137)
      ·
        refine ⟨2304775514573066522484103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073034019430755363312137 2304775514573066522484103)
        ·
          refine ⟨3457163271859599783726155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2304775514573066522484103 3457163271859599783726155)
          ·
            refine ⟨5185744907789399675589233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3457163271859599783726155 5185744907789399675589233)
            ·
              refine ⟨3889308680842049756691925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5185744907789399675589233 3889308680842049756691925)
              ·
                refine ⟨91155672207235541172467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3889308680842049756691925 91155672207235541172467)
                ·
                  rfl

theorem cell21_1198294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1198294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198294 prefixEnd_1198294 := by exact prefixLift 1198294
  have htrace : WordTrace (prefixWord ++ tailWord_1198294) baseStart_1198294 baseEnd_1198294 := by
    simpa [prefixWord, tailWord_1198294, baseEnd_1198294] using wordTrace_append hprefix tailTrace_1198294
  have hstable : (prefixWord ++ tailWord_1198294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198294).length < 2 ^ (prefixWord ++ tailWord_1198294).sum := by decide
  have hdescent : baseEnd_1198294 < baseStart_1198294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198308 : List Nat := [2, 3, 1, 1, 1, 2, 1, 7, 3]
def baseStart_1198308 : Nat := 118140960795 + 1198308 * 2 ^ 59
def prefixEnd_1198308 : Nat := 4983230072969 + 3 ^ 40 * 1198308 * 2
def baseEnd_1198308 : Nat := 273470211612445710284039

theorem tailTrace_1198308 : CollatzResearch.WordTrace tailWord_1198308 prefixEnd_1198308 273470211612445710284039 := by
  unfold tailWord_1198308
  simp only [CollatzResearch.WordTrace]
  refine ⟨21852941671371122779057789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29137255561828163705410385 21852941671371122779057789)
  ·
    refine ⟨8194853126764171042146671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21852941671371122779057789 8194853126764171042146671)
    ·
      refine ⟨12292279690146256563220007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8194853126764171042146671 12292279690146256563220007)
      ·
        refine ⟨18438419535219384844830011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12292279690146256563220007 18438419535219384844830011)
        ·
          refine ⟨27657629302829077267245017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18438419535219384844830011 27657629302829077267245017)
          ·
            refine ⟨20743221977121807950433763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27657629302829077267245017 20743221977121807950433763)
            ·
              refine ⟨31114832965682711925650645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20743221977121807950433763 31114832965682711925650645)
              ·
                refine ⟨729253897633188560757437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31114832965682711925650645 729253897633188560757437)
                ·
                  refine ⟨273470211612445710284039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729253897633188560757437 273470211612445710284039)
                  ·
                    rfl

theorem cell21_1198308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_1198308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198308 prefixEnd_1198308 := by exact prefixLift 1198308
  have htrace : WordTrace (prefixWord ++ tailWord_1198308) baseStart_1198308 baseEnd_1198308 := by
    simpa [prefixWord, tailWord_1198308, baseEnd_1198308] using wordTrace_append hprefix tailTrace_1198308
  have hstable : (prefixWord ++ tailWord_1198308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198308).length < 2 ^ (prefixWord ++ tailWord_1198308).sum := by decide
  have hdescent : baseEnd_1198308 < baseStart_1198308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198336 : List Nat := [2, 1, 1, 2, 1, 1, 7, 6]
def baseStart_1198336 : Nat := 118140960795 + 1198336 * 2 ^ 59
def prefixEnd_1198336 : Nat := 4983230072969 + 3 ^ 40 * 1198336 * 2
def baseEnd_1198336 : Nat := 91158867197974627939105

theorem tailTrace_1198336 : CollatzResearch.WordTrace tailWord_1198336 prefixEnd_1198336 91158867197974627939105 := by
  unfold tailWord_1198336
  simp only [CollatzResearch.WordTrace]
  refine ⟨21853452293320403170067431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29137936391093870893423241 21853452293320403170067431)
  ·
    refine ⟨32780178439980604755101147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21853452293320403170067431 32780178439980604755101147)
    ·
      refine ⟨49170267659970907132651721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32780178439980604755101147 49170267659970907132651721)
      ·
        refine ⟨36877700744978180349488791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49170267659970907132651721 36877700744978180349488791)
        ·
          refine ⟨55316551117467270524233187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36877700744978180349488791 55316551117467270524233187)
          ·
            refine ⟨82974826676200905786349781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55316551117467270524233187 82974826676200905786349781)
            ·
              refine ⟨1944722500223458729367573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82974826676200905786349781 1944722500223458729367573)
              ·
                refine ⟨91158867197974627939105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1944722500223458729367573 91158867197974627939105)
                ·
                  rfl

theorem cell21_1198336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_1198336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198336 prefixEnd_1198336 := by exact prefixLift 1198336
  have htrace : WordTrace (prefixWord ++ tailWord_1198336) baseStart_1198336 baseEnd_1198336 := by
    simpa [prefixWord, tailWord_1198336, baseEnd_1198336] using wordTrace_append hprefix tailTrace_1198336
  have hstable : (prefixWord ++ tailWord_1198336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198336).length < 2 ^ (prefixWord ++ tailWord_1198336).sum := by decide
  have hdescent : baseEnd_1198336 < baseStart_1198336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198353 : List Nat := [1, 2, 2, 1, 1, 6, 3, 5]
def baseStart_1198353 : Nat := 118140960795 + 1198353 * 2 ^ 59
def prefixEnd_1198353 : Nat := 4983230072969 + 3 ^ 40 * 1198353 * 2
def baseEnd_1198353 : Nat := 91160160408511877344649

theorem tailTrace_1198353 : CollatzResearch.WordTrace tailWord_1198353 prefixEnd_1198353 91160160408511877344649 := by
  unfold tailWord_1198353
  simp only [CollatzResearch.WordTrace]
  refine ⟨43707524627579218243503713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29138349751719478829002475 43707524627579218243503713)
  ·
    refine ⟨32780643470684413682627785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43707524627579218243503713 32780643470684413682627785)
    ·
      refine ⟨24585482603013310261970839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32780643470684413682627785 24585482603013310261970839)
      ·
        refine ⟨36878223904519965392956259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24585482603013310261970839 36878223904519965392956259)
        ·
          refine ⟨55317335856779948089434389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36878223904519965392956259 55317335856779948089434389)
          ·
            refine ⟨2593000118286560066692237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55317335856779948089434389 2593000118286560066692237)
            ·
              refine ⟨972375044357460025009589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593000118286560066692237 972375044357460025009589)
              ·
                refine ⟨91160160408511877344649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 972375044357460025009589 91160160408511877344649)
                ·
                  rfl

theorem cell21_1198353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 5].length) (baseStart_1198353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198353 prefixEnd_1198353 := by exact prefixLift 1198353
  have htrace : WordTrace (prefixWord ++ tailWord_1198353) baseStart_1198353 baseEnd_1198353 := by
    simpa [prefixWord, tailWord_1198353, baseEnd_1198353] using wordTrace_append hprefix tailTrace_1198353
  have hstable : (prefixWord ++ tailWord_1198353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198353).length < 2 ^ (prefixWord ++ tailWord_1198353).sum := by decide
  have hdescent : baseEnd_1198353 < baseStart_1198353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198404 : List Nat := [2, 3, 4, 1, 3, 1, 2, 5]
def baseStart_1198404 : Nat := 118140960795 + 1198404 * 2 ^ 59
def prefixEnd_1198404 : Nat := 4983230072969 + 3 ^ 40 * 1198404 * 2
def baseEnd_1198404 : Nat := 91164040040123625561281

theorem tailTrace_1198404 : CollatzResearch.WordTrace tailWord_1198404 prefixEnd_1198404 91164040040123625561281 := by
  unfold tailWord_1198404
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854692375197226976805133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29139589833596302635740177 21854692375197226976805133)
  ·
    refine ⟨8195509640698960116301925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21854692375197226976805133 8195509640698960116301925)
    ·
      refine ⟨1536658057631055021806611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8195509640698960116301925 1536658057631055021806611)
      ·
        refine ⟨2304987086446582532709917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1536658057631055021806611 2304987086446582532709917)
        ·
          refine ⟨864370157417468449766219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2304987086446582532709917 864370157417468449766219)
          ·
            refine ⟨1296555236126202674649329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864370157417468449766219 1296555236126202674649329)
            ·
              refine ⟨972416427094652005986997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296555236126202674649329 972416427094652005986997)
              ·
                refine ⟨91164040040123625561281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 972416427094652005986997 91164040040123625561281)
                ·
                  rfl

theorem cell21_1198404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 2, 5].length) (baseStart_1198404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198404 prefixEnd_1198404 := by exact prefixLift 1198404
  have htrace : WordTrace (prefixWord ++ tailWord_1198404) baseStart_1198404 baseEnd_1198404 := by
    simpa [prefixWord, tailWord_1198404, baseEnd_1198404] using wordTrace_append hprefix tailTrace_1198404
  have hstable : (prefixWord ++ tailWord_1198404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198404).length < 2 ^ (prefixWord ++ tailWord_1198404).sum := by decide
  have hdescent : baseEnd_1198404 < baseStart_1198404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198412 : List Nat := [2, 2, 1, 3, 2, 1, 3, 7]
def baseStart_1198412 : Nat := 118140960795 + 1198412 * 2 ^ 59
def prefixEnd_1198412 : Nat := 4983230072969 + 3 ^ 40 * 1198412 * 2
def baseEnd_1198412 : Nat := 91164648609788213516831

theorem tailTrace_1198412 : CollatzResearch.WordTrace tailWord_1198412 prefixEnd_1198412 91164648609788213516831 := by
  unfold tailWord_1198412
  simp only [CollatzResearch.WordTrace]
  refine ⟨21854838267182735659950745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29139784356243647546600993 21854838267182735659950745)
  ·
    refine ⟨16391128700387051744963059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21854838267182735659950745 16391128700387051744963059)
    ·
      refine ⟨24586693050580577617444589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16391128700387051744963059 24586693050580577617444589)
      ·
        refine ⟨9220009893967716606541721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24586693050580577617444589 9220009893967716606541721)
        ·
          refine ⟨6915007420475787454906291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9220009893967716606541721 6915007420475787454906291)
          ·
            refine ⟨10372511130713681182359437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915007420475787454906291 10372511130713681182359437)
            ·
              refine ⟨3889691674017630443384789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10372511130713681182359437 3889691674017630443384789)
              ·
                refine ⟨91164648609788213516831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3889691674017630443384789 91164648609788213516831)
                ·
                  rfl

theorem cell21_1198412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 7].length) (baseStart_1198412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198412 prefixEnd_1198412 := by exact prefixLift 1198412
  have htrace : WordTrace (prefixWord ++ tailWord_1198412) baseStart_1198412 baseEnd_1198412 := by
    simpa [prefixWord, tailWord_1198412, baseEnd_1198412] using wordTrace_append hprefix tailTrace_1198412
  have hstable : (prefixWord ++ tailWord_1198412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198412).length < 2 ^ (prefixWord ++ tailWord_1198412).sum := by decide
  have hdescent : baseEnd_1198412 < baseStart_1198412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198486 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1198486 : Nat := 118140960795 + 1198486 * 2 ^ 59
def prefixEnd_1198486 : Nat := 4983230072969 + 3 ^ 40 * 1198486 * 2
def baseEnd_1198486 : Nat := 273510833637556956317009

theorem tailTrace_1198486 : CollatzResearch.WordTrace tailWord_1198486 prefixEnd_1198486 273510833637556956317009 := by
  unfold tailWord_1198486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732023471006086372380957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29141583690731587972063541 2732023471006086372380957)
  ·
    refine ⟨1024508801627282389642859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2732023471006086372380957 1024508801627282389642859)
    ·
      refine ⟨1536763202440923584464289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024508801627282389642859 1536763202440923584464289)
      ·
        refine ⟨1152572401830692688348217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1536763202440923584464289 1152572401830692688348217)
        ·
          refine ⟨864429301373019516261163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1152572401830692688348217 864429301373019516261163)
          ·
            refine ⟨1296643952059529274391745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864429301373019516261163 1296643952059529274391745)
            ·
              refine ⟨972482964044646955793809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1296643952059529274391745 972482964044646955793809)
              ·
                refine ⟨729362223033485216845357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972482964044646955793809 729362223033485216845357)
                ·
                  refine ⟨273510833637556956317009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729362223033485216845357 273510833637556956317009)
                  ·
                    rfl

theorem cell21_1198486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1198486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198486 prefixEnd_1198486 := by exact prefixLift 1198486
  have htrace : WordTrace (prefixWord ++ tailWord_1198486) baseStart_1198486 baseEnd_1198486 := by
    simpa [prefixWord, tailWord_1198486, baseEnd_1198486] using wordTrace_append hprefix tailTrace_1198486
  have hstable : (prefixWord ++ tailWord_1198486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198486).length < 2 ^ (prefixWord ++ tailWord_1198486).sum := by decide
  have hdescent : baseEnd_1198486 < baseStart_1198486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198488 : List Nat := [2, 1, 2, 5, 1, 10]
def baseStart_1198488 : Nat := 118140960795 + 1198488 * 2 ^ 59
def prefixEnd_1198488 : Nat := 4983230072969 + 3 ^ 40 * 1198488 * 2
def baseEnd_1198488 : Nat := 10130047780177977677173

theorem tailTrace_1198488 : CollatzResearch.WordTrace tailWord_1198488 prefixEnd_1198488 10130047780177977677173 := by
  unfold tailWord_1198488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21856224241045068149834059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29141632321393424199778745 21856224241045068149834059)
  ·
    refine ⟨32784336361567602224751089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21856224241045068149834059 32784336361567602224751089)
    ·
      refine ⟨24588252271175701668563317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32784336361567602224751089 24588252271175701668563317)
      ·
        refine ⟨2305148650422722031427811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24588252271175701668563317 2305148650422722031427811)
        ·
          refine ⟨3457722975634083047141717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305148650422722031427811 3457722975634083047141717)
          ·
            refine ⟨10130047780177977677173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3457722975634083047141717 10130047780177977677173)
            ·
              rfl

theorem cell21_1198488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 10].length) (baseStart_1198488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198488 prefixEnd_1198488 := by exact prefixLift 1198488
  have htrace : WordTrace (prefixWord ++ tailWord_1198488) baseStart_1198488 baseEnd_1198488 := by
    simpa [prefixWord, tailWord_1198488, baseEnd_1198488] using wordTrace_append hprefix tailTrace_1198488
  have hstable : (prefixWord ++ tailWord_1198488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198488).length < 2 ^ (prefixWord ++ tailWord_1198488).sum := by decide
  have hdescent : baseEnd_1198488 < baseStart_1198488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198494 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1198494 : Nat := 118140960795 + 1198494 * 2 ^ 59
def prefixEnd_1198494 : Nat := 4983230072969 + 3 ^ 40 * 1198494 * 2
def baseEnd_1198494 : Nat := 273512659346550720183659

theorem tailTrace_1198494 : CollatzResearch.WordTrace tailWord_1198494 prefixEnd_1198494 273512659346550720183659 := by
  unfold tailWord_1198494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5464083415008549915548317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29141778213378932882924357 5464083415008549915548317)
  ·
    refine ⟨2049031280628206218330619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5464083415008549915548317 2049031280628206218330619)
    ·
      refine ⟨3073546920942309327495929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2049031280628206218330619 3073546920942309327495929)
      ·
        refine ⟨2305160190706731995621947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3073546920942309327495929 2305160190706731995621947)
        ·
          refine ⟨3457740286060097993432921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2305160190706731995621947 3457740286060097993432921)
          ·
            refine ⟨2593305214545073495074691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3457740286060097993432921 2593305214545073495074691)
            ·
              refine ⟨3889957821817610242612037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593305214545073495074691 3889957821817610242612037)
              ·
                refine ⟨729367091590801920489757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3889957821817610242612037 729367091590801920489757)
                ·
                  refine ⟨273512659346550720183659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729367091590801920489757 273512659346550720183659)
                  ·
                    rfl

theorem cell21_1198494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1198494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198494 prefixEnd_1198494 := by exact prefixLift 1198494
  have htrace : WordTrace (prefixWord ++ tailWord_1198494) baseStart_1198494 baseEnd_1198494 := by
    simpa [prefixWord, tailWord_1198494, baseEnd_1198494] using wordTrace_append hprefix tailTrace_1198494
  have hstable : (prefixWord ++ tailWord_1198494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198494).length < 2 ^ (prefixWord ++ tailWord_1198494).sum := by decide
  have hdescent : baseEnd_1198494 < baseStart_1198494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198519 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 5]
def baseStart_1198519 : Nat := 118140960795 + 1198519 * 2 ^ 59
def prefixEnd_1198519 : Nat := 4983230072969 + 3 ^ 40 * 1198519 * 2
def baseEnd_1198519 : Nat := 273518364687156232266941

theorem tailTrace_1198519 : CollatzResearch.WordTrace tailWord_1198519 prefixEnd_1198519 273518364687156232266941 := by
  unfold tailWord_1198519
  simp only [CollatzResearch.WordTrace]
  refine ⟨43713579144977828594046611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29142386096651885729364407 43713579144977828594046611)
  ·
    refine ⟨65570368717466742891069917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43713579144977828594046611 65570368717466742891069917)
    ·
      refine ⟨24588888269050028584151219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65570368717466742891069917 24588888269050028584151219)
      ·
        refine ⟨36883332403575042876226829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24588888269050028584151219 36883332403575042876226829)
        ·
          refine ⟨13831249651340641078585061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36883332403575042876226829 13831249651340641078585061)
          ·
            refine ⟨2593359309626370202234699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13831249651340641078585061 2593359309626370202234699)
            ·
              refine ⟨3890038964439555303352049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2593359309626370202234699 3890038964439555303352049)
              ·
                refine ⟨2917529223329666477514037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3890038964439555303352049 2917529223329666477514037)
                ·
                  refine ⟨273518364687156232266941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2917529223329666477514037 273518364687156232266941)
                  ·
                    rfl

theorem cell21_1198519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 5].length) (baseStart_1198519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198519 prefixEnd_1198519 := by exact prefixLift 1198519
  have htrace : WordTrace (prefixWord ++ tailWord_1198519) baseStart_1198519 baseEnd_1198519 := by
    simpa [prefixWord, tailWord_1198519, baseEnd_1198519] using wordTrace_append hprefix tailTrace_1198519
  have hstable : (prefixWord ++ tailWord_1198519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198519).length < 2 ^ (prefixWord ++ tailWord_1198519).sum := by decide
  have hdescent : baseEnd_1198519 < baseStart_1198519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198536 : List Nat := [2, 1, 3, 1, 3, 2, 1, 5, 3]
def baseStart_1198536 : Nat := 118140960795 + 1198536 * 2 ^ 59
def prefixEnd_1198536 : Nat := 4983230072969 + 3 ^ 40 * 1198536 * 2
def baseEnd_1198536 : Nat := 273522244318767980483573

theorem tailTrace_1198536 : CollatzResearch.WordTrace tailWord_1198536 prefixEnd_1198536 273522244318767980483573 := by
  unfold tailWord_1198536
  simp only [CollatzResearch.WordTrace]
  refine ⟨21857099592958120248707731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29142799457277493664943641 21857099592958120248707731)
  ·
    refine ⟨32785649389437180373061597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21857099592958120248707731 32785649389437180373061597)
    ·
      refine ⟨12294618521038942639898099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32785649389437180373061597 12294618521038942639898099)
      ·
        refine ⟨18441927781558413959847149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12294618521038942639898099 18441927781558413959847149)
        ·
          refine ⟨6915722918084405234942681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18441927781558413959847149 6915722918084405234942681)
          ·
            refine ⟨5186792188563303926207011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6915722918084405234942681 5186792188563303926207011)
            ·
              refine ⟨7780188282844955889310517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5186792188563303926207011 7780188282844955889310517)
              ·
                refine ⟨729392651516714614622861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7780188282844955889310517 729392651516714614622861)
                ·
                  refine ⟨273522244318767980483573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729392651516714614622861 273522244318767980483573)
                  ·
                    rfl

theorem cell21_1198536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 3].length) (baseStart_1198536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198536 prefixEnd_1198536 := by exact prefixLift 1198536
  have htrace : WordTrace (prefixWord ++ tailWord_1198536) baseStart_1198536 baseEnd_1198536 := by
    simpa [prefixWord, tailWord_1198536, baseEnd_1198536] using wordTrace_append hprefix tailTrace_1198536
  have hstable : (prefixWord ++ tailWord_1198536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198536).length < 2 ^ (prefixWord ++ tailWord_1198536).sum := by decide
  have hdescent : baseEnd_1198536 < baseStart_1198536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198567 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 4]
def baseStart_1198567 : Nat := 118140960795 + 1198567 * 2 ^ 59
def prefixEnd_1198567 : Nat := 4983230072969 + 3 ^ 40 * 1198567 * 2
def baseEnd_1198567 : Nat := 273529318941118815466843

theorem tailTrace_1198567 : CollatzResearch.WordTrace tailWord_1198567 prefixEnd_1198567 273529318941118815466843 := by
  unfold tailWord_1198567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43715329848803932791793955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29143553232535955194529303 43715329848803932791793955)
  ·
    refine ⟨65572994773205899187690933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43715329848803932791793955 65572994773205899187690933)
    ·
      refine ⟨6147468259988053048846025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65572994773205899187690933 6147468259988053048846025)
      ·
        refine ⟨4610601194991039786634519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6147468259988053048846025 4610601194991039786634519)
        ·
          refine ⟨6915901792486559679951779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4610601194991039786634519 6915901792486559679951779)
          ·
            refine ⟨10373852688729839519927669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6915901792486559679951779 10373852688729839519927669)
            ·
              refine ⟨972548689568422454993219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10373852688729839519927669 972548689568422454993219)
              ·
                refine ⟨1458823034352633682489829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 972548689568422454993219 1458823034352633682489829)
                ·
                  refine ⟨273529318941118815466843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1458823034352633682489829 273529318941118815466843)
                  ·
                    rfl

theorem cell21_1198567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 4].length) (baseStart_1198567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198567 prefixEnd_1198567 := by exact prefixLift 1198567
  have htrace : WordTrace (prefixWord ++ tailWord_1198567) baseStart_1198567 baseEnd_1198567 := by
    simpa [prefixWord, tailWord_1198567, baseEnd_1198567] using wordTrace_append hprefix tailTrace_1198567
  have hstable : (prefixWord ++ tailWord_1198567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198567).length < 2 ^ (prefixWord ++ tailWord_1198567).sum := by decide
  have hdescent : baseEnd_1198567 < baseStart_1198567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198781 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1198781 : Nat := 118140960795 + 1198781 * 2 ^ 59
def prefixEnd_1198781 : Nat := 4983230072969 + 3 ^ 40 * 1198781 * 2
def baseEnd_1198781 : Nat := 273578156656701998899739

theorem tailTrace_1198781 : CollatzResearch.WordTrace tailWord_1198781 prefixEnd_1198781 273578156656701998899739 := by
  unfold tailWord_1198781
  simp only [CollatzResearch.WordTrace]
  refine ⟨43723135070028647340084197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29148756713352431560056131 43723135070028647340084197)
  ·
    refine ⟨8198087825630371376265787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43723135070028647340084197 8198087825630371376265787)
    ·
      refine ⟨12297131738445557064398681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8198087825630371376265787 12297131738445557064398681)
      ·
        refine ⟨9222848803834167798299011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12297131738445557064398681 9222848803834167798299011)
        ·
          refine ⟨13834273205751251697448517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9222848803834167798299011 13834273205751251697448517)
          ·
            refine ⟨2593926226078359693271597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13834273205751251697448517 2593926226078359693271597)
            ·
              refine ⟨972722334779384884976849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2593926226078359693271597 972722334779384884976849)
              ·
                refine ⟨729541751084538663732637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972722334779384884976849 729541751084538663732637)
                ·
                  refine ⟨273578156656701998899739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729541751084538663732637 273578156656701998899739)
                  ·
                    rfl

theorem cell21_1198781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1198781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198781 prefixEnd_1198781 := by exact prefixLift 1198781
  have htrace : WordTrace (prefixWord ++ tailWord_1198781) baseStart_1198781 baseEnd_1198781 := by
    simpa [prefixWord, tailWord_1198781, baseEnd_1198781] using wordTrace_append hprefix tailTrace_1198781
  have hstable : (prefixWord ++ tailWord_1198781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198781).length < 2 ^ (prefixWord ++ tailWord_1198781).sum := by decide
  have hdescent : baseEnd_1198781 < baseStart_1198781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198792 : List Nat := [2, 1, 3, 1, 2, 4, 2, 6]
def baseStart_1198792 : Nat := 118140960795 + 1198792 * 2 ^ 59
def prefixEnd_1198792 : Nat := 4983230072969 + 3 ^ 40 * 1198792 * 2
def baseEnd_1198792 : Nat := 91193555668856141405461

theorem tailTrace_1198792 : CollatzResearch.WordTrace tailWord_1198792 prefixEnd_1198792 91193555668856141405461 := by
  unfold tailWord_1198792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21861768136494398109367315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29149024181992530812489753 21861768136494398109367315)
  ·
    refine ⟨32792652204741597164050973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21861768136494398109367315 32792652204741597164050973)
    ·
      refine ⟨12297244576778098936519115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32792652204741597164050973 12297244576778098936519115)
      ·
        refine ⟨18445866865167148404778673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12297244576778098936519115 18445866865167148404778673)
        ·
          refine ⟨13834400148875361303584005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18445866865167148404778673 13834400148875361303584005)
          ·
            refine ⟨2593950027914130244422001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13834400148875361303584005 2593950027914130244422001)
            ·
              refine ⟨1945462520935597683316501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2593950027914130244422001 1945462520935597683316501)
              ·
                refine ⟨91193555668856141405461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1945462520935597683316501 91193555668856141405461)
                ·
                  rfl

theorem cell21_1198792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_1198792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198792 prefixEnd_1198792 := by exact prefixLift 1198792
  have htrace : WordTrace (prefixWord ++ tailWord_1198792) baseStart_1198792 baseEnd_1198792 := by
    simpa [prefixWord, tailWord_1198792, baseEnd_1198792] using wordTrace_append hprefix tailTrace_1198792
  have hstable : (prefixWord ++ tailWord_1198792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198792).length < 2 ^ (prefixWord ++ tailWord_1198792).sum := by decide
  have hdescent : baseEnd_1198792 < baseStart_1198792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1198899 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 5]
def baseStart_1198899 : Nat := 118140960795 + 1198899 * 2 ^ 59
def prefixEnd_1198899 : Nat := 4983230072969 + 3 ^ 40 * 1198899 * 2
def baseEnd_1198899 : Nat := 273605085864360015932831

theorem tailTrace_1198899 : CollatzResearch.WordTrace tailWord_1198899 prefixEnd_1198899 273605085864360015932831 := by
  unfold tailWord_1198899
  simp only [CollatzResearch.WordTrace]
  refine ⟨43727438883601153492879751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29151625922400768995253167 43727438883601153492879751)
  ·
    refine ⟨65591158325401730239319627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43727438883601153492879751 65591158325401730239319627)
    ·
      refine ⟨98386737488102595358979441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65591158325401730239319627 98386737488102595358979441)
      ·
        refine ⟨73790053116076946519234581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98386737488102595358979441 73790053116076946519234581)
        ·
          refine ⟨3458908739816106868089121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 73790053116076946519234581 3458908739816106868089121)
          ·
            refine ⟨2594181554862080151066841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3458908739816106868089121 2594181554862080151066841)
            ·
              refine ⟨1945636166146560113300131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2594181554862080151066841 1945636166146560113300131)
              ·
                refine ⟨2918454249219840169950197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1945636166146560113300131 2918454249219840169950197)
                ·
                  refine ⟨273605085864360015932831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918454249219840169950197 273605085864360015932831)
                  ·
                    rfl

theorem cell21_1198899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_1198899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1198899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1198899 prefixEnd_1198899 := by exact prefixLift 1198899
  have htrace : WordTrace (prefixWord ++ tailWord_1198899) baseStart_1198899 baseEnd_1198899 := by
    simpa [prefixWord, tailWord_1198899, baseEnd_1198899] using wordTrace_append hprefix tailTrace_1198899
  have hstable : (prefixWord ++ tailWord_1198899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1198899).length < 2 ^ (prefixWord ++ tailWord_1198899).sum := by decide
  have hdescent : baseEnd_1198899 < baseStart_1198899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1198899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199009 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 3]
def baseStart_1199009 : Nat := 118140960795 + 1199009 * 2 ^ 59
def prefixEnd_1199009 : Nat := 4983230072969 + 3 ^ 40 * 1199009 * 2
def baseEnd_1199009 : Nat := 273630189363024269099273

theorem tailTrace_1199009 : CollatzResearch.WordTrace tailWord_1199009 prefixEnd_1199009 273630189363024269099273 := by
  unfold tailWord_1199009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43731450913202642279384081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29154300608801761519589387 43731450913202642279384081)
  ·
    refine ⟨32798588184901981709538061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43731450913202642279384081 32798588184901981709538061)
    ·
      refine ⟨12299470569338243141076773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32798588184901981709538061 12299470569338243141076773)
      ·
        refine ⟨2306150731750920588951895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12299470569338243141076773 2306150731750920588951895)
        ·
          refine ⟨3459226097626380883427843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306150731750920588951895 3459226097626380883427843)
          ·
            refine ⟨5188839146439571325141765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459226097626380883427843 5188839146439571325141765)
            ·
              refine ⟨972907339957419623464081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5188839146439571325141765 972907339957419623464081)
              ·
                refine ⟨729680504968064717598061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 972907339957419623464081 729680504968064717598061)
                ·
                  refine ⟨273630189363024269099273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729680504968064717598061 273630189363024269099273)
                  ·
                    rfl

theorem cell21_1199009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_1199009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199009 prefixEnd_1199009 := by exact prefixLift 1199009
  have htrace : WordTrace (prefixWord ++ tailWord_1199009) baseStart_1199009 baseEnd_1199009 := by
    simpa [prefixWord, tailWord_1199009, baseEnd_1199009] using wordTrace_append hprefix tailTrace_1199009
  have hstable : (prefixWord ++ tailWord_1199009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199009).length < 2 ^ (prefixWord ++ tailWord_1199009).sum := by decide
  have hdescent : baseEnd_1199009 < baseStart_1199009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199034 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 5]
def baseStart_1199034 : Nat := 118140960795 + 1199034 * 2 ^ 59
def prefixEnd_1199034 : Nat := 4983230072969 + 3 ^ 40 * 1199034 * 2
def baseEnd_1199034 : Nat := 273635894703629781182555

theorem tailTrace_1199034 : CollatzResearch.WordTrace tailWord_1199034 prefixEnd_1199034 273635894703629781182555 := by
  unfold tailWord_1199034
  simp only [CollatzResearch.WordTrace]
  refine ⟨10933090684528017887261039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29154908492074714366029437 10933090684528017887261039)
  ·
    refine ⟨16399636026792026830891559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10933090684528017887261039 16399636026792026830891559)
    ·
      refine ⟨24599454040188040246337339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16399636026792026830891559 24599454040188040246337339)
      ·
        refine ⟨36899181060282060369506009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24599454040188040246337339 36899181060282060369506009)
        ·
          refine ⟨27674385795211545277129507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36899181060282060369506009 27674385795211545277129507)
          ·
            refine ⟨41511578692817317915694261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27674385795211545277129507 41511578692817317915694261)
            ·
              refine ⟨3891710502451623554596337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41511578692817317915694261 3891710502451623554596337)
              ·
                refine ⟨2918782876838717665947253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3891710502451623554596337 2918782876838717665947253)
                ·
                  refine ⟨273635894703629781182555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2918782876838717665947253 273635894703629781182555)
                  ·
                    rfl

theorem cell21_1199034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_1199034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199034 prefixEnd_1199034 := by exact prefixLift 1199034
  have htrace : WordTrace (prefixWord ++ tailWord_1199034) baseStart_1199034 baseEnd_1199034 := by
    simpa [prefixWord, tailWord_1199034, baseEnd_1199034] using wordTrace_append hprefix tailTrace_1199034
  have hstable : (prefixWord ++ tailWord_1199034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199034).length < 2 ^ (prefixWord ++ tailWord_1199034).sum := by decide
  have hdescent : baseEnd_1199034 < baseStart_1199034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199037 : List Nat := [1, 4, 1, 2, 4, 1, 3, 5]
def baseStart_1199037 : Nat := 118140960795 + 1199037 * 2 ^ 59
def prefixEnd_1199037 : Nat := 4983230072969 + 3 ^ 40 * 1199037 * 2
def baseEnd_1199037 : Nat := 91212193114834147544183

theorem tailTrace_1199037 : CollatzResearch.WordTrace tailWord_1199037 prefixEnd_1199037 91212193114834147544183 := by
  unfold tailWord_1199037
  simp only [CollatzResearch.WordTrace]
  refine ⟨43732472157101203061403365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29154981438067468707602243 43732472157101203061403365)
  ·
    refine ⟨8199838529456475574013131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43732472157101203061403365 8199838529456475574013131)
    ·
      refine ⟨12299757794184713361019697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8199838529456475574013131 12299757794184713361019697)
      ·
        refine ⟨9224818345638535020764773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12299757794184713361019697 9224818345638535020764773)
        ·
          refine ⟨1729653439807225316393395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9224818345638535020764773 1729653439807225316393395)
          ·
            refine ⟨2594480159710837974590093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1729653439807225316393395 2594480159710837974590093)
            ·
              refine ⟨972930059891564240471285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2594480159710837974590093 972930059891564240471285)
              ·
                refine ⟨91212193114834147544183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 972930059891564240471285 91212193114834147544183)
                ·
                  rfl

theorem cell21_1199037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 5].length) (baseStart_1199037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199037 prefixEnd_1199037 := by exact prefixLift 1199037
  have htrace : WordTrace (prefixWord ++ tailWord_1199037) baseStart_1199037 baseEnd_1199037 := by
    simpa [prefixWord, tailWord_1199037, baseEnd_1199037] using wordTrace_append hprefix tailTrace_1199037
  have hstable : (prefixWord ++ tailWord_1199037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199037).length < 2 ^ (prefixWord ++ tailWord_1199037).sum := by decide
  have hdescent : baseEnd_1199037 < baseStart_1199037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199051 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 3]
def baseStart_1199051 : Nat := 118140960795 + 1199051 * 2 ^ 59
def prefixEnd_1199051 : Nat := 4983230072969 + 3 ^ 40 * 1199051 * 2
def baseEnd_1199051 : Nat := 273639774335241529399187

theorem tailTrace_1199051 : CollatzResearch.WordTrace tailWord_1199051 prefixEnd_1199051 273639774335241529399187 := by
  unfold tailWord_1199051
  simp only [CollatzResearch.WordTrace]
  refine ⟨43732982779050483452413007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29155321852700322301608671 43732982779050483452413007)
  ·
    refine ⟨65599474168575725178619511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43732982779050483452413007 65599474168575725178619511)
    ·
      refine ⟨98399211252863587767929267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65599474168575725178619511 98399211252863587767929267)
      ·
        refine ⟨147598816879295381651893901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98399211252863587767929267 147598816879295381651893901)
        ·
          refine ⟨55349556329735768119460213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147598816879295381651893901 55349556329735768119460213)
          ·
            refine ⟨5189020905912728261199395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55349556329735768119460213 5189020905912728261199395)
            ·
              refine ⟨7783531358869092391799093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5189020905912728261199395 7783531358869092391799093)
              ·
                refine ⟨729706064893977411731165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7783531358869092391799093 729706064893977411731165)
                ·
                  refine ⟨273639774335241529399187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729706064893977411731165 273639774335241529399187)
                  ·
                    rfl

theorem cell21_1199051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 3].length) (baseStart_1199051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199051 prefixEnd_1199051 := by exact prefixLift 1199051
  have htrace : WordTrace (prefixWord ++ tailWord_1199051) baseStart_1199051 baseEnd_1199051 := by
    simpa [prefixWord, tailWord_1199051, baseEnd_1199051] using wordTrace_append hprefix tailTrace_1199051
  have hstable : (prefixWord ++ tailWord_1199051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199051).length < 2 ^ (prefixWord ++ tailWord_1199051).sum := by decide
  have hdescent : baseEnd_1199051 < baseStart_1199051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199065 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_1199065 : Nat := 118140960795 + 1199065 * 2 ^ 59
def prefixEnd_1199065 : Nat := 4983230072969 + 3 ^ 40 * 1199065 * 2
def baseEnd_1199065 : Nat := 273642969325980616165825

theorem tailTrace_1199065 : CollatzResearch.WordTrace tailWord_1199065 prefixEnd_1199065 273642969325980616165825 := by
  unfold tailWord_1199065
  simp only [CollatzResearch.WordTrace]
  refine ⟨43733493400999763843422649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29155662267333175895615099 43733493400999763843422649)
  ·
    refine ⟨32800120050749822882566987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43733493400999763843422649 32800120050749822882566987)
    ·
      refine ⟨49200180076124734323850481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32800120050749822882566987 49200180076124734323850481)
      ·
        refine ⟨36900135057093550742887861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49200180076124734323850481 36900135057093550742887861)
        ·
          refine ⟨3459387661602520382145737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36900135057093550742887861 3459387661602520382145737)
          ·
            refine ⟨2594540746201890286609303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3459387661602520382145737 2594540746201890286609303)
            ·
              refine ⟨3891811119302835429913955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2594540746201890286609303 3891811119302835429913955)
              ·
                refine ⟨5837716678954253144870933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3891811119302835429913955 5837716678954253144870933)
                ·
                  refine ⟨273642969325980616165825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5837716678954253144870933 273642969325980616165825)
                  ·
                    rfl

theorem cell21_1199065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_1199065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199065 prefixEnd_1199065 := by exact prefixLift 1199065
  have htrace : WordTrace (prefixWord ++ tailWord_1199065) baseStart_1199065 baseEnd_1199065 := by
    simpa [prefixWord, tailWord_1199065, baseEnd_1199065] using wordTrace_append hprefix tailTrace_1199065
  have hstable : (prefixWord ++ tailWord_1199065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199065).length < 2 ^ (prefixWord ++ tailWord_1199065).sum := by decide
  have hdescent : baseEnd_1199065 < baseStart_1199065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199102 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_1199102 : Nat := 118140960795 + 1199102 * 2 ^ 59
def prefixEnd_1199102 : Nat := 4983230072969 + 3 ^ 40 * 1199102 * 2
def baseEnd_1199102 : Nat := 273651413230076774049083

theorem tailTrace_1199102 : CollatzResearch.WordTrace tailWord_1199102 prefixEnd_1199102 273651413230076774049083 := by
  unfold tailWord_1199102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466855362733214895314945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29156561934577146108346373 5466855362733214895314945)
  ·
    refine ⟨4100141522049911171486209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5466855362733214895314945 4100141522049911171486209)
    ·
      refine ⟨3075106141537433378614657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4100141522049911171486209 3075106141537433378614657)
      ·
        refine ⟨2306329606153075033960993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3075106141537433378614657 2306329606153075033960993)
        ·
          refine ⟨1729747204614806275470745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2306329606153075033960993 1729747204614806275470745)
          ·
            refine ⟨1297310403461104706603059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1729747204614806275470745 1297310403461104706603059)
            ·
              refine ⟨1945965605191657059904589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297310403461104706603059 1945965605191657059904589)
              ·
                refine ⟨729737101946871397464221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1945965605191657059904589 729737101946871397464221)
                ·
                  refine ⟨273651413230076774049083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729737101946871397464221 273651413230076774049083)
                  ·
                    rfl

theorem cell21_1199102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_1199102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199102 prefixEnd_1199102 := by exact prefixLift 1199102
  have htrace : WordTrace (prefixWord ++ tailWord_1199102) baseStart_1199102 baseEnd_1199102 := by
    simpa [prefixWord, tailWord_1199102, baseEnd_1199102] using wordTrace_append hprefix tailTrace_1199102
  have hstable : (prefixWord ++ tailWord_1199102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199102).length < 2 ^ (prefixWord ++ tailWord_1199102).sum := by decide
  have hdescent : baseEnd_1199102 < baseStart_1199102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199127 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 5]
def baseStart_1199127 : Nat := 118140960795 + 1199127 * 2 ^ 59
def prefixEnd_1199127 : Nat := 4983230072969 + 3 ^ 40 * 1199127 * 2
def baseEnd_1199127 : Nat := 273657118570682286132365

theorem tailTrace_1199127 : CollatzResearch.WordTrace tailWord_1199127 prefixEnd_1199127 273657118570682286132365 := by
  unfold tailWord_1199127
  simp only [CollatzResearch.WordTrace]
  refine ⟨43735754726775148432179635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29157169817850098954786423 43735754726775148432179635)
  ·
    refine ⟨65603632090162722648269453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43735754726775148432179635 65603632090162722648269453)
    ·
      refine ⟨24601362033811020993101045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65603632090162722648269453 24601362033811020993101045)
      ·
        refine ⟨2306377690669783218103223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24601362033811020993101045 2306377690669783218103223)
        ·
          refine ⟨3459566536004674827154835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2306377690669783218103223 3459566536004674827154835)
          ·
            refine ⟨5189349804007012240732253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3459566536004674827154835 5189349804007012240732253)
            ·
              refine ⟨1946006176502629590274595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5189349804007012240732253 1946006176502629590274595)
              ·
                refine ⟨2919009264753944385411893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946006176502629590274595 2919009264753944385411893)
                ·
                  refine ⟨273657118570682286132365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2919009264753944385411893 273657118570682286132365)
                  ·
                    rfl

theorem cell21_1199127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_1199127 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199127 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199127 prefixEnd_1199127 := by exact prefixLift 1199127
  have htrace : WordTrace (prefixWord ++ tailWord_1199127) baseStart_1199127 baseEnd_1199127 := by
    simpa [prefixWord, tailWord_1199127, baseEnd_1199127] using wordTrace_append hprefix tailTrace_1199127
  have hstable : (prefixWord ++ tailWord_1199127).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199127).length < 2 ^ (prefixWord ++ tailWord_1199127).sum := by decide
  have hdescent : baseEnd_1199127 < baseStart_1199127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199141 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1199141 : Nat := 118140960795 + 1199141 * 2 ^ 59
def prefixEnd_1199141 : Nat := 4983230072969 + 3 ^ 40 * 1199141 * 2
def baseEnd_1199141 : Nat := 273660313561421372899003

theorem tailTrace_1199141 : CollatzResearch.WordTrace tailWord_1199141 prefixEnd_1199141 273660313561421372899003 := by
  unfold tailWord_1199141
  simp only [CollatzResearch.WordTrace]
  refine ⟨43736265348724428823189277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29157510232482952548792851 43736265348724428823189277)
  ·
    refine ⟨16401099505771660808695979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43736265348724428823189277 16401099505771660808695979)
    ·
      refine ⟨24601649258657491213043969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16401099505771660808695979 24601649258657491213043969)
      ·
        refine ⟨18451236943993118409782977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24601649258657491213043969 18451236943993118409782977)
        ·
          refine ⟨13838427707994838807337233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18451236943993118409782977 13838427707994838807337233)
          ·
            refine ⟨10378820780996129105502925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13838427707994838807337233 10378820780996129105502925)
            ·
              refine ⟨3892057792873548414563597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10378820780996129105502925 3892057792873548414563597)
              ·
                refine ⟨1459521672327580655461349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3892057792873548414563597 1459521672327580655461349)
                ·
                  refine ⟨273660313561421372899003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459521672327580655461349 273660313561421372899003)
                  ·
                    rfl

theorem cell21_1199141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1199141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199141 prefixEnd_1199141 := by exact prefixLift 1199141
  have htrace : WordTrace (prefixWord ++ tailWord_1199141) baseStart_1199141 baseEnd_1199141 := by
    simpa [prefixWord, tailWord_1199141, baseEnd_1199141] using wordTrace_append hprefix tailTrace_1199141
  have hstable : (prefixWord ++ tailWord_1199141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199141).length < 2 ^ (prefixWord ++ tailWord_1199141).sum := by decide
  have hdescent : baseEnd_1199141 < baseStart_1199141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199279 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 3]
def baseStart_1199279 : Nat := 118140960795 + 1199279 * 2 ^ 59
def prefixEnd_1199279 : Nat := 4983230072969 + 3 ^ 40 * 1199279 * 2
def baseEnd_1199279 : Nat := 273691807041563799598721

theorem tailTrace_1199279 : CollatzResearch.WordTrace tailWord_1199279 prefixEnd_1199279 273691807041563799598721 := by
  unfold tailWord_1199279
  simp only [CollatzResearch.WordTrace]
  refine ⟨43741298622224478391712891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29160865748149652261141927 43741298622224478391712891)
  ·
    refine ⟨65611947933336717587569337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43741298622224478391712891 65611947933336717587569337)
    ·
      refine ⟨49208960950002538190677003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65611947933336717587569337 49208960950002538190677003)
      ·
        refine ⟨73813441425003807286015505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49208960950002538190677003 73813441425003807286015505)
        ·
          refine ⟨55360081068752855464511629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73813441425003807286015505 55360081068752855464511629)
          ·
            refine ⟨20760030400782320799191861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55360081068752855464511629 20760030400782320799191861)
            ·
              refine ⟨1946252850073342574924237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20760030400782320799191861 1946252850073342574924237)
              ·
                refine ⟨729844818777503465596589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1946252850073342574924237 729844818777503465596589)
                ·
                  refine ⟨273691807041563799598721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 729844818777503465596589 273691807041563799598721)
                  ·
                    rfl

theorem cell21_1199279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 3].length) (baseStart_1199279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199279 prefixEnd_1199279 := by exact prefixLift 1199279
  have htrace : WordTrace (prefixWord ++ tailWord_1199279) baseStart_1199279 baseEnd_1199279 := by
    simpa [prefixWord, tailWord_1199279, baseEnd_1199279] using wordTrace_append hprefix tailTrace_1199279
  have hstable : (prefixWord ++ tailWord_1199279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199279).length < 2 ^ (prefixWord ++ tailWord_1199279).sum := by decide
  have hdescent : baseEnd_1199279 < baseStart_1199279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199296 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_1199296 : Nat := 118140960795 + 1199296 * 2 ^ 59
def prefixEnd_1199296 : Nat := 4983230072969 + 3 ^ 40 * 1199296 * 2
def baseEnd_1199296 : Nat := 273695686673175547815353

theorem tailTrace_1199296 : CollatzResearch.WordTrace tailWord_1199296 prefixEnd_1199296 273695686673175547815353 := by
  unfold tailWord_1199296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21870959331581445147540871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29161279108775260196721161 21870959331581445147540871)
  ·
    refine ⟨32806438997372167721311307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21870959331581445147540871 32806438997372167721311307)
    ·
      refine ⟨49209658496058251581966961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32806438997372167721311307 49209658496058251581966961)
      ·
        refine ⟨36907243872043688686475221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49209658496058251581966961 36907243872043688686475221)
        ·
          refine ⟨865013528251023953589263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36907243872043688686475221 865013528251023953589263)
          ·
            refine ⟨1297520292376535930383895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865013528251023953589263 1297520292376535930383895)
            ·
              refine ⟨1946280438564803895575843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297520292376535930383895 1946280438564803895575843)
              ·
                refine ⟨2919420657847205843363765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1946280438564803895575843 2919420657847205843363765)
                ·
                  refine ⟨273695686673175547815353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2919420657847205843363765 273695686673175547815353)
                  ·
                    rfl

theorem cell21_1199296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_1199296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199296 prefixEnd_1199296 := by exact prefixLift 1199296
  have htrace : WordTrace (prefixWord ++ tailWord_1199296) baseStart_1199296 baseEnd_1199296 := by
    simpa [prefixWord, tailWord_1199296, baseEnd_1199296] using wordTrace_append hprefix tailTrace_1199296
  have hstable : (prefixWord ++ tailWord_1199296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199296).length < 2 ^ (prefixWord ++ tailWord_1199296).sum := by decide
  have hdescent : baseEnd_1199296 < baseStart_1199296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199302 : List Nat := [6, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_1199302 : Nat := 118140960795 + 1199302 * 2 ^ 59
def prefixEnd_1199302 : Nat := 4983230072969 + 3 ^ 40 * 1199302 * 2
def baseEnd_1199302 : Nat := 273697055954920870715341

theorem tailTrace_1199302 : CollatzResearch.WordTrace tailWord_1199302 prefixEnd_1199302 273697055954920870715341 := by
  unfold tailWord_1199302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366941796910661041243755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29161425000760768879866773 1366941796910661041243755)
  ·
    refine ⟨2050412695365991561865633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1366941796910661041243755 2050412695365991561865633)
    ·
      refine ⟨1537809521524493671399225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2050412695365991561865633 1537809521524493671399225)
      ·
        refine ⟨1153357141143370253549419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537809521524493671399225 1153357141143370253549419)
        ·
          refine ⟨1730035711715055380324129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153357141143370253549419 1730035711715055380324129)
          ·
            refine ⟨1297526783786291535243097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1730035711715055380324129 1297526783786291535243097)
            ·
              refine ⟨973145087839718651432323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297526783786291535243097 973145087839718651432323)
              ·
                refine ⟨1459717631759577977148485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973145087839718651432323 1459717631759577977148485)
                ·
                  refine ⟨273697055954920870715341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459717631759577977148485 273697055954920870715341)
                  ·
                    rfl

theorem cell21_1199302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_1199302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199302 prefixEnd_1199302 := by exact prefixLift 1199302
  have htrace : WordTrace (prefixWord ++ tailWord_1199302) baseStart_1199302 baseEnd_1199302 := by
    simpa [prefixWord, tailWord_1199302, baseEnd_1199302] using wordTrace_append hprefix tailTrace_1199302
  have hstable : (prefixWord ++ tailWord_1199302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199302).length < 2 ^ (prefixWord ++ tailWord_1199302).sum := by decide
  have hdescent : baseEnd_1199302 < baseStart_1199302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199310 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1199310 : Nat := 118140960795 + 1199310 * 2 ^ 59
def prefixEnd_1199310 : Nat := 4983230072969 + 3 ^ 40 * 1199310 * 2
def baseEnd_1199310 : Nat := 273698881663914634581991

theorem tailTrace_1199310 : CollatzResearch.WordTrace tailWord_1199310 prefixEnd_1199310 273698881663914634581991 := by
  unfold tailWord_1199310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5467803660639021335761423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29161619523408113790727589 5467803660639021335761423)
  ·
    refine ⟨8201705490958532003642135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5467803660639021335761423 8201705490958532003642135)
    ·
      refine ⟨12302558236437798005463203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8201705490958532003642135 12302558236437798005463203)
      ·
        refine ⟨18453837354656697008194805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12302558236437798005463203 18453837354656697008194805)
        ·
          refine ⟨1730047251999065344518263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18453837354656697008194805 1730047251999065344518263)
          ·
            refine ⟨2595070877998598016777395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730047251999065344518263 2595070877998598016777395)
            ·
              refine ⟨3892606316997897025166093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2595070877998598016777395 3892606316997897025166093)
              ·
                refine ⟨1459727368874211384437285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3892606316997897025166093 1459727368874211384437285)
                ·
                  refine ⟨273698881663914634581991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1459727368874211384437285 273698881663914634581991)
                  ·
                    rfl

theorem cell21_1199310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1199310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199310 prefixEnd_1199310 := by exact prefixLift 1199310
  have htrace : WordTrace (prefixWord ++ tailWord_1199310) baseStart_1199310 baseEnd_1199310 := by
    simpa [prefixWord, tailWord_1199310, baseEnd_1199310] using wordTrace_append hprefix tailTrace_1199310
  have hstable : (prefixWord ++ tailWord_1199310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199310).length < 2 ^ (prefixWord ++ tailWord_1199310).sum := by decide
  have hdescent : baseEnd_1199310 < baseStart_1199310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199321 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 7]
def baseStart_1199321 : Nat := 118140960795 + 1199321 * 2 ^ 59
def prefixEnd_1199321 : Nat := 4983230072969 + 3 ^ 40 * 1199321 * 2
def baseEnd_1199321 : Nat := 273701392013781059898635

theorem tailTrace_1199321 : CollatzResearch.WordTrace tailWord_1199321 prefixEnd_1199321 273701392013781059898635 := by
  unfold tailWord_1199321
  simp only [CollatzResearch.WordTrace]
  refine ⟨43742830488072319564741817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29161886992048213043161211 43742830488072319564741817)
  ·
    refine ⟨32807122866054239673556363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43742830488072319564741817 32807122866054239673556363)
    ·
      refine ⟨49210684299081359510334545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32807122866054239673556363 49210684299081359510334545)
      ·
        refine ⟨36908013224311019632750909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49210684299081359510334545 36908013224311019632750909)
        ·
          refine ⟨13840504959116632362281591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36908013224311019632750909 13840504959116632362281591)
          ·
            refine ⟨20760757438674948543422387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13840504959116632362281591 20760757438674948543422387)
            ·
              refine ⟨31141136158012422815133581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20760757438674948543422387 31141136158012422815133581)
              ·
                refine ⟨11677926059254658555675093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31141136158012422815133581 11677926059254658555675093)
                ·
                  refine ⟨273701392013781059898635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11677926059254658555675093 273701392013781059898635)
                  ·
                    rfl

theorem cell21_1199321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_1199321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199321 prefixEnd_1199321 := by exact prefixLift 1199321
  have htrace : WordTrace (prefixWord ++ tailWord_1199321) baseStart_1199321 baseEnd_1199321 := by
    simpa [prefixWord, tailWord_1199321, baseEnd_1199321] using wordTrace_append hprefix tailTrace_1199321
  have hstable : (prefixWord ++ tailWord_1199321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199321).length < 2 ^ (prefixWord ++ tailWord_1199321).sum := by decide
  have hdescent : baseEnd_1199321 < baseStart_1199321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199459 : List Nat := [1, 1, 1, 5, 2, 4, 7]
def baseStart_1199459 : Nat := 118140960795 + 1199459 * 2 ^ 59
def prefixEnd_1199459 : Nat := 4983230072969 + 3 ^ 40 * 1199459 * 2
def baseEnd_1199459 : Nat := 30414765054880387399817

theorem tailTrace_1199459 : CollatzResearch.WordTrace tailWord_1199459 prefixEnd_1199459 30414765054880387399817 := by
  unfold tailWord_1199459
  simp only [CollatzResearch.WordTrace]
  refine ⟨43747863761572369133265431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29165242507714912755510287 43747863761572369133265431)
  ·
    refine ⟨65621795642358553699898147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43747863761572369133265431 65621795642358553699898147)
    ·
      refine ⟨98432693463537830549847221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65621795642358553699898147 98432693463537830549847221)
      ·
        refine ⟨9228065012206671614048177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98432693463537830549847221 9228065012206671614048177)
        ·
          refine ⟨6921048759155003710536133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9228065012206671614048177 6921048759155003710536133)
          ·
            refine ⟨1297696642341563195725525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6921048759155003710536133 1297696642341563195725525)
            ·
              refine ⟨30414765054880387399817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1297696642341563195725525 30414765054880387399817)
              ·
                rfl

theorem cell21_1199459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 7].length) (baseStart_1199459 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199459 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199459 prefixEnd_1199459 := by exact prefixLift 1199459
  have htrace : WordTrace (prefixWord ++ tailWord_1199459) baseStart_1199459 baseEnd_1199459 := by
    simpa [prefixWord, tailWord_1199459, baseEnd_1199459] using wordTrace_append hprefix tailTrace_1199459
  have hstable : (prefixWord ++ tailWord_1199459).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199459).length < 2 ^ (prefixWord ++ tailWord_1199459).sum := by decide
  have hdescent : baseEnd_1199459 < baseStart_1199459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199617 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 3]
def baseStart_1199617 : Nat := 118140960795 + 1199617 * 2 ^ 59
def prefixEnd_1199617 : Nat := 4983230072969 + 3 ^ 40 * 1199617 * 2
def baseEnd_1199617 : Nat := 273768943246550322964697

theorem tailTrace_1199617 : CollatzResearch.WordTrace tailWord_1199617 prefixEnd_1199617 273768943246550322964697 := by
  unfold tailWord_1199617
  simp only [CollatzResearch.WordTrace]
  refine ⟨43753626494999962117517105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29169084329999974745011403 43753626494999962117517105)
  ·
    refine ⟨32815219871249971588137829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43753626494999962117517105 32815219871249971588137829)
    ·
      refine ⟨6152853725859369672775843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32815219871249971588137829 6152853725859369672775843)
      ·
        refine ⟨9229280588789054509163765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6152853725859369672775843 9229280588789054509163765)
        ·
          refine ⟨865245055198973860234103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9229280588789054509163765 865245055198973860234103)
          ·
            refine ⟨1297867582798460790351155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865245055198973860234103 1297867582798460790351155)
            ·
              refine ⟨1946801374197691185526733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1297867582798460790351155 1946801374197691185526733)
              ·
                refine ⟨730050515324134194572525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1946801374197691185526733 730050515324134194572525)
                ·
                  refine ⟨273768943246550322964697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730050515324134194572525 273768943246550322964697)
                  ·
                    rfl

theorem cell21_1199617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_1199617 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199617 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199617 prefixEnd_1199617 := by exact prefixLift 1199617
  have htrace : WordTrace (prefixWord ++ tailWord_1199617) baseStart_1199617 baseEnd_1199617 := by
    simpa [prefixWord, tailWord_1199617, baseEnd_1199617] using wordTrace_append hprefix tailTrace_1199617
  have hstable : (prefixWord ++ tailWord_1199617).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199617).length < 2 ^ (prefixWord ++ tailWord_1199617).sum := by decide
  have hdescent : baseEnd_1199617 < baseStart_1199617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199628 : List Nat := [2, 2, 1, 2, 6, 1, 7]
def baseStart_1199628 : Nat := 118140960795 + 1199628 * 2 ^ 59
def prefixEnd_1199628 : Nat := 4983230072969 + 3 ^ 40 * 1199628 * 2
def baseEnd_1199628 : Nat := 30419050399601860920149

theorem tailTrace_1199628 : CollatzResearch.WordTrace tailWord_1199628 prefixEnd_1199628 30419050399601860920149 := by
  unfold tailWord_1199628
  simp only [CollatzResearch.WordTrace]
  refine ⟨21877013848980055498083769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29169351798640073997445025 21877013848980055498083769)
  ·
    refine ⟨16407760386735041623562827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21877013848980055498083769 16407760386735041623562827)
    ·
      refine ⟨24611640580102562435344241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16407760386735041623562827 24611640580102562435344241)
      ·
        refine ⟨18458730435076921826508181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24611640580102562435344241 18458730435076921826508181)
        ·
          refine ⟨865252989144230710617571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18458730435076921826508181 865252989144230710617571)
          ·
            refine ⟨1297879483716346065926357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865252989144230710617571 1297879483716346065926357)
            ·
              refine ⟨30419050399601860920149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1297879483716346065926357 30419050399601860920149)
              ·
                rfl

theorem cell21_1199628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 7].length) (baseStart_1199628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199628 prefixEnd_1199628 := by exact prefixLift 1199628
  have htrace : WordTrace (prefixWord ++ tailWord_1199628) baseStart_1199628 baseEnd_1199628 := by
    simpa [prefixWord, tailWord_1199628, baseEnd_1199628] using wordTrace_append hprefix tailTrace_1199628
  have hstable : (prefixWord ++ tailWord_1199628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199628).length < 2 ^ (prefixWord ++ tailWord_1199628).sum := by decide
  have hdescent : baseEnd_1199628 < baseStart_1199628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199687 : List Nat := [1, 1, 4, 1, 6, 8]
def baseStart_1199687 : Nat := 118140960795 + 1199687 * 2 ^ 59
def prefixEnd_1199687 : Nat := 4983230072969 + 3 ^ 40 * 1199687 * 2
def baseEnd_1199687 : Nat := 10140182155564657659181

theorem tailTrace_1199687 : CollatzResearch.WordTrace tailWord_1199687 prefixEnd_1199687 10140182155564657659181 := by
  unfold tailWord_1199687
  simp only [CollatzResearch.WordTrace]
  refine ⟨43756179604746364072565315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29170786403164242715043543 43756179604746364072565315)
  ·
    refine ⟨65634269407119546108847973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43756179604746364072565315 65634269407119546108847973)
    ·
      refine ⟨12306425513834914895408995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65634269407119546108847973 12306425513834914895408995)
      ·
        refine ⟨18459638270752372343113493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12306425513834914895408995 18459638270752372343113493)
        ·
          refine ⟨865295543941517453583445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18459638270752372343113493 865295543941517453583445)
          ·
            refine ⟨10140182155564657659181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 865295543941517453583445 10140182155564657659181)
            ·
              rfl

theorem cell21_1199687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 8].length) (baseStart_1199687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199687 prefixEnd_1199687 := by exact prefixLift 1199687
  have htrace : WordTrace (prefixWord ++ tailWord_1199687) baseStart_1199687 baseEnd_1199687 := by
    simpa [prefixWord, tailWord_1199687, baseEnd_1199687] using wordTrace_append hprefix tailTrace_1199687
  have hstable : (prefixWord ++ tailWord_1199687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199687).length < 2 ^ (prefixWord ++ tailWord_1199687).sum := by decide
  have hdescent : baseEnd_1199687 < baseStart_1199687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199701 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1199701 : Nat := 118140960795 + 1199701 * 2 ^ 59
def prefixEnd_1199701 : Nat := 4983230072969 + 3 ^ 40 * 1199701 * 2
def baseEnd_1199701 : Nat := 273788113190984843564525

theorem tailTrace_1199701 : CollatzResearch.WordTrace tailWord_1199701 prefixEnd_1199701 273788113190984843564525 := by
  unfold tailWord_1199701
  simp only [CollatzResearch.WordTrace]
  refine ⟨43756690226695644463574957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29171126817797096309049971 43756690226695644463574957)
  ·
    refine ⟨16408758835010866673840609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43756690226695644463574957 16408758835010866673840609)
    ·
      refine ⟨12306569126258150005380457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16408758835010866673840609 12306569126258150005380457)
      ·
        refine ⟨9229926844693612504035343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12306569126258150005380457 9229926844693612504035343)
        ·
          refine ⟨13844890267040418756053015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9229926844693612504035343 13844890267040418756053015)
          ·
            refine ⟨20767335400560628134079523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13844890267040418756053015 20767335400560628134079523)
            ·
              refine ⟨31151003100840942201119285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20767335400560628134079523 31151003100840942201119285)
              ·
                refine ⟨2920406540703838331354933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31151003100840942201119285 2920406540703838331354933)
                ·
                  refine ⟨273788113190984843564525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2920406540703838331354933 273788113190984843564525)
                  ·
                    rfl

theorem cell21_1199701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1199701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199701 prefixEnd_1199701 := by exact prefixLift 1199701
  have htrace : WordTrace (prefixWord ++ tailWord_1199701) baseStart_1199701 baseEnd_1199701 := by
    simpa [prefixWord, tailWord_1199701, baseEnd_1199701] using wordTrace_append hprefix tailTrace_1199701
  have hstable : (prefixWord ++ tailWord_1199701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199701).length < 2 ^ (prefixWord ++ tailWord_1199701).sum := by decide
  have hdescent : baseEnd_1199701 < baseStart_1199701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199780 : List Nat := [2, 3, 1, 2, 2, 4, 2, 5]
def baseStart_1199780 : Nat := 118140960795 + 1199780 * 2 ^ 59
def prefixEnd_1199780 : Nat := 4983230072969 + 3 ^ 40 * 1199780 * 2
def baseEnd_1199780 : Nat := 91268714022432753915899

theorem tailTrace_1199780 : CollatzResearch.WordTrace tailWord_1199780 prefixEnd_1199780 91268714022432753915899 := by
  unfold tailWord_1199780
  simp only [CollatzResearch.WordTrace]
  refine ⟨21879785796704720477850397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29173047728939627303800529 21879785796704720477850397)
  ·
    refine ⟨8204919673764270179193899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21879785796704720477850397 8204919673764270179193899)
    ·
      refine ⟨12307379510646405268790849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8204919673764270179193899 12307379510646405268790849)
      ·
        refine ⟨9230534632984803951593137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12307379510646405268790849 9230534632984803951593137)
        ·
          refine ⟨6922900974738602963694853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9230534632984803951593137 6922900974738602963694853)
          ·
            refine ⟨1298043932763488055692785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6922900974738602963694853 1298043932763488055692785)
            ·
              refine ⟨973532949572616041769589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298043932763488055692785 973532949572616041769589)
              ·
                refine ⟨91268714022432753915899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973532949572616041769589 91268714022432753915899)
                ·
                  rfl

theorem cell21_1199780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 5].length) (baseStart_1199780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199780 prefixEnd_1199780 := by exact prefixLift 1199780
  have htrace : WordTrace (prefixWord ++ tailWord_1199780) baseStart_1199780 baseEnd_1199780 := by
    simpa [prefixWord, tailWord_1199780, baseEnd_1199780] using wordTrace_append hprefix tailTrace_1199780
  have hstable : (prefixWord ++ tailWord_1199780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199780).length < 2 ^ (prefixWord ++ tailWord_1199780).sum := by decide
  have hdescent : baseEnd_1199780 < baseStart_1199780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199791 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 8]
def baseStart_1199791 : Nat := 118140960795 + 1199791 * 2 ^ 59
def prefixEnd_1199791 : Nat := 4983230072969 + 3 ^ 40 * 1199791 * 2
def baseEnd_1199791 : Nat := 273808652417164687064341

theorem tailTrace_1199791 : CollatzResearch.WordTrace tailWord_1199791 prefixEnd_1199791 273808652417164687064341 := by
  unfold tailWord_1199791
  simp only [CollatzResearch.WordTrace]
  refine ⟨43759972796369589834351227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29173315197579726556234151 43759972796369589834351227)
  ·
    refine ⟨65639959194554384751526841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43759972796369589834351227 65639959194554384751526841)
    ·
      refine ⟨49229969395915788563645131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65639959194554384751526841 49229969395915788563645131)
      ·
        refine ⟨73844954093873682845467697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49229969395915788563645131 73844954093873682845467697)
        ·
          refine ⟨55383715570405262134100773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73844954093873682845467697 55383715570405262134100773)
          ·
            refine ⟨10384446669450986650143895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55383715570405262134100773 10384446669450986650143895)
            ·
              refine ⟨15576670004176479975215843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10384446669450986650143895 15576670004176479975215843)
              ·
                refine ⟨23365005006264719962823765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15576670004176479975215843 23365005006264719962823765)
                ·
                  refine ⟨273808652417164687064341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23365005006264719962823765 273808652417164687064341)
                  ·
                    rfl

theorem cell21_1199791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_1199791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199791 prefixEnd_1199791 := by exact prefixLift 1199791
  have htrace : WordTrace (prefixWord ++ tailWord_1199791) baseStart_1199791 baseEnd_1199791 := by
    simpa [prefixWord, tailWord_1199791, baseEnd_1199791] using wordTrace_append hprefix tailTrace_1199791
  have hstable : (prefixWord ++ tailWord_1199791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199791).length < 2 ^ (prefixWord ++ tailWord_1199791).sum := by decide
  have hdescent : baseEnd_1199791 < baseStart_1199791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199808 : List Nat := [2, 1, 1, 2, 4, 1, 2, 4, 4]
def baseStart_1199808 : Nat := 118140960795 + 1199808 * 2 ^ 59
def prefixEnd_1199808 : Nat := 4983230072969 + 3 ^ 40 * 1199808 * 2
def baseEnd_1199808 : Nat := 273812532048776435280973

theorem tailTrace_1199808 : CollatzResearch.WordTrace tailWord_1199808 prefixEnd_1199808 273812532048776435280973 := by
  unfold tailWord_1199808
  simp only [CollatzResearch.WordTrace]
  refine ⟨21880296418654000868860039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29173728558205334491813385 21880296418654000868860039)
  ·
    refine ⟨32820444627981001303290059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21880296418654000868860039 32820444627981001303290059)
    ·
      refine ⟨49230666941971501954935089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32820444627981001303290059 49230666941971501954935089)
      ·
        refine ⟨36923000206478626466201317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49230666941971501954935089 36923000206478626466201317)
        ·
          refine ⟨6923062538714742462412747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36923000206478626466201317 6923062538714742462412747)
          ·
            refine ⟨10384593808072113693619121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6923062538714742462412747 10384593808072113693619121)
            ·
              refine ⟨7788445356054085270214341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10384593808072113693619121 7788445356054085270214341)
              ·
                refine ⟨1460333504260140988165189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7788445356054085270214341 1460333504260140988165189)
                ·
                  refine ⟨273812532048776435280973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460333504260140988165189 273812532048776435280973)
                  ·
                    rfl

theorem cell21_1199808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 4, 4].length) (baseStart_1199808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199808 prefixEnd_1199808 := by exact prefixLift 1199808
  have htrace : WordTrace (prefixWord ++ tailWord_1199808) baseStart_1199808 baseEnd_1199808 := by
    simpa [prefixWord, tailWord_1199808, baseEnd_1199808] using wordTrace_append hprefix tailTrace_1199808
  have hstable : (prefixWord ++ tailWord_1199808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199808).length < 2 ^ (prefixWord ++ tailWord_1199808).sum := by decide
  have hdescent : baseEnd_1199808 < baseStart_1199808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199825 : List Nat := [1, 2, 2, 1, 2, 4, 4, 1, 4]
def baseStart_1199825 : Nat := 118140960795 + 1199825 * 2 ^ 59
def prefixEnd_1199825 : Nat := 4983230072969 + 3 ^ 40 * 1199825 * 2
def baseEnd_1199825 : Nat := 273816411680388183497605

theorem tailTrace_1199825 : CollatzResearch.WordTrace tailWord_1199825 prefixEnd_1199825 273816411680388183497605 := by
  unfold tailWord_1199825
  simp only [CollatzResearch.WordTrace]
  refine ⟨43761212878246413641088929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29174141918830942427392619 43761212878246413641088929)
  ·
    refine ⟨32820909658684810230816697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43761212878246413641088929 32820909658684810230816697)
    ·
      refine ⟨24615682244013607673112523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32820909658684810230816697 24615682244013607673112523)
      ·
        refine ⟨36923523366020411509668785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24615682244013607673112523 36923523366020411509668785)
        ·
          refine ⟨27692642524515308632251589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36923523366020411509668785 27692642524515308632251589)
          ·
            refine ⟨5192370473346620368547173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27692642524515308632251589 5192370473346620368547173)
            ·
              refine ⟨973569463752491319102595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5192370473346620368547173 973569463752491319102595)
              ·
                refine ⟨1460354195628736978653893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 973569463752491319102595 1460354195628736978653893)
                ·
                  refine ⟨273816411680388183497605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460354195628736978653893 273816411680388183497605)
                  ·
                    rfl

theorem cell21_1199825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_1199825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199825 prefixEnd_1199825 := by exact prefixLift 1199825
  have htrace : WordTrace (prefixWord ++ tailWord_1199825) baseStart_1199825 baseEnd_1199825 := by
    simpa [prefixWord, tailWord_1199825, baseEnd_1199825] using wordTrace_append hprefix tailTrace_1199825
  have hstable : (prefixWord ++ tailWord_1199825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199825).length < 2 ^ (prefixWord ++ tailWord_1199825).sum := by decide
  have hdescent : baseEnd_1199825 < baseStart_1199825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199884 : List Nat := [2, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1199884 : Nat := 118140960795 + 1199884 * 2 ^ 59
def prefixEnd_1199884 : Nat := 4983230072969 + 3 ^ 40 * 1199884 * 2
def baseEnd_1199884 : Nat := 273829876284217192014151

theorem tailTrace_1199884 : CollatzResearch.WordTrace tailWord_1199884 prefixEnd_1199884 273829876284217192014151 := by
  unfold tailWord_1199884
  simp only [CollatzResearch.WordTrace]
  refine ⟨21881682392516333358743353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29175576523355111144991137 21881682392516333358743353)
  ·
    refine ⟨16411261794387250019057515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21881682392516333358743353 16411261794387250019057515)
    ·
      refine ⟨24616892691580875028586273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16411261794387250019057515 24616892691580875028586273)
      ·
        refine ⟨18462669518685656271439705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24616892691580875028586273 18462669518685656271439705)
        ·
          refine ⟨13847002139014242203579779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18462669518685656271439705 13847002139014242203579779)
          ·
            refine ⟨20770503208521363305369669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13847002139014242203579779 20770503208521363305369669)
            ·
              refine ⟨3894469351597755619756813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20770503208521363305369669 3894469351597755619756813)
              ·
                refine ⟨1460426006849158357408805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3894469351597755619756813 1460426006849158357408805)
                ·
                  refine ⟨273829876284217192014151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460426006849158357408805 273829876284217192014151)
                  ·
                    rfl

theorem cell21_1199884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1199884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199884 prefixEnd_1199884 := by exact prefixLift 1199884
  have htrace : WordTrace (prefixWord ++ tailWord_1199884) baseStart_1199884 baseEnd_1199884 := by
    simpa [prefixWord, tailWord_1199884, baseEnd_1199884] using wordTrace_append hprefix tailTrace_1199884
  have hstable : (prefixWord ++ tailWord_1199884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199884).length < 2 ^ (prefixWord ++ tailWord_1199884).sum := by decide
  have hdescent : baseEnd_1199884 < baseStart_1199884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1199949 : List Nat := [1, 6, 1, 2, 1, 3, 2, 5]
def baseStart_1199949 : Nat := 118140960795 + 1199949 * 2 ^ 59
def prefixEnd_1199949 : Nat := 4983230072969 + 3 ^ 40 * 1199949 * 2
def baseEnd_1199949 : Nat := 91281570056597174476895

theorem tailTrace_1199949 : CollatzResearch.WordTrace tailWord_1199949 prefixEnd_1199949 91281570056597174476895 := by
  unfold tailWord_1199949
  simp only [CollatzResearch.WordTrace]
  refine ⟨43765735529797182818602901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29177157019864788545735267 43765735529797182818602901)
  ·
    refine ⟨2051518852959242944622011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43765735529797182818602901 2051518852959242944622011)
    ·
      refine ⟨3077278279438864416933017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051518852959242944622011 3077278279438864416933017)
      ·
        refine ⟨2307958709579148312699763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3077278279438864416933017 2307958709579148312699763)
        ·
          refine ⟨3461938064368722469049645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2307958709579148312699763 3461938064368722469049645)
          ·
            refine ⟨1298226774138270925893617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3461938064368722469049645 1298226774138270925893617)
            ·
              refine ⟨973670080603703194420213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298226774138270925893617 973670080603703194420213)
              ·
                refine ⟨91281570056597174476895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 973670080603703194420213 91281570056597174476895)
                ·
                  rfl

theorem cell21_1199949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 5].length) (baseStart_1199949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1199949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1199949 prefixEnd_1199949 := by exact prefixLift 1199949
  have htrace : WordTrace (prefixWord ++ tailWord_1199949) baseStart_1199949 baseEnd_1199949 := by
    simpa [prefixWord, tailWord_1199949, baseEnd_1199949] using wordTrace_append hprefix tailTrace_1199949
  have hstable : (prefixWord ++ tailWord_1199949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1199949).length < 2 ^ (prefixWord ++ tailWord_1199949).sum := by decide
  have hdescent : baseEnd_1199949 < baseStart_1199949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1199949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200036 : List Nat := [2, 3, 1, 2, 1, 3, 1, 4, 4]
def baseStart_1200036 : Nat := 118140960795 + 1200036 * 2 ^ 59
def prefixEnd_1200036 : Nat := 4983230072969 + 3 ^ 40 * 1200036 * 2
def baseEnd_1200036 : Nat := 273864564755098705480507

theorem tailTrace_1200036 : CollatzResearch.WordTrace tailWord_1200036 prefixEnd_1200036 273864564755098705480507 := by
  unfold tailWord_1200036
  simp only [CollatzResearch.WordTrace]
  refine ⟨21884454340240998338509981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29179272453654664451346641 21884454340240998338509981)
  ·
    refine ⟨8206670377590374376941243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21884454340240998338509981 8206670377590374376941243)
    ·
      refine ⟨12310005566385561565411865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8206670377590374376941243 12310005566385561565411865)
      ·
        refine ⟨9232504174789171174058899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12310005566385561565411865 9232504174789171174058899)
        ·
          refine ⟨13848756262183756761088349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9232504174789171174058899 13848756262183756761088349)
          ·
            refine ⟨5193283598318908785408131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13848756262183756761088349 5193283598318908785408131)
            ·
              refine ⟨7789925397478363178112197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5193283598318908785408131 7789925397478363178112197)
              ·
                refine ⟨1460611012027193095896037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7789925397478363178112197 1460611012027193095896037)
                ·
                  refine ⟨273864564755098705480507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460611012027193095896037 273864564755098705480507)
                  ·
                    rfl

theorem cell21_1200036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_1200036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200036 prefixEnd_1200036 := by exact prefixLift 1200036
  have htrace : WordTrace (prefixWord ++ tailWord_1200036) baseStart_1200036 baseEnd_1200036 := by
    simpa [prefixWord, tailWord_1200036, baseEnd_1200036] using wordTrace_append hprefix tailTrace_1200036
  have hstable : (prefixWord ++ tailWord_1200036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200036).length < 2 ^ (prefixWord ++ tailWord_1200036).sum := by decide
  have hdescent : baseEnd_1200036 < baseStart_1200036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200039 : List Nat := [1, 1, 6, 1, 2, 2, 1, 4, 3]
def baseStart_1200039 : Nat := 118140960795 + 1200039 * 2 ^ 59
def prefixEnd_1200039 : Nat := 4983230072969 + 3 ^ 40 * 1200039 * 2
def baseEnd_1200039 : Nat := 273865249395971366930501

theorem tailTrace_1200039 : CollatzResearch.WordTrace tailWord_1200039 prefixEnd_1200039 273865249395971366930501 := by
  unfold tailWord_1200039
  simp only [CollatzResearch.WordTrace]
  refine ⟨43769018099471128189379171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29179345399647418792919447 43769018099471128189379171)
  ·
    refine ⟨65653527149206692284068757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43769018099471128189379171 65653527149206692284068757)
    ·
      refine ⟨3077509085119063700815723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65653527149206692284068757 3077509085119063700815723)
      ·
        refine ⟨4616263627678595551223585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077509085119063700815723 4616263627678595551223585)
        ·
          refine ⟨3462197720758946663417689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4616263627678595551223585 3462197720758946663417689)
          ·
            refine ⟨2596648290569209997563267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3462197720758946663417689 2596648290569209997563267)
            ·
              refine ⟨3894972435853814996344901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2596648290569209997563267 3894972435853814996344901)
              ·
                refine ⟨730307331722590311814669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3894972435853814996344901 730307331722590311814669)
                ·
                  refine ⟨273865249395971366930501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730307331722590311814669 273865249395971366930501)
                  ·
                    rfl

theorem cell21_1200039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 4, 3].length) (baseStart_1200039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200039 prefixEnd_1200039 := by exact prefixLift 1200039
  have htrace : WordTrace (prefixWord ++ tailWord_1200039) baseStart_1200039 baseEnd_1200039 := by
    simpa [prefixWord, tailWord_1200039, baseEnd_1200039] using wordTrace_append hprefix tailTrace_1200039
  have hstable : (prefixWord ++ tailWord_1200039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200039).length < 2 ^ (prefixWord ++ tailWord_1200039).sum := by decide
  have hdescent : baseEnd_1200039 < baseStart_1200039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200205 : List Nat := [1, 6, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1200205 : Nat := 118140960795 + 1200205 * 2 ^ 59
def prefixEnd_1200205 : Nat := 4983230072969 + 3 ^ 40 * 1200205 * 2
def baseEnd_1200205 : Nat := 273903132857591967163495

theorem tailTrace_1200205 : CollatzResearch.WordTrace tailWord_1200205 prefixEnd_1200205 273903132857591967163495 := by
  unfold tailWord_1200205
  simp only [CollatzResearch.WordTrace]
  refine ⟨43775072616869738539922069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29183381744579825693281379 43775072616869738539922069)
  ·
    refine ⟨2051956528915768994058847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43775072616869738539922069 2051956528915768994058847)
    ·
      refine ⟨3077934793373653491088271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2051956528915768994058847 3077934793373653491088271)
      ·
        refine ⟨4616902190060480236632407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3077934793373653491088271 4616902190060480236632407)
        ·
          refine ⟨6925353285090720354948611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4616902190060480236632407 6925353285090720354948611)
          ·
            refine ⟨10388029927636080532422917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6925353285090720354948611 10388029927636080532422917)
            ·
              refine ⟨1947755611431765099829297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10388029927636080532422917 1947755611431765099829297)
              ·
                refine ⟨1460816708573823824871973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1947755611431765099829297 1460816708573823824871973)
                ·
                  refine ⟨273903132857591967163495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1460816708573823824871973 273903132857591967163495)
                  ·
                    rfl

theorem cell21_1200205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1200205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200205 prefixEnd_1200205 := by exact prefixLift 1200205
  have htrace : WordTrace (prefixWord ++ tailWord_1200205) baseStart_1200205 baseEnd_1200205 := by
    simpa [prefixWord, tailWord_1200205, baseEnd_1200205] using wordTrace_append hprefix tailTrace_1200205
  have hstable : (prefixWord ++ tailWord_1200205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200205).length < 2 ^ (prefixWord ++ tailWord_1200205).sum := by decide
  have hdescent : baseEnd_1200205 < baseStart_1200205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200264 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1200264 : Nat := 118140960795 + 1200264 * 2 ^ 59
def prefixEnd_1200264 : Nat := 4983230072969 + 3 ^ 40 * 1200264 * 2
def baseEnd_1200264 : Nat := 273916597461420975680041

theorem tailTrace_1200264 : CollatzResearch.WordTrace tailWord_1200264 prefixEnd_1200264 273916597461420975680041 := by
  unfold tailWord_1200264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21888612261827995808159923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29184816349103994410879897 21888612261827995808159923)
  ·
    refine ⟨32832918392741993712239885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21888612261827995808159923 32832918392741993712239885)
    ·
      refine ⟨12312344397278247642089957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32832918392741993712239885 12312344397278247642089957)
      ·
        refine ⟨2308564574489671432891867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12312344397278247642089957 2308564574489671432891867)
        ·
          refine ⟨3462846861734507149337801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2308564574489671432891867 3462846861734507149337801)
          ·
            refine ⟨2597135146300880362003351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3462846861734507149337801 2597135146300880362003351)
            ·
              refine ⟨3895702719451320543005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597135146300880362003351 3895702719451320543005027)
              ·
                refine ⟨5843554079176980814507541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3895702719451320543005027 5843554079176980814507541)
                ·
                  refine ⟨273916597461420975680041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5843554079176980814507541 273916597461420975680041)
                  ·
                    rfl

theorem cell21_1200264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1200264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200264 prefixEnd_1200264 := by exact prefixLift 1200264
  have htrace : WordTrace (prefixWord ++ tailWord_1200264) baseStart_1200264 baseEnd_1200264 := by
    simpa [prefixWord, tailWord_1200264, baseEnd_1200264] using wordTrace_append hprefix tailTrace_1200264
  have hstable : (prefixWord ++ tailWord_1200264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200264).length < 2 ^ (prefixWord ++ tailWord_1200264).sum := by decide
  have hdescent : baseEnd_1200264 < baseStart_1200264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200295 : List Nat := [1, 1, 6, 2, 2, 1, 1, 7]
def baseStart_1200295 : Nat := 118140960795 + 1200295 * 2 ^ 59
def prefixEnd_1200295 : Nat := 4983230072969 + 3 ^ 40 * 1200295 * 2
def baseEnd_1200295 : Nat := 91307890694590603554437

theorem tailTrace_1200295 : CollatzResearch.WordTrace tailWord_1200295 prefixEnd_1200295 91307890694590603554437 := by
  unfold tailWord_1200295
  simp only [CollatzResearch.WordTrace]
  refine ⟨43778355186543683910698339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29185570124362455940465559 43778355186543683910698339)
  ·
    refine ⟨65667532779815525866047509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43778355186543683910698339 65667532779815525866047509)
    ·
      refine ⟨3078165599053852774970977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65667532779815525866047509 3078165599053852774970977)
      ·
        refine ⟨2308624199290389581228233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3078165599053852774970977 2308624199290389581228233)
        ·
          refine ⟨1731468149467792185921175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2308624199290389581228233 1731468149467792185921175)
          ·
            refine ⟨2597202224201688278881763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1731468149467792185921175 2597202224201688278881763)
            ·
              refine ⟨3895803336302532418322645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2597202224201688278881763 3895803336302532418322645)
              ·
                refine ⟨91307890694590603554437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3895803336302532418322645 91307890694590603554437)
                ·
                  rfl

theorem cell21_1200295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 7].length) (baseStart_1200295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200295 prefixEnd_1200295 := by exact prefixLift 1200295
  have htrace : WordTrace (prefixWord ++ tailWord_1200295) baseStart_1200295 baseEnd_1200295 := by
    simpa [prefixWord, tailWord_1200295, baseEnd_1200295] using wordTrace_append hprefix tailTrace_1200295
  have hstable : (prefixWord ++ tailWord_1200295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200295).length < 2 ^ (prefixWord ++ tailWord_1200295).sum := by decide
  have hdescent : baseEnd_1200295 < baseStart_1200295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200337 : List Nat := [1, 2, 2, 1, 2, 2, 3, 8]
def baseStart_1200337 : Nat := 118140960795 + 1200337 * 2 ^ 59
def prefixEnd_1200337 : Nat := 4983230072969 + 3 ^ 40 * 1200337 * 2
def baseEnd_1200337 : Nat := 91311085685329690321075

theorem tailTrace_1200337 : CollatzResearch.WordTrace tailWord_1200337 prefixEnd_1200337 91311085685329690321075 := by
  unfold tailWord_1200337
  simp only [CollatzResearch.WordTrace]
  refine ⟨43779887052391525083727265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29186591368261016722484843 43779887052391525083727265)
  ·
    refine ⟨32834915289293643812795449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43779887052391525083727265 32834915289293643812795449)
    ·
      refine ⟨24626186466970232859596587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32834915289293643812795449 24626186466970232859596587)
      ·
        refine ⟨36939279700455349289394881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24626186466970232859596587 36939279700455349289394881)
        ·
          refine ⟨27704459775341511967046161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36939279700455349289394881 27704459775341511967046161)
          ·
            refine ⟨20778344831506133975284621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27704459775341511967046161 20778344831506133975284621)
            ·
              refine ⟨7791879311814800240731733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20778344831506133975284621 7791879311814800240731733)
              ·
                refine ⟨91311085685329690321075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7791879311814800240731733 91311085685329690321075)
                ·
                  rfl

theorem cell21_1200337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 8].length) (baseStart_1200337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200337 prefixEnd_1200337 := by exact prefixLift 1200337
  have htrace : WordTrace (prefixWord ++ tailWord_1200337) baseStart_1200337 baseEnd_1200337 := by
    simpa [prefixWord, tailWord_1200337, baseEnd_1200337] using wordTrace_append hprefix tailTrace_1200337
  have hstable : (prefixWord ++ tailWord_1200337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200337).length < 2 ^ (prefixWord ++ tailWord_1200337).sum := by decide
  have hdescent : baseEnd_1200337 < baseStart_1200337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200388 : List Nat := [2, 3, 2, 2, 4, 1, 1, 6]
def baseStart_1200388 : Nat := 118140960795 + 1200388 * 2 ^ 59
def prefixEnd_1200388 : Nat := 4983230072969 + 3 ^ 40 * 1200388 * 2
def baseEnd_1200388 : Nat := 91314965316941438537707

theorem tailTrace_1200388 : CollatzResearch.WordTrace tailWord_1200388 prefixEnd_1200388 91314965316941438537707 := by
  unfold tailWord_1200388
  simp only [CollatzResearch.WordTrace]
  refine ⟨21890873587603380396916909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29187831450137840529222545 21890873587603380396916909)
  ·
    refine ⟨8209077595351267648843841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21890873587603380396916909 8209077595351267648843841)
    ·
      refine ⟨6156808196513450736632881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8209077595351267648843841 6156808196513450736632881)
      ·
        refine ⟨4617606147385088052474661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6156808196513450736632881 4617606147385088052474661)
        ·
          refine ⟨865801152634704009838999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4617606147385088052474661 865801152634704009838999)
          ·
            refine ⟨1298701728952056014758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 865801152634704009838999 1298701728952056014758499)
            ·
              refine ⟨1948052593428084022137749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298701728952056014758499 1948052593428084022137749)
              ·
                refine ⟨91314965316941438537707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1948052593428084022137749 91314965316941438537707)
                ·
                  rfl

theorem cell21_1200388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_1200388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200388 prefixEnd_1200388 := by exact prefixLift 1200388
  have htrace : WordTrace (prefixWord ++ tailWord_1200388) baseStart_1200388 baseEnd_1200388 := by
    simpa [prefixWord, tailWord_1200388, baseEnd_1200388] using wordTrace_append hprefix tailTrace_1200388
  have hstable : (prefixWord ++ tailWord_1200388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200388).length < 2 ^ (prefixWord ++ tailWord_1200388).sum := by decide
  have hdescent : baseEnd_1200388 < baseStart_1200388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200433 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 4]
def baseStart_1200433 : Nat := 118140960795 + 1200433 * 2 ^ 59
def prefixEnd_1200433 : Nat := 4983230072969 + 3 ^ 40 * 1200433 * 2
def baseEnd_1200433 : Nat := 273955165563914237363029

theorem tailTrace_1200433 : CollatzResearch.WordTrace tailWord_1200433 prefixEnd_1200433 273955165563914237363029 := by
  unfold tailWord_1200433
  simp only [CollatzResearch.WordTrace]
  refine ⟨43783388460043733479221953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29188925640029155652814635 43783388460043733479221953)
  ·
    refine ⟨32837541345032800109416465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43783388460043733479221953 32837541345032800109416465)
    ·
      refine ⟨24628156008774600082062349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32837541345032800109416465 24628156008774600082062349)
      ·
        refine ⟨9235558503290475030773381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24628156008774600082062349 9235558503290475030773381)
        ·
          refine ⟨1731667219366964068270009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9235558503290475030773381 1731667219366964068270009)
          ·
            refine ⟨1298750414525223051202507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731667219366964068270009 1298750414525223051202507)
            ·
              refine ⟨1948125621787834576803761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298750414525223051202507 1948125621787834576803761)
              ·
                refine ⟨1461094216340875932602821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1948125621787834576803761 1461094216340875932602821)
                ·
                  refine ⟨273955165563914237363029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461094216340875932602821 273955165563914237363029)
                  ·
                    rfl

theorem cell21_1200433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_1200433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200433 prefixEnd_1200433 := by exact prefixLift 1200433
  have htrace : WordTrace (prefixWord ++ tailWord_1200433) baseStart_1200433 baseEnd_1200433 := by
    simpa [prefixWord, tailWord_1200433, baseEnd_1200433] using wordTrace_append hprefix tailTrace_1200433
  have hstable : (prefixWord ++ tailWord_1200433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200433).length < 2 ^ (prefixWord ++ tailWord_1200433).sum := by decide
  have hdescent : baseEnd_1200433 < baseStart_1200433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200509 : List Nat := [1, 4, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1200509 : Nat := 118140960795 + 1200509 * 2 ^ 59
def prefixEnd_1200509 : Nat := 4983230072969 + 3 ^ 40 * 1200509 * 2
def baseEnd_1200509 : Nat := 273972509799354994096207

theorem tailTrace_1200509 : CollatzResearch.WordTrace tailWord_1200509 prefixEnd_1200509 273972509799354994096207 := by
  unfold tailWord_1200509
  simp only [CollatzResearch.WordTrace]
  refine ⟨43786160407768398458988581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29190773605178932305992387 43786160407768398458988581)
  ·
    refine ⟨8209905076456574711060359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43786160407768398458988581 8209905076456574711060359)
    ·
      refine ⟨12314857614684862066590539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8209905076456574711060359 12314857614684862066590539)
      ·
        refine ⟨18472286422027293099885809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12314857614684862066590539 18472286422027293099885809)
        ·
          refine ⟨13854214816520469824914357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18472286422027293099885809 13854214816520469824914357)
          ·
            refine ⟨1298832639048794046085721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13854214816520469824914357 1298832639048794046085721)
            ·
              refine ⟨974124479286595534564291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1298832639048794046085721 974124479286595534564291)
              ·
                refine ⟨1461186718929893301846437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974124479286595534564291 1461186718929893301846437)
                ·
                  refine ⟨273972509799354994096207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461186718929893301846437 273972509799354994096207)
                  ·
                    rfl

theorem cell21_1200509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1200509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200509 prefixEnd_1200509 := by exact prefixLift 1200509
  have htrace : WordTrace (prefixWord ++ tailWord_1200509) baseStart_1200509 baseEnd_1200509 := by
    simpa [prefixWord, tailWord_1200509, baseEnd_1200509] using wordTrace_append hprefix tailTrace_1200509
  have hstable : (prefixWord ++ tailWord_1200509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200509).length < 2 ^ (prefixWord ++ tailWord_1200509).sum := by decide
  have hdescent : baseEnd_1200509 < baseStart_1200509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200520 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 7]
def baseStart_1200520 : Nat := 118140960795 + 1200520 * 2 ^ 59
def prefixEnd_1200520 : Nat := 4983230072969 + 3 ^ 40 * 1200520 * 2
def baseEnd_1200520 : Nat := 273975020149221419412851

theorem tailTrace_1200520 : CollatzResearch.WordTrace tailWord_1200520 prefixEnd_1200520 273975020149221419412851 := by
  unfold tailWord_1200520
  simp only [CollatzResearch.WordTrace]
  refine ⟨21893280805364273668819507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29191041073819031558426009 21893280805364273668819507)
  ·
    refine ⟨32839921208046410503229261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21893280805364273668819507 32839921208046410503229261)
    ·
      refine ⟨12314970453017403938710973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32839921208046410503229261 12314970453017403938710973)
      ·
        refine ⟨4618113919881526477016615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12314970453017403938710973 4618113919881526477016615)
        ·
          refine ⟨6927170879822289715524923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618113919881526477016615 6927170879822289715524923)
          ·
            refine ⟨10390756319733434573287385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6927170879822289715524923 10390756319733434573287385)
            ·
              refine ⟨7793067239800075929965539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10390756319733434573287385 7793067239800075929965539)
              ·
                refine ⟨11689600859700113894948309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7793067239800075929965539 11689600859700113894948309)
                ·
                  refine ⟨273975020149221419412851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11689600859700113894948309 273975020149221419412851)
                  ·
                    rfl

theorem cell21_1200520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_1200520 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200520 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200520 prefixEnd_1200520 := by exact prefixLift 1200520
  have htrace : WordTrace (prefixWord ++ tailWord_1200520) baseStart_1200520 baseEnd_1200520 := by
    simpa [prefixWord, tailWord_1200520, baseEnd_1200520] using wordTrace_append hprefix tailTrace_1200520
  have hstable : (prefixWord ++ tailWord_1200520).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200520).length < 2 ^ (prefixWord ++ tailWord_1200520).sum := by decide
  have hdescent : baseEnd_1200520 < baseStart_1200520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200537 : List Nat := [1, 2, 1, 2, 1, 4, 2, 5, 3]
def baseStart_1200537 : Nat := 118140960795 + 1200537 * 2 ^ 59
def prefixEnd_1200537 : Nat := 4983230072969 + 3 ^ 40 * 1200537 * 2
def baseEnd_1200537 : Nat := 273978899780833167629483

theorem tailTrace_1200537 : CollatzResearch.WordTrace tailWord_1200537 prefixEnd_1200537 273978899780833167629483 := by
  unfold tailWord_1200537
  simp only [CollatzResearch.WordTrace]
  refine ⟨43787181651666959241007865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29191454434444639494005243 43787181651666959241007865)
  ·
    refine ⟨32840386238750219430755899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43787181651666959241007865 32840386238750219430755899)
    ·
      refine ⟨49260579358125329146133849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32840386238750219430755899 49260579358125329146133849)
      ·
        refine ⟨36945434518593996859600387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49260579358125329146133849 36945434518593996859600387)
        ·
          refine ⟨55418151777890995289400581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36945434518593996859600387 55418151777890995289400581)
          ·
            refine ⟨10390903458354561616762609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55418151777890995289400581 10390903458354561616762609)
            ·
              refine ⟨7793177593765921212571957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10390903458354561616762609 7793177593765921212571957)
              ·
                refine ⟨730610399415555113678621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7793177593765921212571957 730610399415555113678621)
                ·
                  refine ⟨273978899780833167629483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730610399415555113678621 273978899780833167629483)
                  ·
                    rfl

theorem cell21_1200537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_1200537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200537 prefixEnd_1200537 := by exact prefixLift 1200537
  have htrace : WordTrace (prefixWord ++ tailWord_1200537) baseStart_1200537 baseEnd_1200537 := by
    simpa [prefixWord, tailWord_1200537, baseEnd_1200537] using wordTrace_append hprefix tailTrace_1200537
  have hstable : (prefixWord ++ tailWord_1200537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200537).length < 2 ^ (prefixWord ++ tailWord_1200537).sum := by decide
  have hdescent : baseEnd_1200537 < baseStart_1200537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200647 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 3]
def baseStart_1200647 : Nat := 118140960795 + 1200647 * 2 ^ 59
def prefixEnd_1200647 : Nat := 4983230072969 + 3 ^ 40 * 1200647 * 2
def baseEnd_1200647 : Nat := 274004003279497420795925

theorem tailTrace_1200647 : CollatzResearch.WordTrace tailWord_1200647 prefixEnd_1200647 274004003279497420795925 := by
  unfold tailWord_1200647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43791193681268448027512195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29194129120845632018341463 43791193681268448027512195)
  ·
    refine ⟨65686790521902672041268293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43791193681268448027512195 65686790521902672041268293)
    ·
      refine ⟨12316273222856751007737805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65686790521902672041268293 12316273222856751007737805)
      ·
        refine ⟨4618602458571281627901677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12316273222856751007737805 4618602458571281627901677)
        ·
          refine ⟨1731975921964230610463129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4618602458571281627901677 1731975921964230610463129)
          ·
            refine ⟨1298981941473172957847347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1731975921964230610463129 1298981941473172957847347)
            ·
              refine ⟨1948472912209759436771021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1298981941473172957847347 1948472912209759436771021)
              ·
                refine ⟨730677342078659788789133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1948472912209759436771021 730677342078659788789133)
                ·
                  refine ⟨274004003279497420795925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730677342078659788789133 274004003279497420795925)
                  ·
                    rfl

theorem cell21_1200647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 3].length) (baseStart_1200647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200647 prefixEnd_1200647 := by exact prefixLift 1200647
  have htrace : WordTrace (prefixWord ++ tailWord_1200647) baseStart_1200647 baseEnd_1200647 := by
    simpa [prefixWord, tailWord_1200647, baseEnd_1200647] using wordTrace_append hprefix tailTrace_1200647
  have hstable : (prefixWord ++ tailWord_1200647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200647).length < 2 ^ (prefixWord ++ tailWord_1200647).sum := by decide
  have hdescent : baseEnd_1200647 < baseStart_1200647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200655 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 9]
def baseStart_1200655 : Nat := 118140960795 + 1200655 * 2 ^ 59
def prefixEnd_1200655 : Nat := 4983230072969 + 3 ^ 40 * 1200655 * 2
def baseEnd_1200655 : Nat := 274005828988491184662575

theorem tailTrace_1200655 : CollatzResearch.WordTrace tailWord_1200655 prefixEnd_1200655 274005828988491184662575 := by
  unfold tailWord_1200655
  simp only [CollatzResearch.WordTrace]
  refine ⟨43791485465239465393803419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29194323643492976929202279 43791485465239465393803419)
  ·
    refine ⟨65687228197859198090705129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43791485465239465393803419 65687228197859198090705129)
    ·
      refine ⟨49265421148394398568028847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65687228197859198090705129 49265421148394398568028847)
      ·
        refine ⟨73898131722591597852043271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49265421148394398568028847 73898131722591597852043271)
        ·
          refine ⟨110847197583887396778064907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73898131722591597852043271 110847197583887396778064907)
          ·
            refine ⟨166270796375831095167097361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110847197583887396778064907 166270796375831095167097361)
            ·
              refine ⟨124703097281873321375323021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166270796375831095167097361 124703097281873321375323021)
              ·
                refine ⟨46763661480702495515746133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 124703097281873321375323021 46763661480702495515746133)
                ·
                  refine ⟨274005828988491184662575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46763661480702495515746133 274005828988491184662575)
                  ·
                    rfl

theorem cell21_1200655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 9].length) (baseStart_1200655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200655 prefixEnd_1200655 := by exact prefixLift 1200655
  have htrace : WordTrace (prefixWord ++ tailWord_1200655) baseStart_1200655 baseEnd_1200655 := by
    simpa [prefixWord, tailWord_1200655, baseEnd_1200655] using wordTrace_append hprefix tailTrace_1200655
  have hstable : (prefixWord ++ tailWord_1200655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200655).length < 2 ^ (prefixWord ++ tailWord_1200655).sum := by decide
  have hdescent : baseEnd_1200655 < baseStart_1200655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200855 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 4]
def baseStart_1200855 : Nat := 118140960795 + 1200855 * 2 ^ 59
def prefixEnd_1200855 : Nat := 4983230072969 + 3 ^ 40 * 1200855 * 2
def baseEnd_1200855 : Nat := 274051471713335281328833

theorem tailTrace_1200855 : CollatzResearch.WordTrace tailWord_1200855 prefixEnd_1200855 274051471713335281328833 := by
  unfold tailWord_1200855
  simp only [CollatzResearch.WordTrace]
  refine ⟨43798780064514899551084019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29199186709676599700722679 43798780064514899551084019)
  ·
    refine ⟨65698170096772349326626029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43798780064514899551084019 65698170096772349326626029)
    ·
      refine ⟨24636813786289630997484761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65698170096772349326626029 24636813786289630997484761)
      ·
        refine ⟨18477610339717223248113571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24636813786289630997484761 18477610339717223248113571)
        ·
          refine ⟨27716415509575834872170357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18477610339717223248113571 27716415509575834872170357)
          ·
            refine ⟨2598413954022734519265971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27716415509575834872170357 2598413954022734519265971)
            ·
              refine ⟨3897620931034101778898957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598413954022734519265971 3897620931034101778898957)
              ·
                refine ⟨1461607849137788167087109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3897620931034101778898957 1461607849137788167087109)
                ·
                  refine ⟨274051471713335281328833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1461607849137788167087109 274051471713335281328833)
                  ·
                    rfl

theorem cell21_1200855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 4].length) (baseStart_1200855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200855 prefixEnd_1200855 := by exact prefixLift 1200855
  have htrace : WordTrace (prefixWord ++ tailWord_1200855) baseStart_1200855 baseEnd_1200855 := by
    simpa [prefixWord, tailWord_1200855, baseEnd_1200855] using wordTrace_append hprefix tailTrace_1200855
  have hstable : (prefixWord ++ tailWord_1200855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200855).length < 2 ^ (prefixWord ++ tailWord_1200855).sum := by decide
  have hdescent : baseEnd_1200855 < baseStart_1200855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200869 : List Nat := [1, 3, 1, 4, 1, 2, 2, 7]
def baseStart_1200869 : Nat := 118140960795 + 1200869 * 2 ^ 59
def prefixEnd_1200869 : Nat := 4983230072969 + 3 ^ 40 * 1200869 * 2
def baseEnd_1200869 : Nat := 91351555568024789365157

theorem tailTrace_1200869 : CollatzResearch.WordTrace tailWord_1200869 prefixEnd_1200869 91351555568024789365157 := by
  unfold tailWord_1200869
  simp only [CollatzResearch.WordTrace]
  refine ⟨43799290686464179942093661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29199527124309453294729107 43799290686464179942093661)
  ·
    refine ⟨16424734007424067478285123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43799290686464179942093661 16424734007424067478285123)
    ·
      refine ⟨24637101011136101217427685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16424734007424067478285123 24637101011136101217427685)
      ·
        refine ⟨4619456439588018978267691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24637101011136101217427685 4619456439588018978267691)
        ·
          refine ⟨6929184659382028467401537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619456439588018978267691 6929184659382028467401537)
          ·
            refine ⟨5196888494536521350551153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6929184659382028467401537 5196888494536521350551153)
            ·
              refine ⟨3897666370902391012913365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5196888494536521350551153 3897666370902391012913365)
              ·
                refine ⟨91351555568024789365157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3897666370902391012913365 91351555568024789365157)
                ·
                  rfl

theorem cell21_1200869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_1200869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200869 prefixEnd_1200869 := by exact prefixLift 1200869
  have htrace : WordTrace (prefixWord ++ tailWord_1200869) baseStart_1200869 baseEnd_1200869 := by
    simpa [prefixWord, tailWord_1200869, baseEnd_1200869] using wordTrace_append hprefix tailTrace_1200869
  have hstable : (prefixWord ++ tailWord_1200869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200869).length < 2 ^ (prefixWord ++ tailWord_1200869).sum := by decide
  have hdescent : baseEnd_1200869 < baseStart_1200869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200900 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1200900 : Nat := 118140960795 + 1200900 * 2 ^ 59
def prefixEnd_1200900 : Nat := 4983230072969 + 3 ^ 40 * 1200900 * 2
def baseEnd_1200900 : Nat := 274061741326425203078741

theorem tailTrace_1200900 : CollatzResearch.WordTrace tailWord_1200900 prefixEnd_1200900 274061741326425203078741 := by
  unfold tailWord_1200900
  simp only [CollatzResearch.WordTrace]
  refine ⟨21900210674675936118236077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29200280899567914824314769 21900210674675936118236077)
  ·
    refine ⟨8212579003003476044338529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21900210674675936118236077 8212579003003476044338529)
    ·
      refine ⟨6159434252252607033253897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8212579003003476044338529 6159434252252607033253897)
      ·
        refine ⟨4619575689189455274940423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6159434252252607033253897 4619575689189455274940423)
        ·
          refine ⟨6929363533784182912410635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4619575689189455274940423 6929363533784182912410635)
          ·
            refine ⟨10394045300676274368615953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6929363533784182912410635 10394045300676274368615953)
            ·
              refine ⟨7795533975507205776461965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10394045300676274368615953 7795533975507205776461965)
              ·
                refine ⟨2923325240815202166173237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7795533975507205776461965 2923325240815202166173237)
                ·
                  refine ⟨274061741326425203078741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923325240815202166173237 274061741326425203078741)
                  ·
                    rfl

theorem cell21_1200900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1200900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200900 prefixEnd_1200900 := by exact prefixLift 1200900
  have htrace : WordTrace (prefixWord ++ tailWord_1200900) baseStart_1200900 baseEnd_1200900 := by
    simpa [prefixWord, tailWord_1200900, baseEnd_1200900] using wordTrace_append hprefix tailTrace_1200900
  have hstable : (prefixWord ++ tailWord_1200900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200900).length < 2 ^ (prefixWord ++ tailWord_1200900).sum := by decide
  have hdescent : baseEnd_1200900 < baseStart_1200900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1200948 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 6]
def baseStart_1200948 : Nat := 118140960795 + 1200948 * 2 ^ 59
def prefixEnd_1200948 : Nat := 4983230072969 + 3 ^ 40 * 1200948 * 2
def baseEnd_1200948 : Nat := 274072695580387786278643

theorem tailTrace_1200948 : CollatzResearch.WordTrace tailWord_1200948 prefixEnd_1200948 274072695580387786278643 := by
  unfold tailWord_1200948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21901086026588988217109749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29201448035451984289479665 21901086026588988217109749)
  ·
    refine ⟨2053226814992717645354039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21901086026588988217109749 2053226814992717645354039)
    ·
      refine ⟨3079840222489076468031059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2053226814992717645354039 3079840222489076468031059)
      ·
        refine ⟨4619760333733614702046589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079840222489076468031059 4619760333733614702046589)
        ·
          refine ⟨1732410125150105513267471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4619760333733614702046589 1732410125150105513267471)
          ·
            refine ⟨2598615187725158269901207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1732410125150105513267471 2598615187725158269901207)
            ·
              refine ⟨3897922781587737404851811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2598615187725158269901207 3897922781587737404851811)
              ·
                refine ⟨5846884172381606107277717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3897922781587737404851811 5846884172381606107277717)
                ·
                  refine ⟨274072695580387786278643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5846884172381606107277717 274072695580387786278643)
                  ·
                    rfl

theorem cell21_1200948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_1200948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1200948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1200948 prefixEnd_1200948 := by exact prefixLift 1200948
  have htrace : WordTrace (prefixWord ++ tailWord_1200948) baseStart_1200948 baseEnd_1200948 := by
    simpa [prefixWord, tailWord_1200948, baseEnd_1200948] using wordTrace_append hprefix tailTrace_1200948
  have hstable : (prefixWord ++ tailWord_1200948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1200948).length < 2 ^ (prefixWord ++ tailWord_1200948).sum := by decide
  have hdescent : baseEnd_1200948 < baseStart_1200948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1200948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201035 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 5]
def baseStart_1201035 : Nat := 118140960795 + 1201035 * 2 ^ 59
def prefixEnd_1201035 : Nat := 4983230072969 + 3 ^ 40 * 1201035 * 2
def baseEnd_1201035 : Nat := 274092550165694968328465

theorem tailTrace_1201035 : CollatzResearch.WordTrace tailWord_1201035 prefixEnd_1201035 274092550165694968328465 := by
  unfold tailWord_1201035
  simp only [CollatzResearch.WordTrace]
  refine ⟨43805345203862790292636559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29203563469241860195091039 43805345203862790292636559)
  ·
    refine ⟨65708017805794185438954839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43805345203862790292636559 65708017805794185438954839)
    ·
      refine ⟨98562026708691278158432259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65708017805794185438954839 98562026708691278158432259)
      ·
        refine ⟨147843040063036917237648389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98562026708691278158432259 147843040063036917237648389)
        ·
          refine ⟨27720570011819421982059073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 147843040063036917237648389 27720570011819421982059073)
          ·
            refine ⟨20790427508864566486544305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27720570011819421982059073 20790427508864566486544305)
            ·
              refine ⟨15592820631648424864908229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20790427508864566486544305 15592820631648424864908229)
              ·
                refine ⟨2923653868434079662170293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15592820631648424864908229 2923653868434079662170293)
                ·
                  refine ⟨274092550165694968328465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2923653868434079662170293 274092550165694968328465)
                  ·
                    rfl

theorem cell21_1201035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 5].length) (baseStart_1201035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201035 prefixEnd_1201035 := by exact prefixLift 1201035
  have htrace : WordTrace (prefixWord ++ tailWord_1201035) baseStart_1201035 baseEnd_1201035 := by
    simpa [prefixWord, tailWord_1201035, baseEnd_1201035] using wordTrace_append hprefix tailTrace_1201035
  have hstable : (prefixWord ++ tailWord_1201035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201035).length < 2 ^ (prefixWord ++ tailWord_1201035).sum := by decide
  have hdescent : baseEnd_1201035 < baseStart_1201035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201162 : List Nat := [3, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_1201162 : Nat := 118140960795 + 1201162 * 2 ^ 59
def prefixEnd_1201162 : Nat := 4983230072969 + 3 ^ 40 * 1201162 * 2
def baseEnd_1201162 : Nat := 274121533295970969711539

theorem tailTrace_1201162 : CollatzResearch.WordTrace tailWord_1201162 prefixEnd_1201162 274121533295970969711539 := by
  unfold tailWord_1201162
  simp only [CollatzResearch.WordTrace]
  refine ⟨10952494318600672745627435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29206651516268460655006493 10952494318600672745627435)
  ·
    refine ⟨16428741477901009118441153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10952494318600672745627435 16428741477901009118441153)
    ·
      refine ⟨12321556108425756838830865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16428741477901009118441153 12321556108425756838830865)
      ·
        refine ⟨9241167081319317629123149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12321556108425756838830865 9241167081319317629123149)
        ·
          refine ⟨3465437655494744110921181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9241167081319317629123149 3465437655494744110921181)
          ·
            refine ⟨1299539120810529041595443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3465437655494744110921181 1299539120810529041595443)
            ·
              refine ⟨1949308681215793562393165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299539120810529041595443 1949308681215793562393165)
              ·
                refine ⟨730990755455922585897437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1949308681215793562393165 730990755455922585897437)
                ·
                  refine ⟨274121533295970969711539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 730990755455922585897437 274121533295970969711539)
                  ·
                    rfl

theorem cell21_1201162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_1201162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201162 prefixEnd_1201162 := by exact prefixLift 1201162
  have htrace : WordTrace (prefixWord ++ tailWord_1201162) baseStart_1201162 baseEnd_1201162 := by
    simpa [prefixWord, tailWord_1201162, baseEnd_1201162] using wordTrace_append hprefix tailTrace_1201162
  have hstable : (prefixWord ++ tailWord_1201162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201162).length < 2 ^ (prefixWord ++ tailWord_1201162).sum := by decide
  have hdescent : baseEnd_1201162 < baseStart_1201162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201173 : List Nat := [1, 3, 2, 1, 4, 3, 7]
def baseStart_1201173 : Nat := 118140960795 + 1201173 * 2 ^ 59
def prefixEnd_1201173 : Nat := 4983230072969 + 3 ^ 40 * 1201173 * 2
def baseEnd_1201173 : Nat := 30458227071759710558687

theorem tailTrace_1201173 : CollatzResearch.WordTrace tailWord_1201173 prefixEnd_1201173 30458227071759710558687 := by
  unfold tailWord_1201173
  simp only [CollatzResearch.WordTrace]
  refine ⟨43810378477362839861160173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29206918984908559907440115 43810378477362839861160173)
  ·
    refine ⟨16428891929011064947935065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43810378477362839861160173 16428891929011064947935065)
    ·
      refine ⟨12321668946758298710951299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16428891929011064947935065 12321668946758298710951299)
      ·
        refine ⟨18482503420137448066426949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12321668946758298710951299 18482503420137448066426949)
        ·
          refine ⟨3465469391275771512455053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18482503420137448066426949 3465469391275771512455053)
          ·
            refine ⟨1299551021728414317170645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3465469391275771512455053 1299551021728414317170645)
            ·
              refine ⟨30458227071759710558687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1299551021728414317170645 30458227071759710558687)
              ·
                rfl

theorem cell21_1201173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 7].length) (baseStart_1201173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201173 prefixEnd_1201173 := by exact prefixLift 1201173
  have htrace : WordTrace (prefixWord ++ tailWord_1201173) baseStart_1201173 baseEnd_1201173 := by
    simpa [prefixWord, tailWord_1201173, baseEnd_1201173] using wordTrace_append hprefix tailTrace_1201173
  have hstable : (prefixWord ++ tailWord_1201173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201173).length < 2 ^ (prefixWord ++ tailWord_1201173).sum := by decide
  have hdescent : baseEnd_1201173 < baseStart_1201173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201263 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 5]
def baseStart_1201263 : Nat := 118140960795 + 1201263 * 2 ^ 59
def prefixEnd_1201263 : Nat := 4983230072969 + 3 ^ 40 * 1201263 * 2
def baseEnd_1201263 : Nat := 274144582872017238527999

theorem tailTrace_1201263 : CollatzResearch.WordTrace tailWord_1201263 prefixEnd_1201263 274144582872017238527999 := by
  unfold tailWord_1201263
  simp only [CollatzResearch.WordTrace]
  refine ⟨43813661047036785231936443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29209107364691190154624295 43813661047036785231936443)
  ·
    refine ⟨65720491570555177847904665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43813661047036785231936443 65720491570555177847904665)
    ·
      refine ⟨49290368677916383385928499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65720491570555177847904665 49290368677916383385928499)
      ·
        refine ⟨73935553016874575078892749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49290368677916383385928499 73935553016874575078892749)
        ·
          refine ⟨27725832381327965654584781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73935553016874575078892749 27725832381327965654584781)
          ·
            refine ⟨10397187142997987120469293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27725832381327965654584781 10397187142997987120469293)
            ·
              refine ⟨3898945178624245170175985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10397187142997987120469293 3898945178624245170175985)
              ·
                refine ⟨2924208883968183877631989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3898945178624245170175985 2924208883968183877631989)
                ·
                  refine ⟨274144582872017238527999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924208883968183877631989 274144582872017238527999)
                  ·
                    rfl

theorem cell21_1201263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 5].length) (baseStart_1201263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201263 prefixEnd_1201263 := by exact prefixLift 1201263
  have htrace : WordTrace (prefixWord ++ tailWord_1201263) baseStart_1201263 baseEnd_1201263 := by
    simpa [prefixWord, tailWord_1201263, baseEnd_1201263] using wordTrace_append hprefix tailTrace_1201263
  have hstable : (prefixWord ++ tailWord_1201263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201263).length < 2 ^ (prefixWord ++ tailWord_1201263).sum := by decide
  have hdescent : baseEnd_1201263 < baseStart_1201263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201280 : List Nat := [2, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_1201280 : Nat := 118140960795 + 1201280 * 2 ^ 59
def prefixEnd_1201280 : Nat := 4983230072969 + 3 ^ 40 * 1201280 * 2
def baseEnd_1201280 : Nat := 274148462503628986744631

theorem tailTrace_1201280 : CollatzResearch.WordTrace tailWord_1201280 prefixEnd_1201280 274148462503628986744631 := by
  unfold tailWord_1201280
  simp only [CollatzResearch.WordTrace]
  refine ⟨21907140543987598567652647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29209520725316798090203529 21907140543987598567652647)
  ·
    refine ⟨32860710815981397851478971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21907140543987598567652647 32860710815981397851478971)
    ·
      refine ⟨49291066223972096777218457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32860710815981397851478971 49291066223972096777218457)
      ·
        refine ⟨36968299667979072582913843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49291066223972096777218457 36968299667979072582913843)
        ·
          refine ⟨55452449501968608874370765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36968299667979072582913843 55452449501968608874370765)
          ·
            refine ⟨20794668563238228327889037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55452449501968608874370765 20794668563238228327889037)
            ·
              refine ⟨7798000711214335622958389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20794668563238228327889037 7798000711214335622958389)
              ·
                refine ⟨731062566676343964652349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7798000711214335622958389 731062566676343964652349)
                ·
                  refine ⟨274148462503628986744631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731062566676343964652349 274148462503628986744631)
                  ·
                    rfl

theorem cell21_1201280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_1201280 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201280 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201280 prefixEnd_1201280 := by exact prefixLift 1201280
  have htrace : WordTrace (prefixWord ++ tailWord_1201280) baseStart_1201280 baseEnd_1201280 := by
    simpa [prefixWord, tailWord_1201280, baseEnd_1201280] using wordTrace_append hprefix tailTrace_1201280
  have hstable : (prefixWord ++ tailWord_1201280).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201280).length < 2 ^ (prefixWord ++ tailWord_1201280).sum := by decide
  have hdescent : baseEnd_1201280 < baseStart_1201280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201384 : List Nat := [2, 1, 4, 1, 2, 1, 1, 9]
def baseStart_1201384 : Nat := 118140960795 + 1201384 * 2 ^ 59
def prefixEnd_1201384 : Nat := 4983230072969 + 3 ^ 40 * 1201384 * 2
def baseEnd_1201384 : Nat := 91390732240182639003695

theorem tailTrace_1201384 : CollatzResearch.WordTrace tailWord_1201384 prefixEnd_1201384 91390732240182639003695 := by
  unfold tailWord_1201384
  simp only [CollatzResearch.WordTrace]
  refine ⟨21909037139799211448545603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29212049519732281931394137 21909037139799211448545603)
  ·
    refine ⟨32863555709698817172818405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21909037139799211448545603 32863555709698817172818405)
    ·
      refine ⟨6161916695568528219903451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32863555709698817172818405 6161916695568528219903451)
      ·
        refine ⟨9242875043352792329855177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6161916695568528219903451 9242875043352792329855177)
        ·
          refine ⟨6932156282514594247391383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9242875043352792329855177 6932156282514594247391383)
          ·
            refine ⟨10398234423771891371087075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6932156282514594247391383 10398234423771891371087075)
            ·
              refine ⟨15597351635657837056630613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10398234423771891371087075 15597351635657837056630613)
              ·
                refine ⟨91390732240182639003695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15597351635657837056630613 91390732240182639003695)
                ·
                  rfl

theorem cell21_1201384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 9].length) (baseStart_1201384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201384 prefixEnd_1201384 := by exact prefixLift 1201384
  have htrace : WordTrace (prefixWord ++ tailWord_1201384) baseStart_1201384 baseEnd_1201384 := by
    simpa [prefixWord, tailWord_1201384, baseEnd_1201384] using wordTrace_append hprefix tailTrace_1201384
  have hstable : (prefixWord ++ tailWord_1201384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201384).length < 2 ^ (prefixWord ++ tailWord_1201384).sum := by decide
  have hdescent : baseEnd_1201384 < baseStart_1201384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201429 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1201429 : Nat := 118140960795 + 1201429 * 2 ^ 59
def prefixEnd_1201429 : Nat := 4983230072969 + 3 ^ 40 * 1201429 * 2
def baseEnd_1201429 : Nat := 274182466333637838760993

theorem tailTrace_1201429 : CollatzResearch.WordTrace tailWord_1201429 prefixEnd_1201429 274182466333637838760993 := by
  unfold tailWord_1201429
  simp only [CollatzResearch.WordTrace]
  refine ⟨43819715564435395582479341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29213143709623597054986227 43819715564435395582479341)
  ·
    refine ⟨16432393336663273343429753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43819715564435395582479341 16432393336663273343429753)
    ·
      refine ⟨12324295002497455007572315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16432393336663273343429753 12324295002497455007572315)
      ·
        refine ⟨18486442503746182511358473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12324295002497455007572315 18486442503746182511358473)
        ·
          refine ⟨13864831877809636883518855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18486442503746182511358473 13864831877809636883518855)
          ·
            refine ⟨20797247816714455325278283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13864831877809636883518855 20797247816714455325278283)
            ·
              refine ⟨31195871725071682987917425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20797247816714455325278283 31195871725071682987917425)
              ·
                refine ⟨23396903793803762240938069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31195871725071682987917425 23396903793803762240938069)
                ·
                  refine ⟨274182466333637838760993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23396903793803762240938069 274182466333637838760993)
                  ·
                    rfl

theorem cell21_1201429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1201429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201429 prefixEnd_1201429 := by exact prefixLift 1201429
  have htrace : WordTrace (prefixWord ++ tailWord_1201429) baseStart_1201429 baseEnd_1201429 := by
    simpa [prefixWord, tailWord_1201429, baseEnd_1201429] using wordTrace_append hprefix tailTrace_1201429
  have hstable : (prefixWord ++ tailWord_1201429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201429).length < 2 ^ (prefixWord ++ tailWord_1201429).sum := by decide
  have hdescent : baseEnd_1201429 < baseStart_1201429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201522 : List Nat := [3, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1201522 : Nat := 118140960795 + 1201522 * 2 ^ 59
def prefixEnd_1201522 : Nat := 4983230072969 + 3 ^ 40 * 1201522 * 2
def baseEnd_1201522 : Nat := 274203690200690343710803

theorem tailTrace_1201522 : CollatzResearch.WordTrace tailWord_1201522 prefixEnd_1201522 274203690200690343710803 := by
  unfold tailWord_1201522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10955776888274618116403705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29215405035398981643743213 10955776888274618116403705)
  ·
    refine ⟨8216832666205963587302779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10955776888274618116403705 8216832666205963587302779)
    ·
      refine ⟨12325248999308945380954169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8216832666205963587302779 12325248999308945380954169)
      ·
        refine ⟨9243936749481709035715627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12325248999308945380954169 9243936749481709035715627)
        ·
          refine ⟨13865905124222563553573441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9243936749481709035715627 13865905124222563553573441)
          ·
            refine ⟨10399428843166922665180081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13865905124222563553573441 10399428843166922665180081)
            ·
              refine ⟨7799571632375191998885061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10399428843166922665180081 7799571632375191998885061)
              ·
                refine ⟨1462419681070348499790949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7799571632375191998885061 1462419681070348499790949)
                ·
                  refine ⟨274203690200690343710803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462419681070348499790949 274203690200690343710803)
                  ·
                    rfl

theorem cell21_1201522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1201522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201522 prefixEnd_1201522 := by exact prefixLift 1201522
  have htrace : WordTrace (prefixWord ++ tailWord_1201522) baseStart_1201522 baseEnd_1201522 := by
    simpa [prefixWord, tailWord_1201522, baseEnd_1201522] using wordTrace_append hprefix tailTrace_1201522
  have hstable : (prefixWord ++ tailWord_1201522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201522).length < 2 ^ (prefixWord ++ tailWord_1201522).sum := by decide
  have hdescent : baseEnd_1201522 < baseStart_1201522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201525 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1201525 : Nat := 118140960795 + 1201525 * 2 ^ 59
def prefixEnd_1201525 : Nat := 4983230072969 + 3 ^ 40 * 1201525 * 2
def baseEnd_1201525 : Nat := 274204374841563005160797

theorem tailTrace_1201525 : CollatzResearch.WordTrace tailWord_1201525 prefixEnd_1201525 274204374841563005160797 := by
  unfold tailWord_1201525
  simp only [CollatzResearch.WordTrace]
  refine ⟨43823216972087603977974029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29215477981391735985316019 43823216972087603977974029)
  ·
    refine ⟨16433706364532851491740261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43823216972087603977974029 16433706364532851491740261)
    ·
      refine ⟨3081319943349909654701299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16433706364532851491740261 3081319943349909654701299)
      ·
        refine ⟨4621979915024864482051949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3081319943349909654701299 4621979915024864482051949)
        ·
          refine ⟨1733242468134324180769481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4621979915024864482051949 1733242468134324180769481)
          ·
            refine ⟨1299931851100743135577111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733242468134324180769481 1299931851100743135577111)
            ·
              refine ⟨1949897776651114703365667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1299931851100743135577111 1949897776651114703365667)
              ·
                refine ⟨2924846664976672055048501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1949897776651114703365667 2924846664976672055048501)
                ·
                  refine ⟨274204374841563005160797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2924846664976672055048501 274204374841563005160797)
                  ·
                    rfl

theorem cell21_1201525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1201525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201525 prefixEnd_1201525 := by exact prefixLift 1201525
  have htrace : WordTrace (prefixWord ++ tailWord_1201525) baseStart_1201525 baseEnd_1201525 := by
    simpa [prefixWord, tailWord_1201525, baseEnd_1201525] using wordTrace_append hprefix tailTrace_1201525
  have hstable : (prefixWord ++ tailWord_1201525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201525).length < 2 ^ (prefixWord ++ tailWord_1201525).sum := by decide
  have hdescent : baseEnd_1201525 < baseStart_1201525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201539 : List Nat := [1, 1, 1, 3, 5, 1, 4, 1, 4]
def baseStart_1201539 : Nat := 118140960795 + 1201539 * 2 ^ 59
def prefixEnd_1201539 : Nat := 4983230072969 + 3 ^ 40 * 1201539 * 2
def baseEnd_1201539 : Nat := 274207569832302091927435

theorem tailTrace_1201539 : CollatzResearch.WordTrace tailWord_1201539 prefixEnd_1201539 274207569832302091927435 := by
  unfold tailWord_1201539
  simp only [CollatzResearch.WordTrace]
  refine ⟨43823727594036884368983671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29215818396024589579322447 43823727594036884368983671)
  ·
    refine ⟨65735591391055326553475507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43823727594036884368983671 65735591391055326553475507)
    ·
      refine ⟨98603387086582989830213261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65735591391055326553475507 98603387086582989830213261)
      ·
        refine ⟨36976270157468621186329973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98603387086582989830213261 36976270157468621186329973)
        ·
          refine ⟨3466525327262683236218435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36976270157468621186329973 3466525327262683236218435)
          ·
            refine ⟨5199787990894024854327653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3466525327262683236218435 5199787990894024854327653)
            ·
              refine ⟨974960248292629660186435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5199787990894024854327653 974960248292629660186435)
              ·
                refine ⟨1462440372438944490279653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 974960248292629660186435 1462440372438944490279653)
                ·
                  refine ⟨274207569832302091927435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462440372438944490279653 274207569832302091927435)
                  ·
                    rfl

theorem cell21_1201539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 1, 4].length) (baseStart_1201539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201539 prefixEnd_1201539 := by exact prefixLift 1201539
  have htrace : WordTrace (prefixWord ++ tailWord_1201539) baseStart_1201539 baseEnd_1201539 := by
    simpa [prefixWord, tailWord_1201539, baseEnd_1201539] using wordTrace_append hprefix tailTrace_1201539
  have hstable : (prefixWord ++ tailWord_1201539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201539).length < 2 ^ (prefixWord ++ tailWord_1201539).sum := by decide
  have hdescent : baseEnd_1201539 < baseStart_1201539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201576 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_1201576 : Nat := 118140960795 + 1201576 * 2 ^ 59
def prefixEnd_1201576 : Nat := 4983230072969 + 3 ^ 40 * 1201576 * 2
def baseEnd_1201576 : Nat := 274216013736398249810693

theorem tailTrace_1201576 : CollatzResearch.WordTrace tailWord_1201576 prefixEnd_1201576 274216013736398249810693 := by
  unfold tailWord_1201576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21912538547451419844040291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29216718063268559792053721 21912538547451419844040291)
  ·
    refine ⟨32868807821177129766060437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21912538547451419844040291 32868807821177129766060437)
    ·
      refine ⟨1540725366617677957784083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32868807821177129766060437 1540725366617677957784083)
      ·
        refine ⟨2311088049926516936676125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1540725366617677957784083 2311088049926516936676125)
        ·
          refine ⟨866658018722443851253547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2311088049926516936676125 866658018722443851253547)
          ·
            refine ⟨1299987028083665776880321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866658018722443851253547 1299987028083665776880321)
            ·
              refine ⟨974990271062749332660241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1299987028083665776880321 974990271062749332660241)
              ·
                refine ⟨731242703297061999495181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 974990271062749332660241 731242703297061999495181)
                ·
                  refine ⟨274216013736398249810693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731242703297061999495181 274216013736398249810693)
                  ·
                    rfl

theorem cell21_1201576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_1201576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201576 prefixEnd_1201576 := by exact prefixLift 1201576
  have htrace : WordTrace (prefixWord ++ tailWord_1201576) baseStart_1201576 baseEnd_1201576 := by
    simpa [prefixWord, tailWord_1201576, baseEnd_1201576] using wordTrace_append hprefix tailTrace_1201576
  have hstable : (prefixWord ++ tailWord_1201576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201576).length < 2 ^ (prefixWord ++ tailWord_1201576).sum := by decide
  have hdescent : baseEnd_1201576 < baseStart_1201576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201764 : List Nat := [2, 3, 1, 1, 2, 3, 3, 6]
def baseStart_1201764 : Nat := 118140960795 + 1201764 * 2 ^ 59
def prefixEnd_1201764 : Nat := 4983230072969 + 3 ^ 40 * 1201764 * 2
def baseEnd_1201764 : Nat := 91419639299250566892325

theorem tailTrace_1201764 : CollatzResearch.WordTrace tailWord_1201764 prefixEnd_1201764 91419639299250566892325 := by
  unfold tailWord_1201764
  simp only [CollatzResearch.WordTrace]
  refine ⟨21915967009110873897962173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29221289345481165197282897 21915967009110873897962173)
  ·
    refine ⟨8218487628416577711735815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21915967009110873897962173 8218487628416577711735815)
    ·
      refine ⟨12327731442624866567603723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8218487628416577711735815 12327731442624866567603723)
      ·
        refine ⟨18491597163937299851405585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12327731442624866567603723 18491597163937299851405585)
        ·
          refine ⟨13868697872952974888554189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18491597163937299851405585 13868697872952974888554189)
          ·
            refine ⟨5200761702357365583207821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13868697872952974888554189 5200761702357365583207821)
            ·
              refine ⟨1950285638384012093702933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5200761702357365583207821 1950285638384012093702933)
              ·
                refine ⟨91419639299250566892325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1950285638384012093702933 91419639299250566892325)
                ·
                  rfl

theorem cell21_1201764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 6].length) (baseStart_1201764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201764 prefixEnd_1201764 := by exact prefixLift 1201764
  have htrace : WordTrace (prefixWord ++ tailWord_1201764) baseStart_1201764 baseEnd_1201764 := by
    simpa [prefixWord, tailWord_1201764, baseEnd_1201764] using wordTrace_append hprefix tailTrace_1201764
  have hstable : (prefixWord ++ tailWord_1201764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201764).length < 2 ^ (prefixWord ++ tailWord_1201764).sum := by decide
  have hdescent : baseEnd_1201764 < baseStart_1201764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201809 : List Nat := [1, 2, 2, 1, 1, 1, 1, 8, 4]
def baseStart_1201809 : Nat := 118140960795 + 1201809 * 2 ^ 59
def prefixEnd_1201809 : Nat := 4983230072969 + 3 ^ 40 * 1201809 * 2
def baseEnd_1201809 : Nat := 274269187510841622426883

theorem tailTrace_1201809 : CollatzResearch.WordTrace tailWord_1201809 prefixEnd_1201809 274269187510841622426883 := by
  unfold tailWord_1201809
  simp only [CollatzResearch.WordTrace]
  refine ⟨43833575303058720481312481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29222383535372480320874987 43833575303058720481312481)
  ·
    refine ⟨32875181477294040360984361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43833575303058720481312481 32875181477294040360984361)
    ·
      refine ⟨24656386107970530270738271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32875181477294040360984361 24656386107970530270738271)
      ·
        refine ⟨36984579161955795406107407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24656386107970530270738271 36984579161955795406107407)
        ·
          refine ⟨55476868742933693109161111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36984579161955795406107407 55476868742933693109161111)
          ·
            refine ⟨83215303114400539663741667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55476868742933693109161111 83215303114400539663741667)
            ·
              refine ⟨124822954671600809495612501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83215303114400539663741667 124822954671600809495612501)
              ·
                refine ⟨1462769000057821986276709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 124822954671600809495612501 1462769000057821986276709)
                ·
                  refine ⟨274269187510841622426883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462769000057821986276709 274269187510841622426883)
                  ·
                    rfl

theorem cell21_1201809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_1201809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201809 prefixEnd_1201809 := by exact prefixLift 1201809
  have htrace : WordTrace (prefixWord ++ tailWord_1201809) baseStart_1201809 baseEnd_1201809 := by
    simpa [prefixWord, tailWord_1201809, baseEnd_1201809] using wordTrace_append hprefix tailTrace_1201809
  have hstable : (prefixWord ++ tailWord_1201809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201809).length < 2 ^ (prefixWord ++ tailWord_1201809).sum := by decide
  have hdescent : baseEnd_1201809 < baseStart_1201809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201832 : List Nat := [2, 1, 7, 1, 1, 2, 2, 5]
def baseStart_1201832 : Nat := 118140960795 + 1201832 * 2 ^ 59
def prefixEnd_1201832 : Nat := 4983230072969 + 3 ^ 40 * 1201832 * 2
def baseEnd_1201832 : Nat := 91424812141399564514501

theorem tailTrace_1201832 : CollatzResearch.WordTrace tailWord_1201832 prefixEnd_1201832 91424812141399564514501 := by
  unfold tailWord_1201832
  simp only [CollatzResearch.WordTrace]
  refine ⟨21917207090987697704699875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29222942787983596939599833 21917207090987697704699875)
  ·
    refine ⟨32875810636481546557049813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21917207090987697704699875 32875810636481546557049813)
    ·
      refine ⟨770526811792536247430855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 32875810636481546557049813 770526811792536247430855)
      ·
        refine ⟨1155790217688804371146283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 770526811792536247430855 1155790217688804371146283)
        ·
          refine ⟨1733685326533206556719425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1155790217688804371146283 1733685326533206556719425)
          ·
            refine ⟨1300263994899904917539569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1733685326533206556719425 1300263994899904917539569)
            ·
              refine ⟨975197996174928688154677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1300263994899904917539569 975197996174928688154677)
              ·
                refine ⟨91424812141399564514501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 975197996174928688154677 91424812141399564514501)
                ·
                  rfl

theorem cell21_1201832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 5].length) (baseStart_1201832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201832 prefixEnd_1201832 := by exact prefixLift 1201832
  have htrace : WordTrace (prefixWord ++ tailWord_1201832) baseStart_1201832 baseEnd_1201832 := by
    simpa [prefixWord, tailWord_1201832, baseEnd_1201832] using wordTrace_append hprefix tailTrace_1201832
  have hstable : (prefixWord ++ tailWord_1201832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201832).length < 2 ^ (prefixWord ++ tailWord_1201832).sum := by decide
  have hdescent : baseEnd_1201832 < baseStart_1201832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201840 : List Nat := [2, 1, 1, 1, 2, 1, 8, 5]
def baseStart_1201840 : Nat := 118140960795 + 1201840 * 2 ^ 59
def prefixEnd_1201840 : Nat := 4983230072969 + 3 ^ 40 * 1201840 * 2
def baseEnd_1201840 : Nat := 91425420711064152470051

theorem tailTrace_1201840 : CollatzResearch.WordTrace tailWord_1201840 prefixEnd_1201840 91425420711064152470051 := by
  unfold tailWord_1201840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21917352982973206387845487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29223137310630941850460649 21917352982973206387845487)
  ·
    refine ⟨32876029474459809581768231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21917352982973206387845487 32876029474459809581768231)
    ·
      refine ⟨49314044211689714372652347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32876029474459809581768231 49314044211689714372652347)
      ·
        refine ⟨73971066317534571558978521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49314044211689714372652347 73971066317534571558978521)
        ·
          refine ⟨55478299738150928669233891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73971066317534571558978521 55478299738150928669233891)
          ·
            refine ⟨83217449607226393003850837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55478299738150928669233891 83217449607226393003850837)
            ·
              refine ⟨975204487584684293013877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 83217449607226393003850837 975204487584684293013877)
              ·
                refine ⟨91425420711064152470051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 975204487584684293013877 91425420711064152470051)
                ·
                  rfl

theorem cell21_1201840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_1201840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201840 prefixEnd_1201840 := by exact prefixLift 1201840
  have htrace : WordTrace (prefixWord ++ tailWord_1201840) baseStart_1201840 baseEnd_1201840 := by
    simpa [prefixWord, tailWord_1201840, baseEnd_1201840] using wordTrace_append hprefix tailTrace_1201840
  have hstable : (prefixWord ++ tailWord_1201840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201840).length < 2 ^ (prefixWord ++ tailWord_1201840).sum := by decide
  have hdescent : baseEnd_1201840 < baseStart_1201840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201846 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1201846 : Nat := 118140960795 + 1201846 * 2 ^ 59
def prefixEnd_1201846 : Nat := 4983230072969 + 3 ^ 40 * 1201846 * 2
def baseEnd_1201846 : Nat := 274277631414937780310141

theorem tailTrace_1201846 : CollatzResearch.WordTrace tailWord_1201846 prefixEnd_1201846 274277631414937780310141 := by
  unfold tailWord_1201846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2739682800245292237525587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29223283202616450533606261 2739682800245292237525587)
  ·
    refine ⟨4109524200367938356288381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2739682800245292237525587 4109524200367938356288381)
    ·
      refine ⟨1541071575137976883608143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4109524200367938356288381 1541071575137976883608143)
      ·
        refine ⟨2311607362706965325412215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1541071575137976883608143 2311607362706965325412215)
        ·
          refine ⟨3467411044060447988118323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2311607362706965325412215 3467411044060447988118323)
          ·
            refine ⟨5201116566090671982177485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467411044060447988118323 5201116566090671982177485)
            ·
              refine ⟨1950418712284001993316557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5201116566090671982177485 1950418712284001993316557)
              ·
                refine ⟨731407017106500747493709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950418712284001993316557 731407017106500747493709)
                ·
                  refine ⟨274277631414937780310141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731407017106500747493709 274277631414937780310141)
                  ·
                    rfl

theorem cell21_1201846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1201846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201846 prefixEnd_1201846 := by exact prefixLift 1201846
  have htrace : WordTrace (prefixWord ++ tailWord_1201846) baseStart_1201846 baseEnd_1201846 := by
    simpa [prefixWord, tailWord_1201846, baseEnd_1201846] using wordTrace_append hprefix tailTrace_1201846
  have hstable : (prefixWord ++ tailWord_1201846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201846).length < 2 ^ (prefixWord ++ tailWord_1201846).sum := by decide
  have hdescent : baseEnd_1201846 < baseStart_1201846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201871 : List Nat := [1, 1, 2, 1, 1, 3, 1, 8, 3]
def baseStart_1201871 : Nat := 118140960795 + 1201871 * 2 ^ 59
def prefixEnd_1201871 : Nat := 4983230072969 + 3 ^ 40 * 1201871 * 2
def baseEnd_1201871 : Nat := 274283336755543292393423

theorem tailTrace_1201871 : CollatzResearch.WordTrace tailWord_1201871 prefixEnd_1201871 274283336755543292393423 := by
  unfold tailWord_1201871
  simp only [CollatzResearch.WordTrace]
  refine ⟨43835836628834105070069467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29223891085889403380046311 43835836628834105070069467)
  ·
    refine ⟨65753754943251157605104201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43835836628834105070069467 65753754943251157605104201)
    ·
      refine ⟨49315316207438368203828151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65753754943251157605104201 49315316207438368203828151)
      ·
        refine ⟨73972974311157552305742227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49315316207438368203828151 73972974311157552305742227)
        ·
          refine ⟨110959461466736328458613341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73972974311157552305742227 110959461466736328458613341)
          ·
            refine ⟨41609798050026123171980003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110959461466736328458613341 41609798050026123171980003)
            ·
              refine ⟨62414697075039184757970005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41609798050026123171980003 62414697075039184757970005)
              ·
                refine ⟨731422231348115446382461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 62414697075039184757970005 731422231348115446382461)
                ·
                  refine ⟨274283336755543292393423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731422231348115446382461 274283336755543292393423)
                  ·
                    rfl

theorem cell21_1201871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8, 3].length) (baseStart_1201871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201871 prefixEnd_1201871 := by exact prefixLift 1201871
  have htrace : WordTrace (prefixWord ++ tailWord_1201871) baseStart_1201871 baseEnd_1201871 := by
    simpa [prefixWord, tailWord_1201871, baseEnd_1201871] using wordTrace_append hprefix tailTrace_1201871
  have hstable : (prefixWord ++ tailWord_1201871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201871).length < 2 ^ (prefixWord ++ tailWord_1201871).sum := by decide
  have hdescent : baseEnd_1201871 < baseStart_1201871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201899 : List Nat := [1, 1, 1, 1, 2, 4, 4, 7]
def baseStart_1201899 : Nat := 118140960795 + 1201899 * 2 ^ 59
def prefixEnd_1201899 : Nat := 4983230072969 + 3 ^ 40 * 1201899 * 2
def baseEnd_1201899 : Nat := 91429908912340488642233

theorem tailTrace_1201899 : CollatzResearch.WordTrace tailWord_1201899 prefixEnd_1201899 91429908912340488642233 := by
  unfold tailWord_1201899
  simp only [CollatzResearch.WordTrace]
  refine ⟨43836857872732665852088751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29224571915155110568059167 43836857872732665852088751)
  ·
    refine ⟨65755286809098998778133127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43836857872732665852088751 65755286809098998778133127)
    ·
      refine ⟨98632930213648498167199691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65755286809098998778133127 98632930213648498167199691)
      ·
        refine ⟨147949395320472747250799537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98632930213648498167199691 147949395320472747250799537)
        ·
          refine ⟨110962046490354560438099653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147949395320472747250799537 110962046490354560438099653)
          ·
            refine ⟨20805383716941480082143685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110962046490354560438099653 20805383716941480082143685)
            ·
              refine ⟨3901009446926527515401941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20805383716941480082143685 3901009446926527515401941)
              ·
                refine ⟨91429908912340488642233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3901009446926527515401941 91429908912340488642233)
                ·
                  rfl

theorem cell21_1201899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 7].length) (baseStart_1201899 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201899 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201899 prefixEnd_1201899 := by exact prefixLift 1201899
  have htrace : WordTrace (prefixWord ++ tailWord_1201899) baseStart_1201899 baseEnd_1201899 := by
    simpa [prefixWord, tailWord_1201899, baseEnd_1201899] using wordTrace_append hprefix tailTrace_1201899
  have hstable : (prefixWord ++ tailWord_1201899).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201899).length < 2 ^ (prefixWord ++ tailWord_1201899).sum := by decide
  have hdescent : baseEnd_1201899 < baseStart_1201899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201964 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_1201964 : Nat := 118140960795 + 1201964 * 2 ^ 59
def prefixEnd_1201964 : Nat := 4983230072969 + 3 ^ 40 * 1201964 * 2
def baseEnd_1201964 : Nat := 274304560622595797343233

theorem tailTrace_1201964 : CollatzResearch.WordTrace tailWord_1201964 prefixEnd_1201964 274304560622595797343233 := by
  unfold tailWord_1201964
  simp only [CollatzResearch.WordTrace]
  refine ⟨21919614308748590976602473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29226152411664787968803297 21919614308748590976602473)
  ·
    refine ⟨16439710731561443232451855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21919614308748590976602473 16439710731561443232451855)
    ·
      refine ⟨24659566097342164848677783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16439710731561443232451855 24659566097342164848677783)
      ·
        refine ⟨36989349146013247273016675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24659566097342164848677783 36989349146013247273016675)
        ·
          refine ⟨55484023719019870909525013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36989349146013247273016675 55484023719019870909525013)
          ·
            refine ⟨2600813611829056448883985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55484023719019870909525013 2600813611829056448883985)
            ·
              refine ⟨1950610208871792336662989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2600813611829056448883985 1950610208871792336662989)
              ·
                refine ⟨731478828326922126248621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1950610208871792336662989 731478828326922126248621)
                ·
                  refine ⟨274304560622595797343233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731478828326922126248621 274304560622595797343233)
                  ·
                    rfl

theorem cell21_1201964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_1201964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201964 prefixEnd_1201964 := by exact prefixLift 1201964
  have htrace : WordTrace (prefixWord ++ tailWord_1201964) baseStart_1201964 baseEnd_1201964 := by
    simpa [prefixWord, tailWord_1201964, baseEnd_1201964] using wordTrace_append hprefix tailTrace_1201964
  have hstable : (prefixWord ++ tailWord_1201964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201964).length < 2 ^ (prefixWord ++ tailWord_1201964).sum := by decide
  have hdescent : baseEnd_1201964 < baseStart_1201964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1201978 : List Nat := [3, 1, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1201978 : Nat := 118140960795 + 1201978 * 2 ^ 59
def prefixEnd_1201978 : Nat := 4983230072969 + 3 ^ 40 * 1201978 * 2
def baseEnd_1201978 : Nat := 274307755613334884109871

theorem tailTrace_1201978 : CollatzResearch.WordTrace tailWord_1201978 prefixEnd_1201978 274307755613334884109871 := by
  unfold tailWord_1201978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10959934809861615586053647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29226492826297641562809725 10959934809861615586053647)
  ·
    refine ⟨16439902214792423379080471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10959934809861615586053647 16439902214792423379080471)
    ·
      refine ⟨24659853322188635068620707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16439902214792423379080471 24659853322188635068620707)
      ·
        refine ⟨36989779983282952602931061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24659853322188635068620707 36989779983282952602931061)
        ·
          refine ⟨3467791873432776806524787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36989779983282952602931061 3467791873432776806524787)
          ·
            refine ⟨5201687810149165209787181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3467791873432776806524787 5201687810149165209787181)
            ·
              refine ⟨1950632928805936953670193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5201687810149165209787181 1950632928805936953670193)
              ·
                refine ⟨1462974696604452715252645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950632928805936953670193 1462974696604452715252645)
                ·
                  refine ⟨274307755613334884109871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1462974696604452715252645 274307755613334884109871)
                  ·
                    rfl

theorem cell21_1201978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1201978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1201978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1201978 prefixEnd_1201978 := by exact prefixLift 1201978
  have htrace : WordTrace (prefixWord ++ tailWord_1201978) baseStart_1201978 baseEnd_1201978 := by
    simpa [prefixWord, tailWord_1201978, baseEnd_1201978] using wordTrace_append hprefix tailTrace_1201978
  have hstable : (prefixWord ++ tailWord_1201978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1201978).length < 2 ^ (prefixWord ++ tailWord_1201978).sum := by decide
  have hdescent : baseEnd_1201978 < baseStart_1201978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1201978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202026 : List Nat := [3, 1, 3, 4, 2, 1, 7]
def baseStart_1202026 : Nat := 118140960795 + 1202026 * 2 ^ 59
def prefixEnd_1202026 : Nat := 4983230072969 + 3 ^ 40 * 1202026 * 2
def baseEnd_1202026 : Nat := 30479856651921940812197

theorem tailTrace_1202026 : CollatzResearch.WordTrace tailWord_1202026 prefixEnd_1202026 30479856651921940812197 := by
  unfold tailWord_1202026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10960372485818141635490483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29227659962181711027974621 10960372485818141635490483)
  ·
    refine ⟨16440558728727212453235725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10960372485818141635490483 16440558728727212453235725)
    ·
      refine ⟨6165209523272704669963397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16440558728727212453235725 6165209523272704669963397)
      ·
        refine ⟨1155976785613632125618137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6165209523272704669963397 1155976785613632125618137)
        ·
          refine ⟨866982589210224094213603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1155976785613632125618137 866982589210224094213603)
          ·
            refine ⟨1300473883815336141320405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 866982589210224094213603 1300473883815336141320405)
            ·
              refine ⟨30479856651921940812197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1300473883815336141320405 30479856651921940812197)
              ·
                rfl

theorem cell21_1202026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 7].length) (baseStart_1202026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202026 prefixEnd_1202026 := by exact prefixLift 1202026
  have htrace : WordTrace (prefixWord ++ tailWord_1202026) baseStart_1202026 baseEnd_1202026 := by
    simpa [prefixWord, tailWord_1202026, baseEnd_1202026] using wordTrace_append hprefix tailTrace_1202026
  have hstable : (prefixWord ++ tailWord_1202026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202026).length < 2 ^ (prefixWord ++ tailWord_1202026).sum := by decide
  have hdescent : baseEnd_1202026 < baseStart_1202026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202037 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1202037 : Nat := 118140960795 + 1202037 * 2 ^ 59
def prefixEnd_1202037 : Nat := 4983230072969 + 3 ^ 40 * 1202037 * 2
def baseEnd_1202037 : Nat := 274321220217163892626417

theorem tailTrace_1202037 : CollatzResearch.WordTrace tailWord_1202037 prefixEnd_1202037 274321220217163892626417 := by
  unfold tailWord_1202037
  simp only [CollatzResearch.WordTrace]
  refine ⟨43841891146232715420612365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29227927430821810280408243 43841891146232715420612365)
  ·
    refine ⟨16440709179837268282729637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43841891146232715420612365 16440709179837268282729637)
    ·
      refine ⟨3082632971219487803011807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16440709179837268282729637 3082632971219487803011807)
      ·
        refine ⟨4623949456829231704517711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082632971219487803011807 4623949456829231704517711)
        ·
          refine ⟨6935924185243847556776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4623949456829231704517711 6935924185243847556776567)
          ·
            refine ⟨10403886277865771335164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6935924185243847556776567 10403886277865771335164851)
            ·
              refine ⟨15605829416798657002747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10403886277865771335164851 15605829416798657002747277)
              ·
                refine ⟨5852186031299496376030229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15605829416798657002747277 5852186031299496376030229)
                ·
                  refine ⟨274321220217163892626417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5852186031299496376030229 274321220217163892626417)
                  ·
                    rfl

theorem cell21_1202037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1202037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202037 prefixEnd_1202037 := by exact prefixLift 1202037
  have htrace : WordTrace (prefixWord ++ tailWord_1202037) baseStart_1202037 baseEnd_1202037 := by
    simpa [prefixWord, tailWord_1202037, baseEnd_1202037] using wordTrace_append hprefix tailTrace_1202037
  have hstable : (prefixWord ++ tailWord_1202037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202037).length < 2 ^ (prefixWord ++ tailWord_1202037).sum := by decide
  have hdescent : baseEnd_1202037 < baseStart_1202037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202051 : List Nat := [1, 1, 1, 3, 4, 2, 1, 8]
def baseStart_1202051 : Nat := 118140960795 + 1202051 * 2 ^ 59
def prefixEnd_1202051 : Nat := 4983230072969 + 3 ^ 40 * 1202051 * 2
def baseEnd_1202051 : Nat := 91441471735967659797685

theorem tailTrace_1202051 : CollatzResearch.WordTrace tailWord_1202051 prefixEnd_1202051 91441471735967659797685 := by
  unfold tailWord_1202051
  simp only [CollatzResearch.WordTrace]
  refine ⟨43842401768181995811622007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29228267845454663874414671 43842401768181995811622007)
  ·
    refine ⟨65763602652272993717433011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43842401768181995811622007 65763602652272993717433011)
    ·
      refine ⟨98645403978409490576149517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65763602652272993717433011 98645403978409490576149517)
      ·
        refine ⟨36992026491903558966056069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98645403978409490576149517 36992026491903558966056069)
        ·
          refine ⟨6936004967231917306135513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36992026491903558966056069 6936004967231917306135513)
          ·
            refine ⟨5202003725423937979601635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6936004967231917306135513 5202003725423937979601635)
            ·
              refine ⟨7803005588135906969402453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5202003725423937979601635 7803005588135906969402453)
              ·
                refine ⟨91441471735967659797685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7803005588135906969402453 91441471735967659797685)
                ·
                  rfl

theorem cell21_1202051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_1202051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202051 prefixEnd_1202051 := by exact prefixLift 1202051
  have htrace : WordTrace (prefixWord ++ tailWord_1202051) baseStart_1202051 baseEnd_1202051 := by
    simpa [prefixWord, tailWord_1202051, baseEnd_1202051] using wordTrace_append hprefix tailTrace_1202051
  have hstable : (prefixWord ++ tailWord_1202051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202051).length < 2 ^ (prefixWord ++ tailWord_1202051).sum := by decide
  have hdescent : baseEnd_1202051 < baseStart_1202051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202068 : List Nat := [2, 4, 2, 1, 1, 2, 2, 7]
def baseStart_1202068 : Nat := 118140960795 + 1202068 * 2 ^ 59
def prefixEnd_1202068 : Nat := 4983230072969 + 3 ^ 40 * 1202068 * 2
def baseEnd_1202068 : Nat := 91442764946504909203229

theorem tailTrace_1202068 : CollatzResearch.WordTrace tailWord_1202068 prefixEnd_1202068 91442764946504909203229 := by
  unfold tailWord_1202068
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921510904560203857495429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29228681206080271809993905 21921510904560203857495429)
  ·
    refine ⟨4110283294605038223280393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21921510904560203857495429 4110283294605038223280393)
    ·
      refine ⟨3082712470953778667460295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4110283294605038223280393 3082712470953778667460295)
      ·
        refine ⟨4624068706430668001190443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3082712470953778667460295 4624068706430668001190443)
        ·
          refine ⟨6936103059646002001785665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624068706430668001190443 6936103059646002001785665)
          ·
            refine ⟨5202077294734501501339249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6936103059646002001785665 5202077294734501501339249)
            ·
              refine ⟨3901557971050876126004437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5202077294734501501339249 3901557971050876126004437)
              ·
                refine ⟨91442764946504909203229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3901557971050876126004437 91442764946504909203229)
                ·
                  rfl

theorem cell21_1202068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 7].length) (baseStart_1202068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202068 prefixEnd_1202068 := by exact prefixLift 1202068
  have htrace : WordTrace (prefixWord ++ tailWord_1202068) baseStart_1202068 baseEnd_1202068 := by
    simpa [prefixWord, tailWord_1202068, baseEnd_1202068] using wordTrace_append hprefix tailTrace_1202068
  have hstable : (prefixWord ++ tailWord_1202068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202068).length < 2 ^ (prefixWord ++ tailWord_1202068).sum := by decide
  have hdescent : baseEnd_1202068 < baseStart_1202068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
