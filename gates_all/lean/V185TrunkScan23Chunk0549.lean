import V185TrunkScan23Chunk0548

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3245447 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 1, 5, 2]
def baseStart_3245447 : Nat := 118140960795 + 3245447 * 2 ^ 59
def prefixEnd_3245447 : Nat := 4983230072969 + 3 ^ 40 * 3245447 * 2
def baseEnd_3245447 : Nat := 1666474249692468907386967

theorem tailTrace_3245447 : CollatzResearch.WordTrace tailWord_3245447 prefixEnd_3245447 1666474249692468907386967 := by
  unfold tailWord_3245447
  simp only [CollatzResearch.WordTrace]
  refine ⟨118371176673307272064366595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78914117782204848042911063 118371176673307272064366595)
  ·
    refine ⟨177556765009960908096549893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118371176673307272064366595 177556765009960908096549893)
    ·
      refine ⟨33291893439367670268103105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177556765009960908096549893 33291893439367670268103105)
      ·
        refine ⟨24968920079525752701077329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33291893439367670268103105 24968920079525752701077329)
        ·
          refine ⟨18726690059644314525807997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24968920079525752701077329 18726690059644314525807997)
          ·
            refine ⟨7022508772366617947177999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18726690059644314525807997 7022508772366617947177999)
            ·
              refine ⟨10533763158549926920766999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022508772366617947177999 10533763158549926920766999)
              ·
                refine ⟨15800644737824890381150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10533763158549926920766999 15800644737824890381150499)
                ·
                  refine ⟨23700967106737335571725749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15800644737824890381150499 23700967106737335571725749)
                  ·
                    refine ⟨2221965666256625209849289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23700967106737335571725749 2221965666256625209849289)
                    ·
                      refine ⟨1666474249692468907386967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2221965666256625209849289 1666474249692468907386967)
                      ·
                        rfl

theorem cell23_3245447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 5, 2].length) (baseStart_3245447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245447 prefixEnd_3245447 := by exact prefixLift 3245447
  have htrace : WordTrace (prefixWord ++ tailWord_3245447) baseStart_3245447 baseEnd_3245447 := by
    simpa [prefixWord, tailWord_3245447, baseEnd_3245447] using wordTrace_append hprefix tailTrace_3245447
  have hstable : (prefixWord ++ tailWord_3245447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245447).length < 2 ^ (prefixWord ++ tailWord_3245447).sum := by decide
  have hdescent : baseEnd_3245447 < baseStart_3245447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245490 : List Nat := [3, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_3245490 : Nat := 118140960795 + 3245490 * 2 ^ 59
def prefixEnd_3245490 : Nat := 4983230072969 + 3 ^ 40 * 3245490 * 2
def baseEnd_3245490 : Nat := 1666496329360612239149269

theorem tailTrace_3245490 : CollatzResearch.WordTrace tailWord_3245490 prefixEnd_3245490 1666496329360612239149269 := by
  unfold tailWord_3245490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29593186253037872602045481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78915163341434326938787949 29593186253037872602045481)
  ·
    refine ⟨22194889689778404451534111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29593186253037872602045481 22194889689778404451534111)
    ·
      refine ⟨33292334534667606677301167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22194889689778404451534111 33292334534667606677301167)
      ·
        refine ⟨49938501802001410015951751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33292334534667606677301167 49938501802001410015951751)
        ·
          refine ⟨74907752703002115023927627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49938501802001410015951751 74907752703002115023927627)
          ·
            refine ⟨112361629054503172535891441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74907752703002115023927627 112361629054503172535891441)
            ·
              refine ⟨84271221790877379401918581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112361629054503172535891441 84271221790877379401918581)
              ·
                refine ⟨7900427042894754318929867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84271221790877379401918581 7900427042894754318929867)
                ·
                  refine ⟨11850640564342131478394801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7900427042894754318929867 11850640564342131478394801)
                  ·
                    refine ⟨8887980423256598608796101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11850640564342131478394801 8887980423256598608796101)
                    ·
                      refine ⟨1666496329360612239149269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8887980423256598608796101 1666496329360612239149269)
                      ·
                        rfl

theorem cell23_3245490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_3245490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245490 prefixEnd_3245490 := by exact prefixLift 3245490
  have htrace : WordTrace (prefixWord ++ tailWord_3245490) baseStart_3245490 baseEnd_3245490 := by
    simpa [prefixWord, tailWord_3245490, baseEnd_3245490] using wordTrace_append hprefix tailTrace_3245490
  have hstable : (prefixWord ++ tailWord_3245490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245490).length < 2 ^ (prefixWord ++ tailWord_3245490).sum := by decide
  have hdescent : baseEnd_3245490 < baseStart_3245490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245503 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3245503 : Nat := 118140960795 + 3245503 * 2 ^ 59
def prefixEnd_3245503 : Nat := 4983230072969 + 3 ^ 40 * 3245503 * 2
def baseEnd_3245503 : Nat := 1666503004609120688286709

theorem tailTrace_3245503 : CollatzResearch.WordTrace tailWord_3245503 prefixEnd_3245503 1666503004609120688286709 := by
  unfold tailWord_3245503
  simp only [CollatzResearch.WordTrace]
  refine ⟨118373219161104393628405163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78915479440736262418936775 118373219161104393628405163)
  ·
    refine ⟨177559828741656590442607745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118373219161104393628405163 177559828741656590442607745)
    ·
      refine ⟨133169871556242442831955809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177559828741656590442607745 133169871556242442831955809)
      ·
        refine ⟨99877403667181832123966857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133169871556242442831955809 99877403667181832123966857)
        ·
          refine ⟨74908052750386374092975143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99877403667181832123966857 74908052750386374092975143)
          ·
            refine ⟨112362079125579561139462715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74908052750386374092975143 112362079125579561139462715)
            ·
              refine ⟨168543118688369341709194073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112362079125579561139462715 168543118688369341709194073)
              ·
                refine ⟨126407339016277006281895555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168543118688369341709194073 126407339016277006281895555)
                ·
                  refine ⟨189611008524415509422843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126407339016277006281895555 189611008524415509422843333)
                  ·
                    refine ⟨35552064098327908016783125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189611008524415509422843333 35552064098327908016783125)
                    ·
                      refine ⟨1666503004609120688286709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35552064098327908016783125 1666503004609120688286709)
                      ·
                        rfl

theorem cell23_3245503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3245503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245503 prefixEnd_3245503 := by exact prefixLift 3245503
  have htrace : WordTrace (prefixWord ++ tailWord_3245503) baseStart_3245503 baseEnd_3245503 := by
    simpa [prefixWord, tailWord_3245503, baseEnd_3245503] using wordTrace_append hprefix tailTrace_3245503
  have hstable : (prefixWord ++ tailWord_3245503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245503).length < 2 ^ (prefixWord ++ tailWord_3245503).sum := by decide
  have hdescent : baseEnd_3245503 < baseStart_3245503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245513 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 1, 9]
def baseStart_3245513 : Nat := 118140960795 + 3245513 * 2 ^ 59
def prefixEnd_3245513 : Nat := 4983230072969 + 3 ^ 40 * 3245513 * 2
def baseEnd_3245513 : Nat := 555502713138555216387221

theorem tailTrace_3245513 : CollatzResearch.WordTrace tailWord_3245513 prefixEnd_3245513 555502713138555216387221 := by
  unfold tailWord_3245513
  simp only [CollatzResearch.WordTrace]
  refine ⟨118373583891068165336269193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78915722594045443557512795 118373583891068165336269193)
  ·
    refine ⟨88780187918301124002201895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118373583891068165336269193 88780187918301124002201895)
    ·
      refine ⟨133170281877451686003302843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88780187918301124002201895 133170281877451686003302843)
      ·
        refine ⟨199755422816177529004954265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133170281877451686003302843 199755422816177529004954265)
        ·
          refine ⟨149816567112133146753715699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199755422816177529004954265 149816567112133146753715699)
          ·
            refine ⟨224724850668199720130573549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149816567112133146753715699 224724850668199720130573549)
            ·
              refine ⟨84271819000574895048965081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224724850668199720130573549 84271819000574895048965081)
              ·
                refine ⟨63203864250431171286723811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84271819000574895048965081 63203864250431171286723811)
                ·
                  refine ⟨94805796375646756930085717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63203864250431171286723811 94805796375646756930085717)
                  ·
                    refine ⟨555502713138555216387221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94805796375646756930085717 555502713138555216387221)
                    ·
                      rfl

theorem cell23_3245513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_3245513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245513 prefixEnd_3245513 := by exact prefixLift 3245513
  have htrace : WordTrace (prefixWord ++ tailWord_3245513) baseStart_3245513 baseEnd_3245513 := by
    simpa [prefixWord, tailWord_3245513, baseEnd_3245513] using wordTrace_append hprefix tailTrace_3245513
  have hstable : (prefixWord ++ tailWord_3245513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245513).length < 2 ^ (prefixWord ++ tailWord_3245513).sum := by decide
  have hdescent : baseEnd_3245513 < baseStart_3245513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245544 : List Nat := [2, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_3245544 : Nat := 118140960795 + 3245544 * 2 ^ 59
def prefixEnd_3245544 : Nat := 4983230072969 + 3 ^ 40 * 3245544 * 2
def baseEnd_3245544 : Nat := 1666524057315955027874021

theorem tailTrace_3245544 : CollatzResearch.WordTrace tailWord_3245544 prefixEnd_3245544 1666524057315955027874021 := by
  unfold tailWord_3245544
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187357276977928815323843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78916476369303905087098457 59187357276977928815323843)
  ·
    refine ⟨88781035915466893222985765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59187357276977928815323843 88781035915466893222985765)
    ·
      refine ⟨16646444234150042479309831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88781035915466893222985765 16646444234150042479309831)
      ·
        refine ⟨24969666351225063718964747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16646444234150042479309831 24969666351225063718964747)
        ·
          refine ⟨37454499526837595578447121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24969666351225063718964747 37454499526837595578447121)
          ·
            refine ⟨28090874645128196683835341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37454499526837595578447121 28090874645128196683835341)
            ·
              refine ⟨10534077991923073756438253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28090874645128196683835341 10534077991923073756438253)
              ·
                refine ⟨3950279246971152658664345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10534077991923073756438253 3950279246971152658664345)
                ·
                  refine ⟨2962709435228364493998259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950279246971152658664345 2962709435228364493998259)
                  ·
                    refine ⟨4444064152842546740997389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2962709435228364493998259 4444064152842546740997389)
                    ·
                      refine ⟨1666524057315955027874021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4444064152842546740997389 1666524057315955027874021)
                      ·
                        rfl

theorem cell23_3245544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_3245544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245544 prefixEnd_3245544 := by exact prefixLift 3245544
  have htrace : WordTrace (prefixWord ++ tailWord_3245544) baseStart_3245544 baseEnd_3245544 := by
    simpa [prefixWord, tailWord_3245544, baseEnd_3245544] using wordTrace_append hprefix tailTrace_3245544
  have hstable : (prefixWord ++ tailWord_3245544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245544).length < 2 ^ (prefixWord ++ tailWord_3245544).sum := by decide
  have hdescent : baseEnd_3245544 < baseStart_3245544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245597 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3245597 : Nat := 118140960795 + 3245597 * 2 ^ 59
def prefixEnd_3245597 : Nat := 4983230072969 + 3 ^ 40 * 3245597 * 2
def baseEnd_3245597 : Nat := 1666551271790643320511277

theorem tailTrace_3245597 : CollatzResearch.WordTrace tailWord_3245597 prefixEnd_3245597 1666551271790643320511277 := by
  unfold tailWord_3245597
  simp only [CollatzResearch.WordTrace]
  refine ⟨118376647622763847682327045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78917765081842565121551363 118376647622763847682327045)
  ·
    refine ⟨22195621429268221440436321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118376647622763847682327045 22195621429268221440436321)
    ·
      refine ⟨16646716071951166080327241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22195621429268221440436321 16646716071951166080327241)
      ·
        refine ⟨12485037053963374560245431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16646716071951166080327241 12485037053963374560245431)
        ·
          refine ⟨18727555580945061840368147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485037053963374560245431 18727555580945061840368147)
          ·
            refine ⟨28091333371417592760552221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727555580945061840368147 28091333371417592760552221)
            ·
              refine ⟨10534250014281597285207083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28091333371417592760552221 10534250014281597285207083)
              ·
                refine ⟨15801375021422395927810625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10534250014281597285207083 15801375021422395927810625)
                ·
                  refine ⟨11851031266066796945857969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15801375021422395927810625 11851031266066796945857969)
                  ·
                    refine ⟨8888273449550097709393477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11851031266066796945857969 8888273449550097709393477)
                    ·
                      refine ⟨1666551271790643320511277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8888273449550097709393477 1666551271790643320511277)
                      ·
                        rfl

theorem cell23_3245597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3245597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245597 prefixEnd_3245597 := by exact prefixLift 3245597
  have htrace : WordTrace (prefixWord ++ tailWord_3245597) baseStart_3245597 baseEnd_3245597 := by
    simpa [prefixWord, tailWord_3245597, baseEnd_3245597] using wordTrace_append hprefix tailTrace_3245597
  have hstable : (prefixWord ++ tailWord_3245597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245597).length < 2 ^ (prefixWord ++ tailWord_3245597).sum := by decide
  have hdescent : baseEnd_3245597 < baseStart_3245597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245601 : List Nat := [1, 2, 3, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_3245601 : Nat := 118140960795 + 3245601 * 2 ^ 59
def prefixEnd_3245601 : Nat := 4983230072969 + 3 ^ 40 * 3245601 * 2
def baseEnd_3245601 : Nat := 1666553325713261304861259

theorem tailTrace_3245601 : CollatzResearch.WordTrace tailWord_3245601 prefixEnd_3245601 1666553325713261304861259 := by
  unfold tailWord_3245601
  simp only [CollatzResearch.WordTrace]
  refine ⟨118376793514749356365472657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78917862343166237576981771 118376793514749356365472657)
  ·
    refine ⟨88782595136062017274104493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118376793514749356365472657 88782595136062017274104493)
    ·
      refine ⟨33293473176023256477789185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88782595136062017274104493 33293473176023256477789185)
      ·
        refine ⟨24970104882017442358341889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33293473176023256477789185 24970104882017442358341889)
        ·
          refine ⟨18727578661513081768756417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24970104882017442358341889 18727578661513081768756417)
          ·
            refine ⟨14045683996134811326567313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18727578661513081768756417 14045683996134811326567313)
            ·
              refine ⟨10534262997101108494925485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14045683996134811326567313 10534262997101108494925485)
              ·
                refine ⟨3950348623912915685597057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10534262997101108494925485 3950348623912915685597057)
                ·
                  refine ⟨2962761467934686764197793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950348623912915685597057 2962761467934686764197793)
                  ·
                    refine ⟨2222071100951015073148345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2962761467934686764197793 2222071100951015073148345)
                    ·
                      refine ⟨1666553325713261304861259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222071100951015073148345 1666553325713261304861259)
                      ·
                        rfl

theorem cell23_3245601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_3245601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245601 prefixEnd_3245601 := by exact prefixLift 3245601
  have htrace : WordTrace (prefixWord ++ tailWord_3245601) baseStart_3245601 baseEnd_3245601 := by
    simpa [prefixWord, tailWord_3245601, baseEnd_3245601] using wordTrace_append hprefix tailTrace_3245601
  have hstable : (prefixWord ++ tailWord_3245601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245601).length < 2 ^ (prefixWord ++ tailWord_3245601).sum := by decide
  have hdescent : baseEnd_3245601 < baseStart_3245601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245622 : List Nat := [5, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_3245622 : Nat := 118140960795 + 3245622 * 2 ^ 59
def prefixEnd_3245622 : Nat := 4983230072969 + 3 ^ 40 * 3245622 * 2
def baseEnd_3245622 : Nat := 1666564108807005722698663

theorem tailTrace_3245622 : CollatzResearch.WordTrace tailWord_3245622 prefixEnd_3245622 1666564108807005722698663 := by
  unfold tailWord_3245622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398597465479579809499195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78918372965115517967991413 7398597465479579809499195)
  ·
    refine ⟨11097896198219369714248793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398597465479579809499195 11097896198219369714248793)
    ·
      refine ⟨8323422148664527285686595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11097896198219369714248793 8323422148664527285686595)
      ·
        refine ⟨12485133222996790928529893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323422148664527285686595 12485133222996790928529893)
        ·
          refine ⟨2340962479311898299099355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12485133222996790928529893 2340962479311898299099355)
          ·
            refine ⟨3511443718967847448649033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340962479311898299099355 3511443718967847448649033)
            ·
              refine ⟨2633582789225885586486775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511443718967847448649033 2633582789225885586486775)
              ·
                refine ⟨3950374183838828379730163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633582789225885586486775 3950374183838828379730163)
                ·
                  refine ⟨5925561275758242569595245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950374183838828379730163 5925561275758242569595245)
                  ·
                    refine ⟨2222085478409340963598217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5925561275758242569595245 2222085478409340963598217)
                    ·
                      refine ⟨1666564108807005722698663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222085478409340963598217 1666564108807005722698663)
                      ·
                        rfl

theorem cell23_3245622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_3245622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245622 prefixEnd_3245622 := by exact prefixLift 3245622
  have htrace : WordTrace (prefixWord ++ tailWord_3245622) baseStart_3245622 baseEnd_3245622 := by
    simpa [prefixWord, tailWord_3245622, baseEnd_3245622] using wordTrace_append hprefix tailTrace_3245622
  have hstable : (prefixWord ++ tailWord_3245622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245622).length < 2 ^ (prefixWord ++ tailWord_3245622).sum := by decide
  have hdescent : baseEnd_3245622 < baseStart_3245622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245624 : List Nat := [2, 1, 2, 1, 4, 3, 2, 3, 5]
def baseStart_3245624 : Nat := 118140960795 + 3245624 * 2 ^ 59
def prefixEnd_3245624 : Nat := 4983230072969 + 3 ^ 40 * 3245624 * 2
def baseEnd_3245624 : Nat := 185173903974257190541517

theorem tailTrace_3245624 : CollatzResearch.WordTrace tailWord_3245624 prefixEnd_3245624 185173903974257190541517 := by
  unfold tailWord_3245624
  simp only [CollatzResearch.WordTrace]
  refine ⟨59188816196833015646779963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78918421595777354195706617 59188816196833015646779963)
  ·
    refine ⟨88783224295249523470169945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59188816196833015646779963 88783224295249523470169945)
    ·
      refine ⟨66587418221437142602627459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88783224295249523470169945 66587418221437142602627459)
      ·
        refine ⟨99881127332155713903941189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66587418221437142602627459 99881127332155713903941189)
        ·
          refine ⟨18727711374779196356988973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99881127332155713903941189 18727711374779196356988973)
          ·
            refine ⟨7022891765542198633870865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18727711374779196356988973 7022891765542198633870865)
            ·
              refine ⟨5267168824156648975403149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7022891765542198633870865 5267168824156648975403149)
              ·
                refine ⟨1975188309058743365776181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5267168824156648975403149 1975188309058743365776181)
                ·
                  refine ⟨185173903974257190541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1975188309058743365776181 185173903974257190541517)
                  ·
                    rfl

theorem cell23_3245624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 3, 5].length) (baseStart_3245624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245624 prefixEnd_3245624 := by exact prefixLift 3245624
  have htrace : WordTrace (prefixWord ++ tailWord_3245624) baseStart_3245624 baseEnd_3245624 := by
    simpa [prefixWord, tailWord_3245624, baseEnd_3245624] using wordTrace_append hprefix tailTrace_3245624
  have hstable : (prefixWord ++ tailWord_3245624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245624).length < 2 ^ (prefixWord ++ tailWord_3245624).sum := by decide
  have hdescent : baseEnd_3245624 < baseStart_3245624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245697 : List Nat := [1, 2, 4, 2, 1, 2, 2, 1, 8]
def baseStart_3245697 : Nat := 118140960795 + 3245697 * 2 ^ 59
def prefixEnd_3245697 : Nat := 4983230072969 + 3 ^ 40 * 3245697 * 2
def baseEnd_3245697 : Nat := 185178068872899214362313

theorem tailTrace_3245697 : CollatzResearch.WordTrace tailWord_3245697 prefixEnd_3245697 185178068872899214362313 := by
  unfold tailWord_3245697
  simp only [CollatzResearch.WordTrace]
  refine ⟨118380294922401564760967345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78920196614934376507311563 118380294922401564760967345)
  ·
    refine ⟨88785221191801173570725509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118380294922401564760967345 88785221191801173570725509)
    ·
      refine ⟨16647228973462720044511033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88785221191801173570725509 16647228973462720044511033)
      ·
        refine ⟨12485421730097040033383275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16647228973462720044511033 12485421730097040033383275)
        ·
          refine ⟨18728132595145560050074913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485421730097040033383275 18728132595145560050074913)
          ·
            refine ⟨14046099446359170037556185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18728132595145560050074913 14046099446359170037556185)
            ·
              refine ⟨10534574584769377528167139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14046099446359170037556185 10534574584769377528167139)
              ·
                refine ⟨15801861877154066292250709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10534574584769377528167139 15801861877154066292250709)
                ·
                  refine ⟨185178068872899214362313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15801861877154066292250709 185178068872899214362313)
                  ·
                    rfl

theorem cell23_3245697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 8].length) (baseStart_3245697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245697 prefixEnd_3245697 := by exact prefixLift 3245697
  have htrace : WordTrace (prefixWord ++ tailWord_3245697) baseStart_3245697 baseEnd_3245697 := by
    simpa [prefixWord, tailWord_3245697, baseEnd_3245697] using wordTrace_append hprefix tailTrace_3245697
  have hstable : (prefixWord ++ tailWord_3245697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245697).length < 2 ^ (prefixWord ++ tailWord_3245697).sum := by decide
  have hdescent : baseEnd_3245697 < baseStart_3245697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245751 : List Nat := [1, 1, 3, 1, 5, 1, 2, 2, 2, 3, 2]
def baseStart_3245751 : Nat := 118140960795 + 3245751 * 2 ^ 59
def prefixEnd_3245751 : Nat := 4983230072969 + 3 ^ 40 * 3245751 * 2
def baseEnd_3245751 : Nat := 1666630347811435717985569

theorem tailTrace_3245751 : CollatzResearch.WordTrace tailWord_3245751 prefixEnd_3245751 1666630347811435717985569 := by
  unfold tailWord_3245751
  simp only [CollatzResearch.WordTrace]
  refine ⟨118382264464205931983433107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78921509642803954655622071 118382264464205931983433107)
  ·
    refine ⟨177573396696308897975149661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118382264464205931983433107 177573396696308897975149661)
    ·
      refine ⟨66590023761115836740681123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177573396696308897975149661 66590023761115836740681123)
      ·
        refine ⟨99885035641673755111021685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66590023761115836740681123 99885035641673755111021685)
        ·
          refine ⟨9364222091406914541658283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99885035641673755111021685 9364222091406914541658283)
          ·
            refine ⟨14046333137110371812487425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364222091406914541658283 14046333137110371812487425)
            ·
              refine ⟨10534749852832778859365569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14046333137110371812487425 10534749852832778859365569)
              ·
                refine ⟨7901062389624584144524177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10534749852832778859365569 7901062389624584144524177)
                ·
                  refine ⟨5925796792218438108393133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7901062389624584144524177 5925796792218438108393133)
                  ·
                    refine ⟨2222173797081914290647425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5925796792218438108393133 2222173797081914290647425)
                    ·
                      refine ⟨1666630347811435717985569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222173797081914290647425 1666630347811435717985569)
                      ·
                        rfl

theorem cell23_3245751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 2, 2, 3, 2].length) (baseStart_3245751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245751 prefixEnd_3245751 := by exact prefixLift 3245751
  have htrace : WordTrace (prefixWord ++ tailWord_3245751) baseStart_3245751 baseEnd_3245751 := by
    simpa [prefixWord, tailWord_3245751, baseEnd_3245751] using wordTrace_append hprefix tailTrace_3245751
  have hstable : (prefixWord ++ tailWord_3245751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245751).length < 2 ^ (prefixWord ++ tailWord_3245751).sum := by decide
  have hdescent : baseEnd_3245751 < baseStart_3245751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245757 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 3, 6]
def baseStart_3245757 : Nat := 118140960795 + 3245757 * 2 ^ 59
def prefixEnd_3245757 : Nat := 4983230072969 + 3 ^ 40 * 3245757 * 2
def baseEnd_3245757 : Nat := 555544476231787564836847

theorem tailTrace_3245757 : CollatzResearch.WordTrace tailWord_3245757 prefixEnd_3245757 555544476231787564836847 := by
  unfold tailWord_3245757
  simp only [CollatzResearch.WordTrace]
  refine ⟨118382483302184195008151525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78921655534789463338767683 118382483302184195008151525)
  ·
    refine ⟨22196715619159536564028411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118382483302184195008151525 22196715619159536564028411)
    ·
      refine ⟨33295073428739304846042617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22196715619159536564028411 33295073428739304846042617)
      ·
        refine ⟨24971305071554478634531963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33295073428739304846042617 24971305071554478634531963)
        ·
          refine ⟨37456957607331717951797945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24971305071554478634531963 37456957607331717951797945)
          ·
            refine ⟨28092718205498788463848459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37456957607331717951797945 28092718205498788463848459)
            ·
              refine ⟨42139077308248182695772689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28092718205498788463848459 42139077308248182695772689)
              ·
                refine ⟨31604307981186137021829517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42139077308248182695772689 31604307981186137021829517)
                ·
                  refine ⟨11851615492944801383186069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31604307981186137021829517 11851615492944801383186069)
                  ·
                    refine ⟨555544476231787564836847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11851615492944801383186069 555544476231787564836847)
                    ·
                      rfl

theorem cell23_3245757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_3245757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245757 prefixEnd_3245757 := by exact prefixLift 3245757
  have htrace : WordTrace (prefixWord ++ tailWord_3245757) baseStart_3245757 baseEnd_3245757 := by
    simpa [prefixWord, tailWord_3245757, baseEnd_3245757] using wordTrace_append hprefix tailTrace_3245757
  have hstable : (prefixWord ++ tailWord_3245757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245757).length < 2 ^ (prefixWord ++ tailWord_3245757).sum := by decide
  have hdescent : baseEnd_3245757 < baseStart_3245757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245764 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_3245764 : Nat := 118140960795 + 3245764 * 2 ^ 59
def prefixEnd_3245764 : Nat := 4983230072969 + 3 ^ 40 * 3245764 * 2
def baseEnd_3245764 : Nat := 1666637023059944167123009

theorem tailTrace_3245764 : CollatzResearch.WordTrace tailWord_3245764 prefixEnd_3245764 1666637023059944167123009 := by
  unfold tailWord_3245764
  simp only [CollatzResearch.WordTrace]
  refine ⟨59191369306579417601828173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78921825742105890135770897 59191369306579417601828173)
  ·
    refine ⟨22196763489967281600685565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59191369306579417601828173 22196763489967281600685565)
    ·
      refine ⟨8323786308737730600257087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22196763489967281600685565 8323786308737730600257087)
      ·
        refine ⟨12485679463106595900385631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323786308737730600257087 12485679463106595900385631)
        ·
          refine ⟨18728519194659893850578447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485679463106595900385631 18728519194659893850578447)
          ·
            refine ⟨28092778791989840775867671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18728519194659893850578447 28092778791989840775867671)
            ·
              refine ⟨42139168187984761163801507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28092778791989840775867671 42139168187984761163801507)
              ·
                refine ⟨63208752281977141745702261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42139168187984761163801507 63208752281977141745702261)
                ·
                  refine ⟨5925820526435357038659587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63208752281977141745702261 5925820526435357038659587)
                  ·
                    refine ⟨8888730789653035557989381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5925820526435357038659587 8888730789653035557989381)
                    ·
                      refine ⟨1666637023059944167123009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8888730789653035557989381 1666637023059944167123009)
                      ·
                        rfl

theorem cell23_3245764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_3245764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245764 prefixEnd_3245764 := by exact prefixLift 3245764
  have htrace : WordTrace (prefixWord ++ tailWord_3245764) baseStart_3245764 baseEnd_3245764 := by
    simpa [prefixWord, tailWord_3245764, baseEnd_3245764] using wordTrace_append hprefix tailTrace_3245764
  have hstable : (prefixWord ++ tailWord_3245764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245764).length < 2 ^ (prefixWord ++ tailWord_3245764).sum := by decide
  have hdescent : baseEnd_3245764 < baseStart_3245764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245767 : List Nat := [1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5]
def baseStart_3245767 : Nat := 118140960795 + 3245767 * 2 ^ 59
def prefixEnd_3245767 : Nat := 4983230072969 + 3 ^ 40 * 3245767 * 2
def baseEnd_3245767 : Nat := 1666638563501907655385495

theorem tailTrace_3245767 : CollatzResearch.WordTrace tailWord_3245767 prefixEnd_3245767 1666638563501907655385495 := by
  unfold tailWord_3245767
  simp only [CollatzResearch.WordTrace]
  refine ⟨118382848032147966716015555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78921898688098644477343703 118382848032147966716015555)
  ·
    refine ⟨177574272048221950074023333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118382848032147966716015555 177574272048221950074023333)
    ·
      refine ⟨33295176009041615638879375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177574272048221950074023333 33295176009041615638879375)
      ·
        refine ⟨49942764013562423458319063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33295176009041615638879375 49942764013562423458319063)
        ·
          refine ⟨74914146020343635187478595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49942764013562423458319063 74914146020343635187478595)
          ·
            refine ⟨112371219030515452781217893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74914146020343635187478595 112371219030515452781217893)
            ·
              refine ⟨21069603568221647396478355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112371219030515452781217893 21069603568221647396478355)
              ·
                refine ⟨31604405352332471094717533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21069603568221647396478355 31604405352332471094717533)
                ·
                  refine ⟨11851652007124676660519075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31604405352332471094717533 11851652007124676660519075)
                  ·
                    refine ⟨17777478010687014990778613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11851652007124676660519075 17777478010687014990778613)
                    ·
                      refine ⟨1666638563501907655385495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17777478010687014990778613 1666638563501907655385495)
                      ·
                        rfl

theorem cell23_3245767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 5].length) (baseStart_3245767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245767 prefixEnd_3245767 := by exact prefixLift 3245767
  have htrace : WordTrace (prefixWord ++ tailWord_3245767) baseStart_3245767 baseEnd_3245767 := by
    simpa [prefixWord, tailWord_3245767, baseEnd_3245767] using wordTrace_append hprefix tailTrace_3245767
  have hstable : (prefixWord ++ tailWord_3245767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245767).length < 2 ^ (prefixWord ++ tailWord_3245767).sum := by decide
  have hdescent : baseEnd_3245767 < baseStart_3245767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245774 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 1, 6]
def baseStart_3245774 : Nat := 118140960795 + 3245774 * 2 ^ 59
def prefixEnd_3245774 : Nat := 4983230072969 + 3 ^ 40 * 3245774 * 2
def baseEnd_3245774 : Nat := 555547385955496375999321

theorem tailTrace_3245774 : CollatzResearch.WordTrace tailWord_3245774 prefixEnd_3245774 555547385955496375999321 := by
  unfold tailWord_3245774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797887917890325863940047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78922068895415071274346917 14797887917890325863940047)
  ·
    refine ⟨22196831876835488795910071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14797887917890325863940047 22196831876835488795910071)
    ·
      refine ⟨33295247815253233193865107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22196831876835488795910071 33295247815253233193865107)
      ·
        refine ⟨49942871722879849790797661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33295247815253233193865107 49942871722879849790797661)
        ·
          refine ⟨18728576896079943671549123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49942871722879849790797661 18728576896079943671549123)
          ·
            refine ⟨28092865344119915507323685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18728576896079943671549123 28092865344119915507323685)
            ·
              refine ⟨5267412252022484157623191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28092865344119915507323685 5267412252022484157623191)
              ·
                refine ⟨7901118378033726236434787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267412252022484157623191 7901118378033726236434787)
                ·
                  refine ⟨11851677567050589354652181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901118378033726236434787 11851677567050589354652181)
                  ·
                    refine ⟨555547385955496375999321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11851677567050589354652181 555547385955496375999321)
                    ·
                      rfl

theorem cell23_3245774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_3245774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245774 prefixEnd_3245774 := by exact prefixLift 3245774
  have htrace : WordTrace (prefixWord ++ tailWord_3245774) baseStart_3245774 baseEnd_3245774 := by
    simpa [prefixWord, tailWord_3245774, baseEnd_3245774] using wordTrace_append hprefix tailTrace_3245774
  have hstable : (prefixWord ++ tailWord_3245774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245774).length < 2 ^ (prefixWord ++ tailWord_3245774).sum := by decide
  have hdescent : baseEnd_3245774 < baseStart_3245774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245784 : List Nat := [2, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3]
def baseStart_3245784 : Nat := 118140960795 + 3245784 * 2 ^ 59
def prefixEnd_3245784 : Nat := 4983230072969 + 3 ^ 40 * 3245784 * 2
def baseEnd_3245784 : Nat := 1666647292673034088872917

theorem tailTrace_3245784 : CollatzResearch.WordTrace tailWord_3245784 prefixEnd_3245784 1666647292673034088872917 := by
  unfold tailWord_3245784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59191734036543189309692203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78922312048724252412922937 59191734036543189309692203)
  ·
    refine ⟨88787601054814783964538305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59191734036543189309692203 88787601054814783964538305)
    ·
      refine ⟨66590700791111087973403729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88787601054814783964538305 66590700791111087973403729)
      ·
        refine ⟨49943025593333315980052797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66590700791111087973403729 49943025593333315980052797)
        ·
          refine ⟨18728634597499993492519799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49943025593333315980052797 18728634597499993492519799)
          ·
            refine ⟨28092951896249990238779699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18728634597499993492519799 28092951896249990238779699)
            ·
              refine ⟨42139427844374985358169549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28092951896249990238779699 42139427844374985358169549)
              ·
                refine ⟨15802285441640619509313581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42139427844374985358169549 15802285441640619509313581)
                ·
                  refine ⟨5925857040615232315992593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15802285441640619509313581 5925857040615232315992593)
                  ·
                    refine ⟨4444392780461424236994445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5925857040615232315992593 4444392780461424236994445)
                    ·
                      refine ⟨1666647292673034088872917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4444392780461424236994445 1666647292673034088872917)
                      ·
                        rfl

theorem cell23_3245784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_3245784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245784 prefixEnd_3245784 := by exact prefixLift 3245784
  have htrace : WordTrace (prefixWord ++ tailWord_3245784) baseStart_3245784 baseEnd_3245784 := by
    simpa [prefixWord, tailWord_3245784, baseEnd_3245784] using wordTrace_append hprefix tailTrace_3245784
  have hstable : (prefixWord ++ tailWord_3245784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245784).length < 2 ^ (prefixWord ++ tailWord_3245784).sum := by decide
  have hdescent : baseEnd_3245784 < baseStart_3245784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245795 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 1, 5]
def baseStart_3245795 : Nat := 118140960795 + 3245795 * 2 ^ 59
def prefixEnd_3245795 : Nat := 4983230072969 + 3 ^ 40 * 3245795 * 2
def baseEnd_3245795 : Nat := 555550980320077848611789

theorem tailTrace_3245795 : CollatzResearch.WordTrace tailWord_3245795 prefixEnd_3245795 555550980320077848611789 := by
  unfold tailWord_3245795
  simp only [CollatzResearch.WordTrace]
  refine ⟨118383869276046527498034839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78922579517364351665356559 118383869276046527498034839)
  ·
    refine ⟨177575803914069791247052259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118383869276046527498034839 177575803914069791247052259)
    ·
      refine ⟨266363705871104686870578389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177575803914069791247052259 266363705871104686870578389)
      ·
        refine ⟨6242899356354016098529181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 266363705871104686870578389 6242899356354016098529181)
        ·
          refine ⟨2341087258632756036948443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6242899356354016098529181 2341087258632756036948443)
          ·
            refine ⟨3511630887949134055422665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341087258632756036948443 3511630887949134055422665)
            ·
              refine ⟨2633723165961850541566999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511630887949134055422665 2633723165961850541566999)
              ·
                refine ⟨3950584748942775812350499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633723165961850541566999 3950584748942775812350499)
                ·
                  refine ⟨5925877123414163718525749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950584748942775812350499 5925877123414163718525749)
                  ·
                    refine ⟨555550980320077848611789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5925877123414163718525749 555550980320077848611789)
                    ·
                      rfl

theorem cell23_3245795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 5].length) (baseStart_3245795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245795 prefixEnd_3245795 := by exact prefixLift 3245795
  have htrace : WordTrace (prefixWord ++ tailWord_3245795) baseStart_3245795 baseEnd_3245795 := by
    simpa [prefixWord, tailWord_3245795, baseEnd_3245795] using wordTrace_append hprefix tailTrace_3245795
  have hstable : (prefixWord ++ tailWord_3245795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245795).length < 2 ^ (prefixWord ++ tailWord_3245795).sum := by decide
  have hdescent : baseEnd_3245795 < baseStart_3245795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245858 : List Nat := [3, 3, 1, 1, 2, 1, 1, 5, 1, 3, 2]
def baseStart_3245858 : Nat := 118140960795 + 3245858 * 2 ^ 59
def prefixEnd_3245858 : Nat := 4983230072969 + 3 ^ 40 * 3245858 * 2
def baseEnd_3245858 : Nat := 1666685290241466799347577

theorem tailTrace_3245858 : CollatzResearch.WordTrace tailWord_3245858 prefixEnd_3245858 1666685290241466799347577 := by
  unfold tailWord_3245858
  simp only [CollatzResearch.WordTrace]
  refine ⟨29596541768704572314394557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78924111383212192838385485 29596541768704572314394557)
  ·
    refine ⟨11098703163264214617897959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29596541768704572314394557 11098703163264214617897959)
    ·
      refine ⟨16648054744896321926846939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11098703163264214617897959 16648054744896321926846939)
      ·
        refine ⟨24972082117344482890270409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16648054744896321926846939 24972082117344482890270409)
        ·
          refine ⟨18729061588008362167702807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24972082117344482890270409 18729061588008362167702807)
          ·
            refine ⟨28093592382012543251554211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18729061588008362167702807 28093592382012543251554211)
            ·
              refine ⟨42140388573018814877331317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28093592382012543251554211 42140388573018814877331317)
              ·
                refine ⟨3950661428720513894749811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42140388573018814877331317 3950661428720513894749811)
                ·
                  refine ⟨5925992143080770842124717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950661428720513894749811 5925992143080770842124717)
                  ·
                    refine ⟨2222247053655289065796769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5925992143080770842124717 2222247053655289065796769)
                    ·
                      refine ⟨1666685290241466799347577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222247053655289065796769 1666685290241466799347577)
                      ·
                        rfl

theorem cell23_3245858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_3245858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245858 prefixEnd_3245858 := by exact prefixLift 3245858
  have htrace : WordTrace (prefixWord ++ tailWord_3245858) baseStart_3245858 baseEnd_3245858 := by
    simpa [prefixWord, tailWord_3245858, baseEnd_3245858] using wordTrace_append hprefix tailTrace_3245858
  have hstable : (prefixWord ++ tailWord_3245858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245858).length < 2 ^ (prefixWord ++ tailWord_3245858).sum := by decide
  have hdescent : baseEnd_3245858 < baseStart_3245858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245884 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3245884 : Nat := 118140960795 + 3245884 * 2 ^ 59
def prefixEnd_3245884 : Nat := 4983230072969 + 3 ^ 40 * 3245884 * 2
def baseEnd_3245884 : Nat := 1666698640738483697622457

theorem tailTrace_3245884 : CollatzResearch.WordTrace tailWord_3245884 prefixEnd_3245884 1666698640738483697622457 := by
  unfold tailWord_3245884
  simp only [CollatzResearch.WordTrace]
  refine ⟨59193557686362047849012353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78924743581816063798683137 59193557686362047849012353)
  ·
    refine ⟨44395168264771535886759265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59193557686362047849012353 44395168264771535886759265)
    ·
      refine ⟨33296376198578651915069449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44395168264771535886759265 33296376198578651915069449)
      ·
        refine ⟨24972282148933988936302087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33296376198578651915069449 24972282148933988936302087)
        ·
          refine ⟨37458423223400983404453131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24972282148933988936302087 37458423223400983404453131)
          ·
            refine ⟨56187634835101475106679697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37458423223400983404453131 56187634835101475106679697)
            ·
              refine ⟨42140726126326106330009773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56187634835101475106679697 42140726126326106330009773)
              ·
                refine ⟨15802772297372289873753665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42140726126326106330009773 15802772297372289873753665)
                ·
                  refine ⟨11852079223029217405315249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15802772297372289873753665 11852079223029217405315249)
                  ·
                    refine ⟨8889059417271913053986437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11852079223029217405315249 8889059417271913053986437)
                    ·
                      refine ⟨1666698640738483697622457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8889059417271913053986437 1666698640738483697622457)
                      ·
                        rfl

theorem cell23_3245884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3245884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245884 prefixEnd_3245884 := by exact prefixLift 3245884
  have htrace : WordTrace (prefixWord ++ tailWord_3245884) baseStart_3245884 baseEnd_3245884 := by
    simpa [prefixWord, tailWord_3245884, baseEnd_3245884] using wordTrace_append hprefix tailTrace_3245884
  have hstable : (prefixWord ++ tailWord_3245884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245884).length < 2 ^ (prefixWord ++ tailWord_3245884).sum := by decide
  have hdescent : baseEnd_3245884 < baseStart_3245884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245904 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3]
def baseStart_3245904 : Nat := 118140960795 + 3245904 * 2 ^ 59
def prefixEnd_3245904 : Nat := 4983230072969 + 3 ^ 40 * 3245904 * 2
def baseEnd_3245904 : Nat := 1666708910351573619372365

theorem tailTrace_3245904 : CollatzResearch.WordTrace tailWord_3245904 prefixEnd_3245904 1666708910351573619372365 := by
  unfold tailWord_3245904
  simp only [CollatzResearch.WordTrace]
  refine ⟨59193922416325819556876383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78925229888434426075835177 59193922416325819556876383)
  ·
    refine ⟨88790883624488729335314575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59193922416325819556876383 88790883624488729335314575)
    ·
      refine ⟨133186325436733094002971863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88790883624488729335314575 133186325436733094002971863)
      ·
        refine ⟨199779488155099641004457795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133186325436733094002971863 199779488155099641004457795)
        ·
          refine ⟨299669232232649461506686693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199779488155099641004457795 299669232232649461506686693)
          ·
            refine ⟨56187981043621774032503755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299669232232649461506686693 56187981043621774032503755)
            ·
              refine ⟨84281971565432661048755633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56187981043621774032503755 84281971565432661048755633)
              ·
                refine ⟨63211478674074495786566725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84281971565432661048755633 63211478674074495786566725)
                ·
                  refine ⟨11852152251388967959981261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63211478674074495786566725 11852152251388967959981261)
                  ·
                    refine ⟨4444557094270862984992973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11852152251388967959981261 4444557094270862984992973)
                    ·
                      refine ⟨1666708910351573619372365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4444557094270862984992973 1666708910351573619372365)
                      ·
                        rfl

theorem cell23_3245904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3].length) (baseStart_3245904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245904 prefixEnd_3245904 := by exact prefixLift 3245904
  have htrace : WordTrace (prefixWord ++ tailWord_3245904) baseStart_3245904 baseEnd_3245904 := by
    simpa [prefixWord, tailWord_3245904, baseEnd_3245904] using wordTrace_append hprefix tailTrace_3245904
  have hstable : (prefixWord ++ tailWord_3245904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245904).length < 2 ^ (prefixWord ++ tailWord_3245904).sum := by decide
  have hdescent : baseEnd_3245904 < baseStart_3245904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245922 : List Nat := [3, 3, 2, 1, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3245922 : Nat := 118140960795 + 3245922 * 2 ^ 59
def prefixEnd_3245922 : Nat := 4983230072969 + 3 ^ 40 * 3245922 * 2
def baseEnd_3245922 : Nat := 1666718153003354548947283

theorem tailTrace_3245922 : CollatzResearch.WordTrace tailWord_3245922 prefixEnd_3245922 1666718153003354548947283 := by
  unfold tailWord_3245922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29597125336646607046977005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78925667564390952125272013 29597125336646607046977005)
  ·
    refine ⟨11098922001242477642616377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29597125336646607046977005 11098922001242477642616377)
    ·
      refine ⟨8324191500931858231962283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11098922001242477642616377 8324191500931858231962283)
      ·
        refine ⟨12486287251397787347943425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8324191500931858231962283 12486287251397787347943425)
        ·
          refine ⟨9364715438548340510957569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12486287251397787347943425 9364715438548340510957569)
          ·
            refine ⟨7023536578911255383218177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9364715438548340510957569 7023536578911255383218177)
            ·
              refine ⟨5267652434183441537413633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7023536578911255383218177 5267652434183441537413633)
              ·
                refine ⟨3950739325637581153060225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267652434183441537413633 3950739325637581153060225)
                ·
                  refine ⟨2963054494228185864795169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950739325637581153060225 2963054494228185864795169)
                  ·
                    refine ⟨2222290870671139398596377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963054494228185864795169 2222290870671139398596377)
                    ·
                      refine ⟨1666718153003354548947283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222290870671139398596377 1666718153003354548947283)
                      ·
                        rfl

theorem cell23_3245922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3245922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245922 prefixEnd_3245922 := by exact prefixLift 3245922
  have htrace : WordTrace (prefixWord ++ tailWord_3245922) baseStart_3245922 baseEnd_3245922 := by
    simpa [prefixWord, tailWord_3245922, baseEnd_3245922] using wordTrace_append hprefix tailTrace_3245922
  have hstable : (prefixWord ++ tailWord_3245922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245922).length < 2 ^ (prefixWord ++ tailWord_3245922).sum := by decide
  have hdescent : baseEnd_3245922 < baseStart_3245922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245961 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 1, 6, 2]
def baseStart_3245961 : Nat := 118140960795 + 3245961 * 2 ^ 59
def prefixEnd_3245961 : Nat := 4983230072969 + 3 ^ 40 * 3245961 * 2
def baseEnd_3245961 : Nat := 1666738178748879896359603

theorem tailTrace_3245961 : CollatzResearch.WordTrace tailWord_3245961 prefixEnd_3245961 1666738178748879896359603 := by
  unfold tailWord_3245961
  simp only [CollatzResearch.WordTrace]
  refine ⟨118389923793445137848577737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78926615862296758565718491 118389923793445137848577737)
  ·
    refine ⟨88792442845083853386433303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118389923793445137848577737 88792442845083853386433303)
    ·
      refine ⟨133188664267625780079649955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88792442845083853386433303 133188664267625780079649955)
      ·
        refine ⟨199782996401438670119474933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133188664267625780079649955 199782996401438670119474933)
        ·
          refine ⟨18729655912634875323700775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199782996401438670119474933 18729655912634875323700775)
          ·
            refine ⟨28094483868952312985551163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18729655912634875323700775 28094483868952312985551163)
            ·
              refine ⟨42141725803428469478326745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28094483868952312985551163 42141725803428469478326745)
              ·
                refine ⟨31606294352571352108745059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42141725803428469478326745 31606294352571352108745059)
                ·
                  refine ⟨47409441528857028163117589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31606294352571352108745059 47409441528857028163117589)
                  ·
                    refine ⟨2222317571665173195146137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47409441528857028163117589 2222317571665173195146137)
                    ·
                      refine ⟨1666738178748879896359603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222317571665173195146137 1666738178748879896359603)
                      ·
                        rfl

theorem cell23_3245961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 6, 2].length) (baseStart_3245961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245961 prefixEnd_3245961 := by exact prefixLift 3245961
  have htrace : WordTrace (prefixWord ++ tailWord_3245961) baseStart_3245961 baseEnd_3245961 := by
    simpa [prefixWord, tailWord_3245961, baseEnd_3245961] using wordTrace_append hprefix tailTrace_3245961
  have hstable : (prefixWord ++ tailWord_3245961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245961).length < 2 ^ (prefixWord ++ tailWord_3245961).sum := by decide
  have hdescent : baseEnd_3245961 < baseStart_3245961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245978 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_3245978 : Nat := 118140960795 + 3245978 * 2 ^ 59
def prefixEnd_3245978 : Nat := 4983230072969 + 3 ^ 40 * 3245978 * 2
def baseEnd_3245978 : Nat := 1666746907920006329847025

theorem tailTrace_3245978 : CollatzResearch.WordTrace tailWord_3245978 prefixEnd_3245978 1666746907920006329847025 := by
  unfold tailWord_3245978
  simp only [CollatzResearch.WordTrace]
  refine ⟨29597635958595887437986647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78927029222922366501297725 29597635958595887437986647)
  ·
    refine ⟨44396453937893831156979971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29597635958595887437986647 44396453937893831156979971)
    ·
      refine ⟨66594680906840746735469957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44396453937893831156979971 66594680906840746735469957)
      ·
        refine ⟨12486502670032640012900617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66594680906840746735469957 12486502670032640012900617)
        ·
          refine ⟨9364877002524480009675463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12486502670032640012900617 9364877002524480009675463)
          ·
            refine ⟨14047315503786720014513195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364877002524480009675463 14047315503786720014513195)
            ·
              refine ⟨21070973255680080021769793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14047315503786720014513195 21070973255680080021769793)
              ·
                refine ⟨15803229941760060016327345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21070973255680080021769793 15803229941760060016327345)
                ·
                  refine ⟨11852422456320045012245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15803229941760060016327345 11852422456320045012245509)
                  ·
                    refine ⟨2222329210560008439796033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11852422456320045012245509 2222329210560008439796033)
                    ·
                      refine ⟨1666746907920006329847025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222329210560008439796033 1666746907920006329847025)
                      ·
                        rfl

theorem cell23_3245978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_3245978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245978 prefixEnd_3245978 := by exact prefixLift 3245978
  have htrace : WordTrace (prefixWord ++ tailWord_3245978) baseStart_3245978 baseEnd_3245978 := by
    simpa [prefixWord, tailWord_3245978, baseEnd_3245978] using wordTrace_append hprefix tailTrace_3245978
  have hstable : (prefixWord ++ tailWord_3245978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245978).length < 2 ^ (prefixWord ++ tailWord_3245978).sum := by decide
  have hdescent : baseEnd_3245978 < baseStart_3245978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245988 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 3, 4]
def baseStart_3245988 : Nat := 118140960795 + 3245988 * 2 ^ 59
def prefixEnd_3245988 : Nat := 4983230072969 + 3 ^ 40 * 3245988 * 2
def baseEnd_3245988 : Nat := 555584014242183763573993

theorem tailTrace_3245988 : CollatzResearch.WordTrace tailWord_3245988 prefixEnd_3245988 555584014242183763573993 := by
  unfold tailWord_3245988
  simp only [CollatzResearch.WordTrace]
  refine ⟨59195454282173660729905309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78927272376231547639873745 59195454282173660729905309)
  ·
    refine ⟨22198295355815122773714491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59195454282173660729905309 22198295355815122773714491)
    ·
      refine ⟨33297443033722684160571737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22198295355815122773714491 33297443033722684160571737)
      ·
        refine ⟨24973082275292013120428803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33297443033722684160571737 24973082275292013120428803)
        ·
          refine ⟨37459623412938019680643205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24973082275292013120428803 37459623412938019680643205)
          ·
            refine ⟨7023679389925878690120601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37459623412938019680643205 7023679389925878690120601)
            ·
              refine ⟨5267759542444409017590451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7023679389925878690120601 5267759542444409017590451)
              ·
                refine ⟨7901639313666613526385677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267759542444409017590451 7901639313666613526385677)
                ·
                  refine ⟨2963114742624980072394629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7901639313666613526385677 2963114742624980072394629)
                  ·
                    refine ⟨555584014242183763573993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963114742624980072394629 555584014242183763573993)
                    ·
                      rfl

theorem cell23_3245988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_3245988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3245988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3245988 prefixEnd_3245988 := by exact prefixLift 3245988
  have htrace : WordTrace (prefixWord ++ tailWord_3245988) baseStart_3245988 baseEnd_3245988 := by
    simpa [prefixWord, tailWord_3245988, baseEnd_3245988] using wordTrace_append hprefix tailTrace_3245988
  have hstable : (prefixWord ++ tailWord_3245988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245988).length < 2 ^ (prefixWord ++ tailWord_3245988).sum := by decide
  have hdescent : baseEnd_3245988 < baseStart_3245988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246031 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 1, 5]
def baseStart_3246031 : Nat := 118140960795 + 3246031 * 2 ^ 59
def prefixEnd_3246031 : Nat := 4983230072969 + 3 ^ 40 * 3246031 * 2
def baseEnd_3246031 : Nat := 555591374131564874161427

theorem tailTrace_3246031 : CollatzResearch.WordTrace tailWord_3246031 prefixEnd_3246031 555591374131564874161427 := by
  unfold tailWord_3246031
  simp only [CollatzResearch.WordTrace]
  refine ⟨118392476903191539803625947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78928317935461026535750631 118392476903191539803625947)
  ·
    refine ⟨177588715354787309705438921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118392476903191539803625947 177588715354787309705438921)
    ·
      refine ⟨133191536516090482279079191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177588715354787309705438921 133191536516090482279079191)
      ·
        refine ⟨199787304774135723418618787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133191536516090482279079191 199787304774135723418618787)
        ·
          refine ⟨299680957161203585127928181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199787304774135723418618787 299680957161203585127928181)
          ·
            refine ⟨28095089733862836105743267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299680957161203585127928181 28095089733862836105743267)
            ·
              refine ⟨42142634600794254158614901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28095089733862836105743267 42142634600794254158614901)
              ·
                refine ⟨3950871993824461327370147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42142634600794254158614901 3950871993824461327370147)
                ·
                  refine ⟨5926307990736691991055221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950871993824461327370147 5926307990736691991055221)
                  ·
                    refine ⟨555591374131564874161427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5926307990736691991055221 555591374131564874161427)
                    ·
                      rfl

theorem cell23_3246031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 5].length) (baseStart_3246031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246031 prefixEnd_3246031 := by exact prefixLift 3246031
  have htrace : WordTrace (prefixWord ++ tailWord_3246031) baseStart_3246031 baseEnd_3246031 := by
    simpa [prefixWord, tailWord_3246031, baseEnd_3246031] using wordTrace_append hprefix tailTrace_3246031
  have hstable : (prefixWord ++ tailWord_3246031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246031).length < 2 ^ (prefixWord ++ tailWord_3246031).sum := by decide
  have hdescent : baseEnd_3246031 < baseStart_3246031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246065 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 1, 5]
def baseStart_3246065 : Nat := 118140960795 + 3246065 * 2 ^ 59
def prefixEnd_3246065 : Nat := 4983230072969 + 3 ^ 40 * 3246065 * 2
def baseEnd_3246065 : Nat := 555597193578982496486375

theorem tailTrace_3246065 : CollatzResearch.WordTrace tailWord_3246065 prefixEnd_3246065 555597193578982496486375 := by
  unfold tailWord_3246065
  simp only [CollatzResearch.WordTrace]
  refine ⟨118393716985068363610363649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78929144656712242406909099 118393716985068363610363649)
  ·
    refine ⟨88795287738801272707772737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118393716985068363610363649 88795287738801272707772737)
    ·
      refine ⟨66596465804100954530829553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88795287738801272707772737 66596465804100954530829553)
      ·
        refine ⟨49947349353075715898122165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66596465804100954530829553 49947349353075715898122165)
        ·
          refine ⟨4682564001850848365448953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49947349353075715898122165 4682564001850848365448953)
          ·
            refine ⟨3511923001388136274086715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682564001850848365448953 3511923001388136274086715)
            ·
              refine ⟨5267884502082204411130073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511923001388136274086715 5267884502082204411130073)
              ·
                refine ⟨3950913376561653308347555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267884502082204411130073 3950913376561653308347555)
                ·
                  refine ⟨5926370064842479962521333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950913376561653308347555 5926370064842479962521333)
                  ·
                    refine ⟨555597193578982496486375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5926370064842479962521333 555597193578982496486375)
                    ·
                      rfl

theorem cell23_3246065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_3246065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246065 prefixEnd_3246065 := by exact prefixLift 3246065
  have htrace : WordTrace (prefixWord ++ tailWord_3246065) baseStart_3246065 baseEnd_3246065 := by
    simpa [prefixWord, tailWord_3246065, baseEnd_3246065] using wordTrace_append hprefix tailTrace_3246065
  have hstable : (prefixWord ++ tailWord_3246065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246065).length < 2 ^ (prefixWord ++ tailWord_3246065).sum := by decide
  have hdescent : baseEnd_3246065 < baseStart_3246065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246078 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 3, 6]
def baseStart_3246078 : Nat := 118140960795 + 3246078 * 2 ^ 59
def prefixEnd_3246078 : Nat := 4983230072969 + 3 ^ 40 * 3246078 * 2
def baseEnd_3246078 : Nat := 555599418661818646198855

theorem tailTrace_3246078 : CollatzResearch.WordTrace tailWord_3246078 prefixEnd_3246078 555599418661818646198855 := by
  unfold tailWord_3246078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14799273891752658353823361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78929460756014177887057925 14799273891752658353823361)
  ·
    refine ⟨11099455418814493765367521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14799273891752658353823361 11099455418814493765367521)
    ·
      refine ⟨8324591564110870324025641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11099455418814493765367521 8324591564110870324025641)
      ·
        refine ⟨6243443673083152743019231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8324591564110870324025641 6243443673083152743019231)
        ·
          refine ⟨9365165509624729114528847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6243443673083152743019231 9365165509624729114528847)
          ·
            refine ⟨14047748264437093671793271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9365165509624729114528847 14047748264437093671793271)
            ·
              refine ⟨21071622396655640507689907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14047748264437093671793271 21071622396655640507689907)
              ·
                refine ⟨31607433594983460761534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21071622396655640507689907 31607433594983460761534861)
                ·
                  refine ⟨11852787598118797785575573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31607433594983460761534861 11852787598118797785575573)
                  ·
                    refine ⟨555599418661818646198855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11852787598118797785575573 555599418661818646198855)
                    ·
                      rfl

theorem cell23_3246078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_3246078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246078 prefixEnd_3246078 := by exact prefixLift 3246078
  have htrace : WordTrace (prefixWord ++ tailWord_3246078) baseStart_3246078 baseEnd_3246078 := by
    simpa [prefixWord, tailWord_3246078, baseEnd_3246078] using wordTrace_append hprefix tailTrace_3246078
  have hstable : (prefixWord ++ tailWord_3246078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246078).length < 2 ^ (prefixWord ++ tailWord_3246078).sum := by decide
  have hdescent : baseEnd_3246078 < baseStart_3246078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246085 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 1, 1, 4]
def baseStart_3246085 : Nat := 118140960795 + 3246085 * 2 ^ 59
def prefixEnd_3246085 : Nat := 4983230072969 + 3 ^ 40 * 3246085 * 2
def baseEnd_3246085 : Nat := 1666801850350037411209033

theorem tailTrace_3246085 : CollatzResearch.WordTrace tailWord_3246085 prefixEnd_3246085 1666801850350037411209033 := by
  unfold tailWord_3246085
  simp only [CollatzResearch.WordTrace]
  refine ⟨118394446444995907026091709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78929630963330604684061139 118394446444995907026091709)
  ·
    refine ⟨44397917416873465134784391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118394446444995907026091709 44397917416873465134784391)
    ·
      refine ⟨66596876125310197702176587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44397917416873465134784391 66596876125310197702176587)
      ·
        refine ⟨99895314187965296553264881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66596876125310197702176587 99895314187965296553264881)
        ·
          refine ⟨74921485640973972414948661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99895314187965296553264881 74921485640973972414948661)
          ·
            refine ⟨7023889278841309913901437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74921485640973972414948661 7023889278841309913901437)
            ·
              refine ⟨2633958479565491217713039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7023889278841309913901437 2633958479565491217713039)
              ·
                refine ⟨3950937719348236826569559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633958479565491217713039 3950937719348236826569559)
                ·
                  refine ⟨5926406579022355239854339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950937719348236826569559 5926406579022355239854339)
                  ·
                    refine ⟨8889609868533532859781509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926406579022355239854339 8889609868533532859781509)
                    ·
                      refine ⟨1666801850350037411209033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8889609868533532859781509 1666801850350037411209033)
                      ·
                        rfl

theorem cell23_3246085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 1, 1, 4].length) (baseStart_3246085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246085 prefixEnd_3246085 := by exact prefixLift 3246085
  have htrace : WordTrace (prefixWord ++ tailWord_3246085) baseStart_3246085 baseEnd_3246085 := by
    simpa [prefixWord, tailWord_3246085, baseEnd_3246085] using wordTrace_append hprefix tailTrace_3246085
  have hstable : (prefixWord ++ tailWord_3246085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246085).length < 2 ^ (prefixWord ++ tailWord_3246085).sum := by decide
  have hdescent : baseEnd_3246085 < baseStart_3246085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246108 : List Nat := [2, 2, 3, 1, 3, 3, 1, 8]
def baseStart_3246108 : Nat := 118140960795 + 3246108 * 2 ^ 59
def prefixEnd_3246108 : Nat := 4983230072969 + 3 ^ 40 * 3246108 * 2
def baseEnd_3246108 : Nat := 61733839274262623008201

theorem tailTrace_3246108 : CollatzResearch.WordTrace tailWord_3246108 prefixEnd_3246108 61733839274262623008201 := by
  unfold tailWord_3246108
  simp only [CollatzResearch.WordTrace]
  refine ⟨59197642661956290977089489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78930190215941721302785985 59197642661956290977089489)
  ·
    refine ⟨44398231996467218232817117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59197642661956290977089489 44398231996467218232817117)
    ·
      refine ⟨16649336998675206837306419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44398231996467218232817117 16649336998675206837306419)
      ·
        refine ⟨24974005498012810255959629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16649336998675206837306419 24974005498012810255959629)
        ·
          refine ⟨9365252061754803845984861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24974005498012810255959629 9365252061754803845984861)
          ·
            refine ⟨3511969523158051442244323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9365252061754803845984861 3511969523158051442244323)
            ·
              refine ⟨5267954284737077163366485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511969523158051442244323 5267954284737077163366485)
              ·
                refine ⟨61733839274262623008201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5267954284737077163366485 61733839274262623008201)
                ·
                  rfl

theorem cell23_3246108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 8].length) (baseStart_3246108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246108 prefixEnd_3246108 := by exact prefixLift 3246108
  have htrace : WordTrace (prefixWord ++ tailWord_3246108) baseStart_3246108 baseEnd_3246108 := by
    simpa [prefixWord, tailWord_3246108, baseEnd_3246108] using wordTrace_append hprefix tailTrace_3246108
  have hstable : (prefixWord ++ tailWord_3246108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246108).length < 2 ^ (prefixWord ++ tailWord_3246108).sum := by decide
  have hdescent : baseEnd_3246108 < baseStart_3246108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246119 : List Nat := [1, 1, 7, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3246119 : Nat := 118140960795 + 3246119 * 2 ^ 59
def prefixEnd_3246119 : Nat := 4983230072969 + 3 ^ 40 * 3246119 * 2
def baseEnd_3246119 : Nat := 1666819308692290278183877

theorem tailTrace_3246119 : CollatzResearch.WordTrace tailWord_3246119 prefixEnd_3246119 1666819308692290278183877 := by
  unfold tailWord_3246119
  simp only [CollatzResearch.WordTrace]
  refine ⟨118395686526872730832829411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78930457684581820555219607 118395686526872730832829411)
  ·
    refine ⟨177593529790309096249244117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118395686526872730832829411 177593529790309096249244117)
    ·
      refine ⟨4162348354460369443341659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 177593529790309096249244117 4162348354460369443341659)
      ·
        refine ⟨6243522531690554165012489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162348354460369443341659 6243522531690554165012489)
        ·
          refine ⟨4682641898767915623759367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243522531690554165012489 4682641898767915623759367)
          ·
            refine ⟨7023962848151873435639051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682641898767915623759367 7023962848151873435639051)
            ·
              refine ⟨10535944272227810153458577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7023962848151873435639051 10535944272227810153458577)
              ·
                refine ⟨7901958204170857615093933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10535944272227810153458577 7901958204170857615093933)
                ·
                  refine ⟨2963234326564071605660225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7901958204170857615093933 2963234326564071605660225)
                  ·
                    refine ⟨2222425744923053704245169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963234326564071605660225 2222425744923053704245169)
                    ·
                      refine ⟨1666819308692290278183877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222425744923053704245169 1666819308692290278183877)
                      ·
                        rfl

theorem cell23_3246119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3246119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246119 prefixEnd_3246119 := by exact prefixLift 3246119
  have htrace : WordTrace (prefixWord ++ tailWord_3246119) baseStart_3246119 baseEnd_3246119 := by
    simpa [prefixWord, tailWord_3246119, baseEnd_3246119] using wordTrace_append hprefix tailTrace_3246119
  have hstable : (prefixWord ++ tailWord_3246119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246119).length < 2 ^ (prefixWord ++ tailWord_3246119).sum := by decide
  have hdescent : baseEnd_3246119 < baseStart_3246119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246151 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3246151 : Nat := 118140960795 + 3246151 * 2 ^ 59
def prefixEnd_3246151 : Nat := 4983230072969 + 3 ^ 40 * 3246151 * 2
def baseEnd_3246151 : Nat := 555611913357744717661243

theorem tailTrace_3246151 : CollatzResearch.WordTrace tailWord_3246151 prefixEnd_3246151 555611913357744717661243 := by
  unfold tailWord_3246151
  simp only [CollatzResearch.WordTrace]
  refine ⟨118396853662756800297994307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78931235775171200198662871 118396853662756800297994307)
  ·
    refine ⟨177595280494135200446991461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118396853662756800297994307 177595280494135200446991461)
    ·
      refine ⟨33299115092650350083810899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177595280494135200446991461 33299115092650350083810899)
      ·
        refine ⟨49948672638975525125716349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33299115092650350083810899 49948672638975525125716349)
        ·
          refine ⟨18730752239615821922143631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49948672638975525125716349 18730752239615821922143631)
          ·
            refine ⟨28096128359423732883215447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18730752239615821922143631 28096128359423732883215447)
            ·
              refine ⟨42144192539135599324823171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28096128359423732883215447 42144192539135599324823171)
              ·
                refine ⟨63216288808703398987234757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42144192539135599324823171 63216288808703398987234757)
                ·
                  refine ⟨11853054151631887310106517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63216288808703398987234757 11853054151631887310106517)
                  ·
                    refine ⟨555611913357744717661243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11853054151631887310106517 555611913357744717661243)
                    ·
                      rfl

theorem cell23_3246151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3246151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246151 prefixEnd_3246151 := by exact prefixLift 3246151
  have htrace : WordTrace (prefixWord ++ tailWord_3246151) baseStart_3246151 baseEnd_3246151 := by
    simpa [prefixWord, tailWord_3246151, baseEnd_3246151] using wordTrace_append hprefix tailTrace_3246151
  have hstable : (prefixWord ++ tailWord_3246151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246151).length < 2 ^ (prefixWord ++ tailWord_3246151).sum := by decide
  have hdescent : baseEnd_3246151 < baseStart_3246151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246161 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3246161 : Nat := 118140960795 + 3246161 * 2 ^ 59
def prefixEnd_3246161 : Nat := 4983230072969 + 3 ^ 40 * 3246161 * 2
def baseEnd_3246161 : Nat := 1666840874879779113858683

theorem tailTrace_3246161 : CollatzResearch.WordTrace tailWord_3246161 prefixEnd_3246161 1666840874879779113858683 := by
  unfold tailWord_3246161
  simp only [CollatzResearch.WordTrace]
  refine ⟨118397218392720572005858337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78931478928480381337238891 118397218392720572005858337)
  ·
    refine ⟨88797913794540429004393753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118397218392720572005858337 88797913794540429004393753)
    ·
      refine ⟨66598435345905321753295315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88797913794540429004393753 66598435345905321753295315)
      ·
        refine ⟨99897653018857982629942973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66598435345905321753295315 99897653018857982629942973)
        ·
          refine ⟨37461619882071743486228615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99897653018857982629942973 37461619882071743486228615)
          ·
            refine ⟨56192429823107615229342923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37461619882071743486228615 56192429823107615229342923)
            ·
              refine ⟨84288644734661422844014385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56192429823107615229342923 84288644734661422844014385)
              ·
                refine ⟨63216483550996067133010789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84288644734661422844014385 63216483550996067133010789)
                ·
                  refine ⟨11853090665811762587439523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63216483550996067133010789 11853090665811762587439523)
                  ·
                    refine ⟨17779635998717643881159285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11853090665811762587439523 17779635998717643881159285)
                    ·
                      refine ⟨1666840874879779113858683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17779635998717643881159285 1666840874879779113858683)
                      ·
                        rfl

theorem cell23_3246161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3246161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246161 prefixEnd_3246161 := by exact prefixLift 3246161
  have htrace : WordTrace (prefixWord ++ tailWord_3246161) baseStart_3246161 baseEnd_3246161 := by
    simpa [prefixWord, tailWord_3246161, baseEnd_3246161] using wordTrace_append hprefix tailTrace_3246161
  have hstable : (prefixWord ++ tailWord_3246161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246161).length < 2 ^ (prefixWord ++ tailWord_3246161).sum := by decide
  have hdescent : baseEnd_3246161 < baseStart_3246161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246260 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_3246260 : Nat := 118140960795 + 3246260 * 2 ^ 59
def prefixEnd_3246260 : Nat := 4983230072969 + 3 ^ 40 * 3246260 * 2
def baseEnd_3246260 : Nat := 1666891709464574226520729

theorem tailTrace_3246260 : CollatzResearch.WordTrace tailWord_3246260 prefixEnd_3246260 1666891709464574226520729 := by
  unfold tailWord_3246260
  simp only [CollatzResearch.WordTrace]
  refine ⟨59200414609680955956856117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78933886146241274609141489 59200414609680955956856117)
  ·
    refine ⟨5550038869657589620955261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59200414609680955956856117 5550038869657589620955261)
    ·
      refine ⟨2081264576121596107858223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5550038869657589620955261 2081264576121596107858223)
      ·
        refine ⟨3121896864182394161787335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081264576121596107858223 3121896864182394161787335)
        ·
          refine ⟨4682845296273591242681003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121896864182394161787335 4682845296273591242681003)
          ·
            refine ⟨7024267944410386864021505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682845296273591242681003 7024267944410386864021505)
            ·
              refine ⟨5268200958307790148016129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7024267944410386864021505 5268200958307790148016129)
              ·
                refine ⟨3951150718730842611012097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5268200958307790148016129 3951150718730842611012097)
                ·
                  refine ⟨2963363039048131958259073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951150718730842611012097 2963363039048131958259073)
                  ·
                    refine ⟨2222522279286098968694305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963363039048131958259073 2222522279286098968694305)
                    ·
                      refine ⟨1666891709464574226520729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222522279286098968694305 1666891709464574226520729)
                      ·
                        rfl

theorem cell23_3246260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_3246260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246260 prefixEnd_3246260 := by exact prefixLift 3246260
  have htrace : WordTrace (prefixWord ++ tailWord_3246260) baseStart_3246260 baseEnd_3246260 := by
    simpa [prefixWord, tailWord_3246260, baseEnd_3246260] using wordTrace_append hprefix tailTrace_3246260
  have hstable : (prefixWord ++ tailWord_3246260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246260).length < 2 ^ (prefixWord ++ tailWord_3246260).sum := by decide
  have hdescent : baseEnd_3246260 < baseStart_3246260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246265 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3246265 : Nat := 118140960795 + 3246265 * 2 ^ 59
def prefixEnd_3246265 : Nat := 4983230072969 + 3 ^ 40 * 3246265 * 2
def baseEnd_3246265 : Nat := 1666894276867846706958205

theorem tailTrace_3246265 : CollatzResearch.WordTrace tailWord_3246265 prefixEnd_3246265 1666894276867846706958205 := by
  unfold tailWord_3246265
  simp only [CollatzResearch.WordTrace]
  refine ⟨118401011584343797767644249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78934007722895865178429499 118401011584343797767644249)
  ·
    refine ⟨88800758688257848325733187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118401011584343797767644249 88800758688257848325733187)
    ·
      refine ⟨133201138032386772488599781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88800758688257848325733187 133201138032386772488599781)
      ·
        refine ⟨24975213381072519841612459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133201138032386772488599781 24975213381072519841612459)
        ·
          refine ⟨37462820071608779762418689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24975213381072519841612459 37462820071608779762418689)
          ·
            refine ⟨28097115053706584821814017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37462820071608779762418689 28097115053706584821814017)
            ·
              refine ⟨21072836290279938616360513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28097115053706584821814017 21072836290279938616360513)
              ·
                refine ⟨15804627217709953962270385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21072836290279938616360513 15804627217709953962270385)
                ·
                  refine ⟨11853470413282465471702789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15804627217709953962270385 11853470413282465471702789)
                  ·
                    refine ⟨2222525702490462275944273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11853470413282465471702789 2222525702490462275944273)
                    ·
                      refine ⟨1666894276867846706958205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222525702490462275944273 1666894276867846706958205)
                      ·
                        rfl

theorem cell23_3246265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3246265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246265 prefixEnd_3246265 := by exact prefixLift 3246265
  have htrace : WordTrace (prefixWord ++ tailWord_3246265) baseStart_3246265 baseEnd_3246265 := by
    simpa [prefixWord, tailWord_3246265, baseEnd_3246265] using wordTrace_append hprefix tailTrace_3246265
  have hstable : (prefixWord ++ tailWord_3246265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246265).length < 2 ^ (prefixWord ++ tailWord_3246265).sum := by decide
  have hdescent : baseEnd_3246265 < baseStart_3246265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246309 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 1, 4]
def baseStart_3246309 : Nat := 118140960795 + 3246309 * 2 ^ 59
def prefixEnd_3246309 : Nat := 4983230072969 + 3 ^ 40 * 3246309 * 2
def baseEnd_3246309 : Nat := 555638956672214844936001

theorem tailTrace_3246309 : CollatzResearch.WordTrace tailWord_3246309 prefixEnd_3246309 555638956672214844936001 := by
  unfold tailWord_3246309
  simp only [CollatzResearch.WordTrace]
  refine ⟨118402616396184393282245981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78935077597456262188163987 118402616396184393282245981)
  ·
    refine ⟨44400981148569147480842243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118402616396184393282245981 44400981148569147480842243)
    ·
      refine ⟨66601471722853721221263365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44400981148569147480842243 66601471722853721221263365)
      ·
        refine ⟨12487775948035072728986881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66601471722853721221263365 12487775948035072728986881)
        ·
          refine ⟨9365831961026304546740161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12487775948035072728986881 9365831961026304546740161)
          ·
            refine ⟨7024373970769728410055121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9365831961026304546740161 7024373970769728410055121)
            ·
              refine ⟨5268280478077296307541341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7024373970769728410055121 5268280478077296307541341)
              ·
                refine ⟨1975605179278986115328003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5268280478077296307541341 1975605179278986115328003)
                ·
                  refine ⟨2963407768918479172992005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975605179278986115328003 2963407768918479172992005)
                  ·
                    refine ⟨555638956672214844936001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2963407768918479172992005 555638956672214844936001)
                    ·
                      rfl

theorem cell23_3246309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 4].length) (baseStart_3246309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246309 prefixEnd_3246309 := by exact prefixLift 3246309
  have htrace : WordTrace (prefixWord ++ tailWord_3246309) baseStart_3246309 baseEnd_3246309 := by
    simpa [prefixWord, tailWord_3246309, baseEnd_3246309] using wordTrace_append hprefix tailTrace_3246309
  have hstable : (prefixWord ++ tailWord_3246309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246309).length < 2 ^ (prefixWord ++ tailWord_3246309).sum := by decide
  have hdescent : baseEnd_3246309 < baseStart_3246309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246315 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 3]
def baseStart_3246315 : Nat := 118140960795 + 3246315 * 2 ^ 59
def prefixEnd_3246315 : Nat := 4983230072969 + 3 ^ 40 * 3246315 * 2
def baseEnd_3246315 : Nat := 1666919950900571511332975

theorem tailTrace_3246315 : CollatzResearch.WordTrace tailWord_3246315 prefixEnd_3246315 1666919950900571511332975 := by
  unfold tailWord_3246315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118402835234162656306964399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78935223489441770871309599 118402835234162656306964399)
  ·
    refine ⟨177604252851243984460446599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118402835234162656306964399 177604252851243984460446599)
    ·
      refine ⟨266406379276865976690669899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177604252851243984460446599 266406379276865976690669899)
      ·
        refine ⟨399609568915298965036004849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266406379276865976690669899 399609568915298965036004849)
        ·
          refine ⟨299707176686474223777003637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399609568915298965036004849 299707176686474223777003637)
          ·
            refine ⟨28097547814356958479094091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299707176686474223777003637 28097547814356958479094091)
            ·
              refine ⟨42146321721535437718641137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28097547814356958479094091 42146321721535437718641137)
              ·
                refine ⟨31609741291151578288980853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42146321721535437718641137 31609741291151578288980853)
                ·
                  refine ⟨2963413246045460464591955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31609741291151578288980853 2963413246045460464591955)
                  ·
                    refine ⟨4445119869068190696887933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963413246045460464591955 4445119869068190696887933)
                    ·
                      refine ⟨1666919950900571511332975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445119869068190696887933 1666919950900571511332975)
                      ·
                        rfl

theorem cell23_3246315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 5, 1, 3].length) (baseStart_3246315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246315 prefixEnd_3246315 := by exact prefixLift 3246315
  have htrace : WordTrace (prefixWord ++ tailWord_3246315) baseStart_3246315 baseEnd_3246315 := by
    simpa [prefixWord, tailWord_3246315, baseEnd_3246315] using wordTrace_append hprefix tailTrace_3246315
  have hstable : (prefixWord ++ tailWord_3246315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246315).length < 2 ^ (prefixWord ++ tailWord_3246315).sum := by decide
  have hdescent : baseEnd_3246315 < baseStart_3246315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246322 : List Nat := [3, 2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_3246322 : Nat := 118140960795 + 3246322 * 2 ^ 59
def prefixEnd_3246322 : Nat := 4983230072969 + 3 ^ 40 * 3246322 * 2
def baseEnd_3246322 : Nat := 185213727251683664882827

theorem tailTrace_3246322 : CollatzResearch.WordTrace tailWord_3246322 prefixEnd_3246322 185213727251683664882827 := by
  unfold tailWord_3246322
  simp only [CollatzResearch.WordTrace]
  refine ⟨29600772636284324125617305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78935393696758197668312813 29600772636284324125617305)
  ·
    refine ⟨22200579477213243094212979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29600772636284324125617305 22200579477213243094212979)
    ·
      refine ⟨33300869215819864641319469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22200579477213243094212979 33300869215819864641319469)
      ·
        refine ⟨12487825955932449240494801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33300869215819864641319469 12487825955932449240494801)
        ·
          refine ⟨9365869466949336930371101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12487825955932449240494801 9365869466949336930371101)
          ·
            refine ⟨3512201050106001348889163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9365869466949336930371101 3512201050106001348889163)
            ·
              refine ⟨5268301575159002023333745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512201050106001348889163 5268301575159002023333745)
              ·
                refine ⟨3951226181369251517500309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5268301575159002023333745 3951226181369251517500309)
                ·
                  refine ⟨185213727251683664882827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3951226181369251517500309 185213727251683664882827)
                  ·
                    rfl

theorem cell23_3246322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_3246322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246322 prefixEnd_3246322 := by exact prefixLift 3246322
  have htrace : WordTrace (prefixWord ++ tailWord_3246322) baseStart_3246322 baseEnd_3246322 := by
    simpa [prefixWord, tailWord_3246322, baseEnd_3246322] using wordTrace_append hprefix tailTrace_3246322
  have hstable : (prefixWord ++ tailWord_3246322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246322).length < 2 ^ (prefixWord ++ tailWord_3246322).sum := by decide
  have hdescent : baseEnd_3246322 < baseStart_3246322 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246332 : List Nat := [2, 2, 2, 1, 4, 1, 1, 3, 3, 1, 3]
def baseStart_3246332 : Nat := 118140960795 + 3246332 * 2 ^ 59
def prefixEnd_3246332 : Nat := 4983230072969 + 3 ^ 40 * 3246332 * 2
def baseEnd_3246332 : Nat := 1666928680071697944820397

theorem tailTrace_3246332 : CollatzResearch.WordTrace tailWord_3246332 prefixEnd_3246332 1666928680071697944820397 := by
  unfold tailWord_3246332
  simp only [CollatzResearch.WordTrace]
  refine ⟨59201727637550534105166625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78935636850067378806888833 59201727637550534105166625)
  ·
    refine ⟨44401295728162900578874969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59201727637550534105166625 44401295728162900578874969)
    ·
      refine ⟨33300971796122175434156227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44401295728162900578874969 33300971796122175434156227)
      ·
        refine ⟨49951457694183263151234341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33300971796122175434156227 49951457694183263151234341)
        ·
          refine ⟨9365898317659361840856439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49951457694183263151234341 9365898317659361840856439)
          ·
            refine ⟨14048847476489042761284659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9365898317659361840856439 14048847476489042761284659)
            ·
              refine ⟨21073271214733564141926989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14048847476489042761284659 21073271214733564141926989)
              ·
                refine ⟨7902476705525086553222621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21073271214733564141926989 7902476705525086553222621)
                ·
                  refine ⟨2963428764571907457458483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7902476705525086553222621 2963428764571907457458483)
                  ·
                    refine ⟨4445143146857861186187725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963428764571907457458483 4445143146857861186187725)
                    ·
                      refine ⟨1666928680071697944820397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445143146857861186187725 1666928680071697944820397)
                      ·
                        rfl

theorem cell23_3246332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_3246332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246332 prefixEnd_3246332 := by exact prefixLift 3246332
  have htrace : WordTrace (prefixWord ++ tailWord_3246332) baseStart_3246332 baseEnd_3246332 := by
    simpa [prefixWord, tailWord_3246332, baseEnd_3246332] using wordTrace_append hprefix tailTrace_3246332
  have hstable : (prefixWord ++ tailWord_3246332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246332).length < 2 ^ (prefixWord ++ tailWord_3246332).sum := by decide
  have hdescent : baseEnd_3246332 < baseStart_3246332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246372 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_3246372 : Nat := 118140960795 + 3246372 * 2 ^ 59
def prefixEnd_3246372 : Nat := 4983230072969 + 3 ^ 40 * 3246372 * 2
def baseEnd_3246372 : Nat := 1666949219297877788320213

theorem tailTrace_3246372 : CollatzResearch.WordTrace tailWord_3246372 prefixEnd_3246372 1666949219297877788320213 := by
  unfold tailWord_3246372
  simp only [CollatzResearch.WordTrace]
  refine ⟨59202457097478077520894685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78936609463304103361192913 59202457097478077520894685)
  ·
    refine ⟨22200921411554279070335507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59202457097478077520894685 22200921411554279070335507)
    ·
      refine ⟨33301382117331418605503261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22200921411554279070335507 33301382117331418605503261)
      ·
        refine ⟨12488018293999281977063723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33301382117331418605503261 12488018293999281977063723)
        ·
          refine ⟨18732027440998922965595585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488018293999281977063723 18732027440998922965595585)
          ·
            refine ⟨14049020580749192224196689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18732027440998922965595585 14049020580749192224196689)
            ·
              refine ⟨10536765435561894168147517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14049020580749192224196689 10536765435561894168147517)
              ·
                refine ⟨3951287038335710313055319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10536765435561894168147517 3951287038335710313055319)
                ·
                  refine ⟨5926930557503565469582979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951287038335710313055319 5926930557503565469582979)
                  ·
                    refine ⟨8890395836255348204374469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926930557503565469582979 8890395836255348204374469)
                    ·
                      refine ⟨1666949219297877788320213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8890395836255348204374469 1666949219297877788320213)
                      ·
                        rfl

theorem cell23_3246372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_3246372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246372 prefixEnd_3246372 := by exact prefixLift 3246372
  have htrace : WordTrace (prefixWord ++ tailWord_3246372) baseStart_3246372 baseEnd_3246372 := by
    simpa [prefixWord, tailWord_3246372, baseEnd_3246372] using wordTrace_append hprefix tailTrace_3246372
  have hstable : (prefixWord ++ tailWord_3246372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246372).length < 2 ^ (prefixWord ++ tailWord_3246372).sum := by decide
  have hdescent : baseEnd_3246372 < baseStart_3246372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246439 : List Nat := [1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 3]
def baseStart_3246439 : Nat := 118140960795 + 3246439 * 2 ^ 59
def prefixEnd_3246439 : Nat := 4983230072969 + 3 ^ 40 * 3246439 * 2
def baseEnd_3246439 : Nat := 1666983622501729026182405

theorem tailTrace_3246439 : CollatzResearch.WordTrace tailWord_3246439 prefixEnd_3246439 1666983622501729026182405 := by
  unfold tailWord_3246439
  simp only [CollatzResearch.WordTrace]
  refine ⟨118407357885713425484478371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78938238590475616989652247 118407357885713425484478371)
  ·
    refine ⟨177611036828570138226717557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118407357885713425484478371 177611036828570138226717557)
    ·
      refine ⟨16651034702678450458754771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177611036828570138226717557 16651034702678450458754771)
      ·
        refine ⟨24976552054017675688132157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16651034702678450458754771 24976552054017675688132157)
        ·
          refine ⟨9366207020256628383049559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24976552054017675688132157 9366207020256628383049559)
          ·
            refine ⟨14049310530384942574574339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9366207020256628383049559 14049310530384942574574339)
            ·
              refine ⟨21073965795577413861861509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14049310530384942574574339 21073965795577413861861509)
              ·
                refine ⟨3951368586670765099099033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21073965795577413861861509 3951368586670765099099033)
                ·
                  refine ⟨2963526440003073824324275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951368586670765099099033 2963526440003073824324275)
                  ·
                    refine ⟨4445289660004610736486413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963526440003073824324275 4445289660004610736486413)
                    ·
                      refine ⟨1666983622501729026182405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445289660004610736486413 1666983622501729026182405)
                      ·
                        rfl

theorem cell23_3246439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 3].length) (baseStart_3246439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246439 prefixEnd_3246439 := by exact prefixLift 3246439
  have htrace : WordTrace (prefixWord ++ tailWord_3246439) baseStart_3246439 baseEnd_3246439 := by
    simpa [prefixWord, tailWord_3246439, baseEnd_3246439] using wordTrace_append hprefix tailTrace_3246439
  have hstable : (prefixWord ++ tailWord_3246439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246439).length < 2 ^ (prefixWord ++ tailWord_3246439).sum := by decide
  have hdescent : baseEnd_3246439 < baseStart_3246439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246440 : List Nat := [2, 1, 4, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_3246440 : Nat := 118140960795 + 3246440 * 2 ^ 59
def prefixEnd_3246440 : Nat := 4983230072969 + 3 ^ 40 * 3246440 * 2
def baseEnd_3246440 : Nat := 1666984135982383522269901

theorem tailTrace_3246440 : CollatzResearch.WordTrace tailWord_3246440 prefixEnd_3246440 1666984135982383522269901 := by
  unfold tailWord_3246440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59203697179354901327632387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78938262905806535103509849 59203697179354901327632387)
  ·
    refine ⟨88805545769032351991448581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59203697179354901327632387 88805545769032351991448581)
    ·
      refine ⟨16651039831693565998396609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88805545769032351991448581 16651039831693565998396609)
      ·
        refine ⟨12488279873770174498797457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16651039831693565998396609 12488279873770174498797457)
        ·
          refine ⟨9366209905327630874098093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12488279873770174498797457 9366209905327630874098093)
          ·
            refine ⟨3512328714497861577786785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9366209905327630874098093 3512328714497861577786785)
            ·
              refine ⟨2634246535873396183340089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512328714497861577786785 2634246535873396183340089)
              ·
                refine ⟨1975684901905047137505067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634246535873396183340089 1975684901905047137505067)
                ·
                  refine ⟨2963527352857570706257601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975684901905047137505067 2963527352857570706257601)
                  ·
                    refine ⟨2222645514643178029693201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963527352857570706257601 2222645514643178029693201)
                    ·
                      refine ⟨1666984135982383522269901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222645514643178029693201 1666984135982383522269901)
                      ·
                        rfl

theorem cell23_3246440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_3246440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246440 prefixEnd_3246440 := by exact prefixLift 3246440
  have htrace : WordTrace (prefixWord ++ tailWord_3246440) baseStart_3246440 baseEnd_3246440 := by
    simpa [prefixWord, tailWord_3246440, baseEnd_3246440] using wordTrace_append hprefix tailTrace_3246440
  have hstable : (prefixWord ++ tailWord_3246440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246440).length < 2 ^ (prefixWord ++ tailWord_3246440).sum := by decide
  have hdescent : baseEnd_3246440 < baseStart_3246440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246445 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 4]
def baseStart_3246445 : Nat := 118140960795 + 3246445 * 2 ^ 59
def prefixEnd_3246445 : Nat := 4983230072969 + 3 ^ 40 * 3246445 * 2
def baseEnd_3246445 : Nat := 1666986703385656002707377

theorem tailTrace_3246445 : CollatzResearch.WordTrace tailWord_3246445 prefixEnd_3246445 1666986703385656002707377 := by
  unfold tailWord_3246445
  simp only [CollatzResearch.WordTrace]
  refine ⟨118407576723691688509196789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78938384482461125672797859 118407576723691688509196789)
  ·
    refine ⟨11100710317846095797737199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118407576723691688509196789 11100710317846095797737199)
    ·
      refine ⟨16651065476769143696605799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100710317846095797737199 16651065476769143696605799)
      ·
        refine ⟨24976598215153715544908699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16651065476769143696605799 24976598215153715544908699)
        ·
          refine ⟨37464897322730573317363049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24976598215153715544908699 37464897322730573317363049)
          ·
            refine ⟨28098672992047929988022287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37464897322730573317363049 28098672992047929988022287)
            ·
              refine ⟨42148009488071894982033431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28098672992047929988022287 42148009488071894982033431)
              ·
                refine ⟨63222014232107842473050147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42148009488071894982033431 63222014232107842473050147)
                ·
                  refine ⟨94833021348161763709575221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63222014232107842473050147 94833021348161763709575221)
                  ·
                    refine ⟨8890595751390165347772677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94833021348161763709575221 8890595751390165347772677)
                    ·
                      refine ⟨1666986703385656002707377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8890595751390165347772677 1666986703385656002707377)
                      ·
                        rfl

theorem cell23_3246445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_3246445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246445 prefixEnd_3246445 := by exact prefixLift 3246445
  have htrace : WordTrace (prefixWord ++ tailWord_3246445) baseStart_3246445 baseEnd_3246445 := by
    simpa [prefixWord, tailWord_3246445, baseEnd_3246445] using wordTrace_append hprefix tailTrace_3246445
  have hstable : (prefixWord ++ tailWord_3246445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246445).length < 2 ^ (prefixWord ++ tailWord_3246445).sum := by decide
  have hdescent : baseEnd_3246445 < baseStart_3246445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246496 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2]
def baseStart_3246496 : Nat := 118140960795 + 3246496 * 2 ^ 59
def prefixEnd_3246496 : Nat := 4983230072969 + 3 ^ 40 * 3246496 * 2
def baseEnd_3246496 : Nat := 1667012890899035303169643

theorem tailTrace_3246496 : CollatzResearch.WordTrace tailWord_3246496 prefixEnd_3246496 1667012890899035303169643 := by
  unfold tailWord_3246496
  simp only [CollatzResearch.WordTrace]
  refine ⟨59204718423253462109651671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78939624564337949479535561 59204718423253462109651671)
  ·
    refine ⟨88807077634880193164477507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59204718423253462109651671 88807077634880193164477507)
    ·
      refine ⟨133210616452320289746716261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88807077634880193164477507 133210616452320289746716261)
      ·
        refine ⟨24976990584810054327509299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133210616452320289746716261 24976990584810054327509299)
        ·
          refine ⟨37465485877215081491263949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24976990584810054327509299 37465485877215081491263949)
          ·
            refine ⟨14049557203955655559223981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37465485877215081491263949 14049557203955655559223981)
            ·
              refine ⟨5268583951483370834708993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14049557203955655559223981 5268583951483370834708993)
              ·
                refine ⟨3951437963612528126031745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5268583951483370834708993 3951437963612528126031745)
                ·
                  refine ⟨2963578472709396094523809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951437963612528126031745 2963578472709396094523809)
                  ·
                    refine ⟨2222683854532047070892857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963578472709396094523809 2222683854532047070892857)
                    ·
                      refine ⟨1667012890899035303169643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222683854532047070892857 1667012890899035303169643)
                      ·
                        rfl

theorem cell23_3246496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_3246496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246496 prefixEnd_3246496 := by exact prefixLift 3246496
  have htrace : WordTrace (prefixWord ++ tailWord_3246496) baseStart_3246496 baseEnd_3246496 := by
    simpa [prefixWord, tailWord_3246496, baseEnd_3246496] using wordTrace_append hprefix tailTrace_3246496
  have hstable : (prefixWord ++ tailWord_3246496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246496).length < 2 ^ (prefixWord ++ tailWord_3246496).sum := by decide
  have hdescent : baseEnd_3246496 < baseStart_3246496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246513 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3246513 : Nat := 118140960795 + 3246513 * 2 ^ 59
def prefixEnd_3246513 : Nat := 4983230072969 + 3 ^ 40 * 3246513 * 2
def baseEnd_3246513 : Nat := 1667021620070161736657065

theorem tailTrace_3246513 : CollatzResearch.WordTrace tailWord_3246513 prefixEnd_3246513 1667021620070161736657065 := by
  unfold tailWord_3246513
  simp only [CollatzResearch.WordTrace]
  refine ⟨118410056887445336122672193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78940037924963557415114795 118410056887445336122672193)
  ·
    refine ⟨88807542665584002092004145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118410056887445336122672193 88807542665584002092004145)
    ·
      refine ⟨66605656999188001569003109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88807542665584002092004145 66605656999188001569003109)
      ·
        refine ⟨12488560687347750294188083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66605656999188001569003109 12488560687347750294188083)
        ·
          refine ⟨18732841031021625441282125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488560687347750294188083 18732841031021625441282125)
          ·
            refine ⟨7024815386633109540480797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18732841031021625441282125 7024815386633109540480797)
            ·
              refine ⟨2634305769987416077680299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7024815386633109540480797 2634305769987416077680299)
              ·
                refine ⟨3951458654981124116520449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634305769987416077680299 3951458654981124116520449)
                ·
                  refine ⟨2963593991235843087390337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951458654981124116520449 2963593991235843087390337)
                  ·
                    refine ⟨2222695493426882315542753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963593991235843087390337 2222695493426882315542753)
                    ·
                      refine ⟨1667021620070161736657065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222695493426882315542753 1667021620070161736657065)
                      ·
                        rfl

theorem cell23_3246513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3246513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246513 prefixEnd_3246513 := by exact prefixLift 3246513
  have htrace : WordTrace (prefixWord ++ tailWord_3246513) baseStart_3246513 baseEnd_3246513 := by
    simpa [prefixWord, tailWord_3246513, baseEnd_3246513] using wordTrace_append hprefix tailTrace_3246513
  have hstable : (prefixWord ++ tailWord_3246513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246513).length < 2 ^ (prefixWord ++ tailWord_3246513).sum := by decide
  have hdescent : baseEnd_3246513 < baseStart_3246513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246522 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2]
def baseStart_3246522 : Nat := 118140960795 + 3246522 * 2 ^ 59
def prefixEnd_3246522 : Nat := 4983230072969 + 3 ^ 40 * 3246522 * 2
def baseEnd_3246522 : Nat := 1667026241396052201444523

theorem tailTrace_3246522 : CollatzResearch.WordTrace tailWord_3246522 prefixEnd_3246522 1667026241396052201444523 := by
  unfold tailWord_3246522
  simp only [CollatzResearch.WordTrace]
  refine ⟨29602596286103182664937455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78940256762941820439833213 29602596286103182664937455)
  ·
    refine ⟨44403894429154773997406183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29602596286103182664937455 44403894429154773997406183)
    ·
      refine ⟨66605841643732160996109275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44403894429154773997406183 66605841643732160996109275)
      ·
        refine ⟨99908762465598241494163913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66605841643732160996109275 99908762465598241494163913)
        ·
          refine ⟨74931571849198681120622935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99908762465598241494163913 74931571849198681120622935)
          ·
            refine ⟨112397357773798021680934403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74931571849198681120622935 112397357773798021680934403)
            ·
              refine ⟨168596036660697032521401605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112397357773798021680934403 168596036660697032521401605)
              ·
                refine ⟨31611756873880693597762801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168596036660697032521401605 31611756873880693597762801)
                ·
                  refine ⟨23708817655410520198322101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31611756873880693597762801 23708817655410520198322101)
                  ·
                    refine ⟨2222701655194736268592697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23708817655410520198322101 2222701655194736268592697)
                    ·
                      refine ⟨1667026241396052201444523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222701655194736268592697 1667026241396052201444523)
                      ·
                        rfl

theorem cell23_3246522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 2, 5, 2].length) (baseStart_3246522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246522 prefixEnd_3246522 := by exact prefixLift 3246522
  have htrace : WordTrace (prefixWord ++ tailWord_3246522) baseStart_3246522 baseEnd_3246522 := by
    simpa [prefixWord, tailWord_3246522, baseEnd_3246522] using wordTrace_append hprefix tailTrace_3246522
  have hstable : (prefixWord ++ tailWord_3246522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246522).length < 2 ^ (prefixWord ++ tailWord_3246522).sum := by decide
  have hdescent : baseEnd_3246522 < baseStart_3246522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246572 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 3]
def baseStart_3246572 : Nat := 118140960795 + 3246572 * 2 ^ 59
def prefixEnd_3246572 : Nat := 4983230072969 + 3 ^ 40 * 3246572 * 2
def baseEnd_3246572 : Nat := 1667051915428777005819293

theorem tailTrace_3246572 : CollatzResearch.WordTrace tailWord_3246572 prefixEnd_3246572 1667051915428777005819293 := by
  unfold tailWord_3246572
  simp only [CollatzResearch.WordTrace]
  refine ⟨59206104397115794599534985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78941472529487726132713313 59206104397115794599534985)
  ·
    refine ⟨44404578297836845949651239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59206104397115794599534985 44404578297836845949651239)
    ·
      refine ⟨66606867446755268924476859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44404578297836845949651239 66606867446755268924476859)
      ·
        refine ⟨99910301170132903386715289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66606867446755268924476859 99910301170132903386715289)
        ·
          refine ⟨74932725877599677540036467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99910301170132903386715289 74932725877599677540036467)
          ·
            refine ⟨112399088816399516310054701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74932725877599677540036467 112399088816399516310054701)
            ·
              refine ⟨42149658306149818616270513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112399088816399516310054701 42149658306149818616270513)
              ·
                refine ⟨31612243729612363962202885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42149658306149818616270513 31612243729612363962202885)
                ·
                  refine ⟨5927295699302318242913041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31612243729612363962202885 5927295699302318242913041)
                  ·
                    refine ⟨4445471774476738682184781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5927295699302318242913041 4445471774476738682184781)
                    ·
                      refine ⟨1667051915428777005819293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445471774476738682184781 1667051915428777005819293)
                      ·
                        rfl

theorem cell23_3246572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 3].length) (baseStart_3246572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246572 prefixEnd_3246572 := by exact prefixLift 3246572
  have htrace : WordTrace (prefixWord ++ tailWord_3246572) baseStart_3246572 baseEnd_3246572 := by
    simpa [prefixWord, tailWord_3246572, baseEnd_3246572] using wordTrace_append hprefix tailTrace_3246572
  have hstable : (prefixWord ++ tailWord_3246572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246572).length < 2 ^ (prefixWord ++ tailWord_3246572).sum := by decide
  have hdescent : baseEnd_3246572 < baseStart_3246572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246589 : List Nat := [1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_3246589 : Nat := 118140960795 + 3246589 * 2 ^ 59
def prefixEnd_3246589 : Nat := 4983230072969 + 3 ^ 40 * 3246589 * 2
def baseEnd_3246589 : Nat := 1667060644599903439306715

theorem tailTrace_3246589 : CollatzResearch.WordTrace tailWord_3246589 prefixEnd_3246589 1667060644599903439306715 := by
  unfold tailWord_3246589
  simp only [CollatzResearch.WordTrace]
  refine ⟨118412828835170001102438821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78941885890113334068292547 118412828835170001102438821)
  ·
    refine ⟨22202405406594375206707279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118412828835170001102438821 22202405406594375206707279)
    ·
      refine ⟨33303608109891562810060919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22202405406594375206707279 33303608109891562810060919)
      ·
        refine ⟨49955412164837344215091379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33303608109891562810060919 49955412164837344215091379)
        ·
          refine ⟨74933118247256016322637069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49955412164837344215091379 74933118247256016322637069)
          ·
            refine ⟨28099919342721006120988901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74933118247256016322637069 28099919342721006120988901)
            ·
              refine ⟨5268734876760188647685419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28099919342721006120988901 5268734876760188647685419)
              ·
                refine ⟨7903102315140282971528129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268734876760188647685419 7903102315140282971528129)
                ·
                  refine ⟨5927326736355212228646097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7903102315140282971528129 5927326736355212228646097)
                  ·
                    refine ⟨4445495052266409171484573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5927326736355212228646097 4445495052266409171484573)
                    ·
                      refine ⟨1667060644599903439306715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445495052266409171484573 1667060644599903439306715)
                      ·
                        rfl

theorem cell23_3246589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_3246589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246589 prefixEnd_3246589 := by exact prefixLift 3246589
  have htrace : WordTrace (prefixWord ++ tailWord_3246589) baseStart_3246589 baseEnd_3246589 := by
    simpa [prefixWord, tailWord_3246589, baseEnd_3246589] using wordTrace_append hprefix tailTrace_3246589
  have hstable : (prefixWord ++ tailWord_3246589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246589).length < 2 ^ (prefixWord ++ tailWord_3246589).sum := by decide
  have hdescent : baseEnd_3246589 < baseStart_3246589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246629 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 4, 3, 2]
def baseStart_3246629 : Nat := 118140960795 + 3246629 * 2 ^ 59
def prefixEnd_3246629 : Nat := 4983230072969 + 3 ^ 40 * 3246629 * 2
def baseEnd_3246629 : Nat := 1667081183826083282806531

theorem tailTrace_3246629 : CollatzResearch.WordTrace tailWord_3246629 prefixEnd_3246629 1667081183826083282806531 := by
  unfold tailWord_3246629
  simp only [CollatzResearch.WordTrace]
  refine ⟨118414287755025087933894941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78942858503350058622596627 118414287755025087933894941)
  ·
    refine ⟨44405357908134407975210603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118414287755025087933894941 44405357908134407975210603)
    ·
      refine ⟨66608036862201611962815905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44405357908134407975210603 66608036862201611962815905)
      ·
        refine ⟨49956027646651208972111929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66608036862201611962815905 49956027646651208972111929)
        ·
          refine ⟨37467020734988406729083947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49956027646651208972111929 37467020734988406729083947)
          ·
            refine ⟨56200531102482610093625921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37467020734988406729083947 56200531102482610093625921)
            ·
              refine ⟨42150398326861957570219441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56200531102482610093625921 42150398326861957570219441)
              ·
                refine ⟨31612798745146468177664581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42150398326861957570219441 31612798745146468177664581)
                ·
                  refine ⟨5927399764714962783312109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31612798745146468177664581 5927399764714962783312109)
                  ·
                    refine ⟨2222774911768111043742041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5927399764714962783312109 2222774911768111043742041)
                    ·
                      refine ⟨1667081183826083282806531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222774911768111043742041 1667081183826083282806531)
                      ·
                        rfl

theorem cell23_3246629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 3, 2].length) (baseStart_3246629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246629 prefixEnd_3246629 := by exact prefixLift 3246629
  have htrace : WordTrace (prefixWord ++ tailWord_3246629) baseStart_3246629 baseEnd_3246629 := by
    simpa [prefixWord, tailWord_3246629, baseEnd_3246629] using wordTrace_append hprefix tailTrace_3246629
  have hstable : (prefixWord ++ tailWord_3246629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246629).length < 2 ^ (prefixWord ++ tailWord_3246629).sum := by decide
  have hdescent : baseEnd_3246629 < baseStart_3246629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246637 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3246637 : Nat := 118140960795 + 3246637 * 2 ^ 59
def prefixEnd_3246637 : Nat := 4983230072969 + 3 ^ 40 * 3246637 * 2
def baseEnd_3246637 : Nat := 1667085291671319251506495

theorem tailTrace_3246637 : CollatzResearch.WordTrace tailWord_3246637 prefixEnd_3246637 1667085291671319251506495 := by
  unfold tailWord_3246637
  simp only [CollatzResearch.WordTrace]
  refine ⟨118414579538996105300186165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78943053025997403533457443 118414579538996105300186165)
  ·
    refine ⟨11101366831780884871892453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118414579538996105300186165 11101366831780884871892453)
    ·
      refine ⟨2081506280958915913479835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11101366831780884871892453 2081506280958915913479835)
      ·
        refine ⟨3122259421438373870219753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081506280958915913479835 3122259421438373870219753)
        ·
          refine ⟨2341694566078780402664815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122259421438373870219753 2341694566078780402664815)
          ·
            refine ⟨3512541849118170603997223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341694566078780402664815 3512541849118170603997223)
            ·
              refine ⟨5268812773677255905995835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512541849118170603997223 5268812773677255905995835)
              ·
                refine ⟨7903219160515883858993753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268812773677255905995835 7903219160515883858993753)
                ·
                  refine ⟨5927414370386912894245315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7903219160515883858993753 5927414370386912894245315)
                  ·
                    refine ⟨8891121555580369341367973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927414370386912894245315 8891121555580369341367973)
                    ·
                      refine ⟨1667085291671319251506495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8891121555580369341367973 1667085291671319251506495)
                      ·
                        rfl

theorem cell23_3246637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3246637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246637 prefixEnd_3246637 := by exact prefixLift 3246637
  have htrace : WordTrace (prefixWord ++ tailWord_3246637) baseStart_3246637 baseEnd_3246637 := by
    simpa [prefixWord, tailWord_3246637, baseEnd_3246637] using wordTrace_append hprefix tailTrace_3246637
  have hstable : (prefixWord ++ tailWord_3246637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246637).length < 2 ^ (prefixWord ++ tailWord_3246637).sum := by decide
  have hdescent : baseEnd_3246637 < baseStart_3246637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246653 : List Nat := [1, 4, 1, 3, 2, 1, 1, 5, 1, 1, 3]
def baseStart_3246653 : Nat := 118140960795 + 3246653 * 2 ^ 59
def prefixEnd_3246653 : Nat := 4983230072969 + 3 ^ 40 * 3246653 * 2
def baseEnd_3246653 : Nat := 1667093507361791188906421

theorem tailTrace_3246653 : CollatzResearch.WordTrace tailWord_3246653 prefixEnd_3246653 1667093507361791188906421 := by
  unfold tailWord_3246653
  simp only [CollatzResearch.WordTrace]
  refine ⟨118415163106938140032768613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78943442071292093355179075 118415163106938140032768613)
  ·
    refine ⟨22202843082550901256144115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118415163106938140032768613 22202843082550901256144115)
    ·
      refine ⟨33304264623826351884216173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22202843082550901256144115 33304264623826351884216173)
      ·
        refine ⟨12489099233934881956581065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33304264623826351884216173 12489099233934881956581065)
        ·
          refine ⟨9366824425451161467435799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12489099233934881956581065 9366824425451161467435799)
          ·
            refine ⟨14050236638176742201153699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9366824425451161467435799 14050236638176742201153699)
            ·
              refine ⟨21075354957265113301730549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14050236638176742201153699 21075354957265113301730549)
              ·
                refine ⟨1975814527243604372037239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21075354957265113301730549 1975814527243604372037239)
                ·
                  refine ⟨2963721790865406558055859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975814527243604372037239 2963721790865406558055859)
                  ·
                    refine ⟨4445582686298109837083789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2963721790865406558055859 4445582686298109837083789)
                    ·
                      refine ⟨1667093507361791188906421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445582686298109837083789 1667093507361791188906421)
                      ·
                        rfl

theorem cell23_3246653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_3246653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246653 prefixEnd_3246653 := by exact prefixLift 3246653
  have htrace : WordTrace (prefixWord ++ tailWord_3246653) baseStart_3246653 baseEnd_3246653 := by
    simpa [prefixWord, tailWord_3246653, baseEnd_3246653] using wordTrace_append hprefix tailTrace_3246653
  have hstable : (prefixWord ++ tailWord_3246653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246653).length < 2 ^ (prefixWord ++ tailWord_3246653).sum := by decide
  have hdescent : baseEnd_3246653 < baseStart_3246653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246660 : List Nat := [2, 3, 5, 1, 1, 2, 1, 2, 6]
def baseStart_3246660 : Nat := 118140960795 + 3246660 * 2 ^ 59
def prefixEnd_3246660 : Nat := 4983230072969 + 3 ^ 40 * 3246660 * 2
def baseEnd_3246660 : Nat := 185233011302930295724321

theorem tailTrace_3246660 : CollatzResearch.WordTrace tailWord_3246660 prefixEnd_3246660 185233011302930295724321 := by
  unfold tailWord_3246660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59207709208956390114136717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78943612278608520152182289 59207709208956390114136717)
  ·
    refine ⟨22202890953358646292801269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59207709208956390114136717 22202890953358646292801269)
    ·
      refine ⟨2081521026877373089950119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22202890953358646292801269 2081521026877373089950119)
      ·
        refine ⟨3122281540316059634925179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081521026877373089950119 3122281540316059634925179)
        ·
          refine ⟨4683422310474089452387769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122281540316059634925179 4683422310474089452387769)
          ·
            refine ⟨3512566732855567089290827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4683422310474089452387769 3512566732855567089290827)
            ·
              refine ⟨5268850099283350633936241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3512566732855567089290827 5268850099283350633936241)
              ·
                refine ⟨3951637574462512975452181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5268850099283350633936241 3951637574462512975452181)
                ·
                  refine ⟨185233011302930295724321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3951637574462512975452181 185233011302930295724321)
                  ·
                    rfl

theorem cell23_3246660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 6].length) (baseStart_3246660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246660 prefixEnd_3246660 := by exact prefixLift 3246660
  have htrace : WordTrace (prefixWord ++ tailWord_3246660) baseStart_3246660 baseEnd_3246660 := by
    simpa [prefixWord, tailWord_3246660, baseEnd_3246660] using wordTrace_append hprefix tailTrace_3246660
  have hstable : (prefixWord ++ tailWord_3246660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246660).length < 2 ^ (prefixWord ++ tailWord_3246660).sum := by decide
  have hdescent : baseEnd_3246660 < baseStart_3246660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246689 : List Nat := [1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_3246689 : Nat := 118140960795 + 3246689 * 2 ^ 59
def prefixEnd_3246689 : Nat := 4983230072969 + 3 ^ 40 * 3246689 * 2
def baseEnd_3246689 : Nat := 1667111992665353048056255

theorem tailTrace_3246689 : CollatzResearch.WordTrace tailWord_3246689 prefixEnd_3246689 1667111992665353048056255 := by
  unfold tailWord_3246689
  simp only [CollatzResearch.WordTrace]
  refine ⟨118416476134807718181079121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78944317423205145454052747 118416476134807718181079121)
  ·
    refine ⟨88812357101105788635809341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118416476134807718181079121 88812357101105788635809341)
    ·
      refine ⟨33304633912914670738428503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88812357101105788635809341 33304633912914670738428503)
      ·
        refine ⟨49956950869372006107642755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33304633912914670738428503 49956950869372006107642755)
        ·
          refine ⟨74935426304058009161464133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49956950869372006107642755 74935426304058009161464133)
          ·
            refine ⟨14050392432010876717774525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74935426304058009161464133 14050392432010876717774525)
            ·
              refine ⟨5268897162004078769165447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14050392432010876717774525 5268897162004078769165447)
              ·
                refine ⟨7903345743006118153748171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268897162004078769165447 7903345743006118153748171)
                ·
                  refine ⟨11855018614509177230622257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903345743006118153748171 11855018614509177230622257)
                  ·
                    refine ⟨8891263960881882922966693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11855018614509177230622257 8891263960881882922966693)
                    ·
                      refine ⟨1667111992665353048056255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8891263960881882922966693 1667111992665353048056255)
                      ·
                        rfl

theorem cell23_3246689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_3246689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246689 prefixEnd_3246689 := by exact prefixLift 3246689
  have htrace : WordTrace (prefixWord ++ tailWord_3246689) baseStart_3246689 baseEnd_3246689 := by
    simpa [prefixWord, tailWord_3246689, baseEnd_3246689] using wordTrace_append hprefix tailTrace_3246689
  have hstable : (prefixWord ++ tailWord_3246689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246689).length < 2 ^ (prefixWord ++ tailWord_3246689).sum := by decide
  have hdescent : baseEnd_3246689 < baseStart_3246689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246753 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_3246753 : Nat := 118140960795 + 3246753 * 2 ^ 59
def prefixEnd_3246753 : Nat := 4983230072969 + 3 ^ 40 * 3246753 * 2
def baseEnd_3246753 : Nat := 1667144855427240797655961

theorem tailTrace_3246753 : CollatzResearch.WordTrace tailWord_3246753 prefixEnd_3246753 1667144855427240797655961 := by
  unfold tailWord_3246753
  simp only [CollatzResearch.WordTrace]
  refine ⟨118418810406575857111408913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78945873604383904740939275 118418810406575857111408913)
  ·
    refine ⟨88814107804931892833556685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118418810406575857111408913 88814107804931892833556685)
    ·
      refine ⟨33305290426849459812583757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88814107804931892833556685 33305290426849459812583757)
      ·
        refine ⟨12489483910068547429718909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33305290426849459812583757 12489483910068547429718909)
        ·
          refine ⟨4683556466275705286144591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12489483910068547429718909 4683556466275705286144591)
          ·
            refine ⟨7025334699413557929216887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683556466275705286144591 7025334699413557929216887)
            ·
              refine ⟨10538002049120336893825331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025334699413557929216887 10538002049120336893825331)
              ·
                refine ⟨15807003073680505340737997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538002049120336893825331 15807003073680505340737997)
                ·
                  refine ⟨5927626152630189502776749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15807003073680505340737997 5927626152630189502776749)
                  ·
                    refine ⟨2222859807236321063541281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5927626152630189502776749 2222859807236321063541281)
                    ·
                      refine ⟨1667144855427240797655961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222859807236321063541281 1667144855427240797655961)
                      ·
                        rfl

theorem cell23_3246753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_3246753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246753 prefixEnd_3246753 := by exact prefixLift 3246753
  have htrace : WordTrace (prefixWord ++ tailWord_3246753) baseStart_3246753 baseEnd_3246753 := by
    simpa [prefixWord, tailWord_3246753, baseEnd_3246753] using wordTrace_append hprefix tailTrace_3246753
  have hstable : (prefixWord ++ tailWord_3246753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246753).length < 2 ^ (prefixWord ++ tailWord_3246753).sum := by decide
  have hdescent : baseEnd_3246753 < baseStart_3246753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246783 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 2, 2, 2]
def baseStart_3246783 : Nat := 118140960795 + 3246783 * 2 ^ 59
def prefixEnd_3246783 : Nat := 4983230072969 + 3 ^ 40 * 3246783 * 2
def baseEnd_3246783 : Nat := 1667160259846875680280823

theorem tailTrace_3246783 : CollatzResearch.WordTrace tailWord_3246783 prefixEnd_3246783 1667160259846875680280823 := by
  unfold tailWord_3246783
  simp only [CollatzResearch.WordTrace]
  refine ⟨118419904596467172235001003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78946603064311448156667335 118419904596467172235001003)
  ·
    refine ⟨177629856894700758352501505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118419904596467172235001003 177629856894700758352501505)
    ·
      refine ⟨133222392671025568764376129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177629856894700758352501505 133222392671025568764376129)
      ·
        refine ⟨99916794503269176573282097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133222392671025568764376129 99916794503269176573282097)
        ·
          refine ⟨74937595877451882429961573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99916794503269176573282097 74937595877451882429961573)
          ·
            refine ⟨14050799227022227955617795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74937595877451882429961573 14050799227022227955617795)
            ·
              refine ⟨21076198840533341933426693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14050799227022227955617795 21076198840533341933426693)
              ·
                refine ⟨3951787282600001612517505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21076198840533341933426693 3951787282600001612517505)
                ·
                  refine ⟨2963840461950001209388129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3951787282600001612517505 2963840461950001209388129)
                  ·
                    refine ⟨2222880346462500907041097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2963840461950001209388129 2222880346462500907041097)
                    ·
                      refine ⟨1667160259846875680280823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2222880346462500907041097 1667160259846875680280823)
                      ·
                        rfl

theorem cell23_3246783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 2, 2].length) (baseStart_3246783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246783 prefixEnd_3246783 := by exact prefixLift 3246783
  have htrace : WordTrace (prefixWord ++ tailWord_3246783) baseStart_3246783 baseEnd_3246783 := by
    simpa [prefixWord, tailWord_3246783, baseEnd_3246783] using wordTrace_append hprefix tailTrace_3246783
  have hstable : (prefixWord ++ tailWord_3246783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246783).length < 2 ^ (prefixWord ++ tailWord_3246783).sum := by decide
  have hdescent : baseEnd_3246783 < baseStart_3246783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246796 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3246796 : Nat := 118140960795 + 3246796 * 2 ^ 59
def prefixEnd_3246796 : Nat := 4983230072969 + 3 ^ 40 * 3246796 * 2
def baseEnd_3246796 : Nat := 1667166935095384129418263

theorem tailTrace_3246796 : CollatzResearch.WordTrace tailWord_3246796 prefixEnd_3246796 1667166935095384129418263 := by
  unfold tailWord_3246796
  simp only [CollatzResearch.WordTrace]
  refine ⟨59210189372710037727612121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78946919163613383636816161 59210189372710037727612121)
  ·
    refine ⟨44407642029532528295709091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59210189372710037727612121 44407642029532528295709091)
    ·
      refine ⟨66611463044298792443563637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44407642029532528295709091 66611463044298792443563637)
      ·
        refine ⟨6244824660403011791584091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66611463044298792443563637 6244824660403011791584091)
        ·
          refine ⟨9367236990604517687376137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244824660403011791584091 9367236990604517687376137)
          ·
            refine ⟨7025427742953388265532103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367236990604517687376137 7025427742953388265532103)
            ·
              refine ⟨10538141614430082398298155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025427742953388265532103 10538141614430082398298155)
              ·
                refine ⟨15807212421645123597447233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538141614430082398298155 15807212421645123597447233)
                ·
                  refine ⟨11855409316233842698085425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15807212421645123597447233 11855409316233842698085425)
                  ·
                    refine ⟨8891556987175382023564069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11855409316233842698085425 8891556987175382023564069)
                    ·
                      refine ⟨1667166935095384129418263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8891556987175382023564069 1667166935095384129418263)
                      ·
                        rfl

theorem cell23_3246796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3246796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246796 prefixEnd_3246796 := by exact prefixLift 3246796
  have htrace : WordTrace (prefixWord ++ tailWord_3246796) baseStart_3246796 baseEnd_3246796 := by
    simpa [prefixWord, tailWord_3246796, baseEnd_3246796] using wordTrace_append hprefix tailTrace_3246796
  have hstable : (prefixWord ++ tailWord_3246796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246796).length < 2 ^ (prefixWord ++ tailWord_3246796).sum := by decide
  have hdescent : baseEnd_3246796 < baseStart_3246796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246839 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4]
def baseStart_3246839 : Nat := 118140960795 + 3246839 * 2 ^ 59
def prefixEnd_3246839 : Nat := 4983230072969 + 3 ^ 40 * 3246839 * 2
def baseEnd_3246839 : Nat := 1667189014763527461180565

theorem tailTrace_3246839 : CollatzResearch.WordTrace tailWord_3246839 prefixEnd_3246839 1667189014763527461180565 := by
  unfold tailWord_3246839
  simp only [CollatzResearch.WordTrace]
  refine ⟨118421947084264293799039571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78947964722842862532693047 118421947084264293799039571)
  ·
    refine ⟨177632920626396440698559357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118421947084264293799039571 177632920626396440698559357)
    ·
      refine ⟨66612345234898665261959759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177632920626396440698559357 66612345234898665261959759)
      ·
        refine ⟨99918517852347997892939639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66612345234898665261959759 99918517852347997892939639)
        ·
          refine ⟨149877776778521996839409459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99918517852347997892939639 149877776778521996839409459)
          ·
            refine ⟨224816665167782995259114189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149877776778521996839409459 224816665167782995259114189)
            ·
              refine ⟨84306249437918623222167821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224816665167782995259114189 84306249437918623222167821)
              ·
                refine ⟨31614843539219483708312933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84306249437918623222167821 31614843539219483708312933)
                ·
                  refine ⟨5927783163603653195308675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31614843539219483708312933 5927783163603653195308675)
                  ·
                    refine ⟨8891674745405479792963013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927783163603653195308675 8891674745405479792963013)
                    ·
                      refine ⟨1667189014763527461180565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8891674745405479792963013 1667189014763527461180565)
                      ·
                        rfl

theorem cell23_3246839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_3246839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246839 prefixEnd_3246839 := by exact prefixLift 3246839
  have htrace : WordTrace (prefixWord ++ tailWord_3246839) baseStart_3246839 baseEnd_3246839 := by
    simpa [prefixWord, tailWord_3246839, baseEnd_3246839] using wordTrace_append hprefix tailTrace_3246839
  have hstable : (prefixWord ++ tailWord_3246839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246839).length < 2 ^ (prefixWord ++ tailWord_3246839).sum := by decide
  have hdescent : baseEnd_3246839 < baseStart_3246839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246869 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3246869 : Nat := 118140960795 + 3246869 * 2 ^ 59
def prefixEnd_3246869 : Nat := 4983230072969 + 3 ^ 40 * 3246869 * 2
def baseEnd_3246869 : Nat := 1667204419183162343805427

theorem tailTrace_3246869 : CollatzResearch.WordTrace tailWord_3246869 prefixEnd_3246869 1667204419183162343805427 := by
  unfold tailWord_3246869
  simp only [CollatzResearch.WordTrace]
  refine ⟨118423041274155608922631661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78948694182770405948421107 118423041274155608922631661)
  ·
    refine ⟨44408640477808353345986873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118423041274155608922631661 44408640477808353345986873)
    ·
      refine ⟨33306480358356265009490155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44408640477808353345986873 33306480358356265009490155)
      ·
        refine ⟨49959720537534397514235233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33306480358356265009490155 49959720537534397514235233)
        ·
          refine ⟨37469790403150798135676425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49959720537534397514235233 37469790403150798135676425)
          ·
            refine ⟨28102342802363098601757319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37469790403150798135676425 28102342802363098601757319)
            ·
              refine ⟨42153514203544647902635979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28102342802363098601757319 42153514203544647902635979)
              ·
                refine ⟨63230271305316971853953969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42153514203544647902635979 63230271305316971853953969)
                ·
                  refine ⟨47422703478987728890465477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63230271305316971853953969 47422703478987728890465477)
                  ·
                    refine ⟨8891756902310199166962277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47422703478987728890465477 8891756902310199166962277)
                    ·
                      refine ⟨1667204419183162343805427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8891756902310199166962277 1667204419183162343805427)
                      ·
                        rfl

theorem cell23_3246869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3246869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246869 prefixEnd_3246869 := by exact prefixLift 3246869
  have htrace : WordTrace (prefixWord ++ tailWord_3246869) baseStart_3246869 baseEnd_3246869 := by
    simpa [prefixWord, tailWord_3246869, baseEnd_3246869] using wordTrace_append hprefix tailTrace_3246869
  have hstable : (prefixWord ++ tailWord_3246869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246869).length < 2 ^ (prefixWord ++ tailWord_3246869).sum := by decide
  have hdescent : baseEnd_3246869 < baseStart_3246869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246876 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 1, 4, 3]
def baseStart_3246876 : Nat := 118140960795 + 3246876 * 2 ^ 59
def prefixEnd_3246876 : Nat := 4983230072969 + 3 ^ 40 * 3246876 * 2
def baseEnd_3246876 : Nat := 1667208013547743816417895

theorem tailTrace_3246876 : CollatzResearch.WordTrace tailWord_3246876 prefixEnd_3246876 1667208013547743816417895 := by
  unfold tailWord_3246876
  simp only [CollatzResearch.WordTrace]
  refine ⟨59211648292565124559068241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78948864390086832745424321 59211648292565124559068241)
  ·
    refine ⟨44408736219423843419301181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59211648292565124559068241 44408736219423843419301181)
    ·
      refine ⟨16653276082283941282237943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44408736219423843419301181 16653276082283941282237943)
      ·
        refine ⟨24979914123425911923356915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16653276082283941282237943 24979914123425911923356915)
        ·
          refine ⟨37469871185138867885035373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24979914123425911923356915 37469871185138867885035373)
          ·
            refine ⟨14051201694427075456888265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37469871185138867885035373 14051201694427075456888265)
            ·
              refine ⟨10538401270820306592666199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14051201694427075456888265 10538401270820306592666199)
              ·
                refine ⟨15807601906230459888999299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538401270820306592666199 15807601906230459888999299)
                ·
                  refine ⟨23711402859345689833498949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15807601906230459888999299 23711402859345689833498949)
                  ·
                    refine ⟨4445888036127316843781053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23711402859345689833498949 4445888036127316843781053)
                    ·
                      refine ⟨1667208013547743816417895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445888036127316843781053 1667208013547743816417895)
                      ·
                        rfl

theorem cell23_3246876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_3246876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246876 prefixEnd_3246876 := by exact prefixLift 3246876
  have htrace : WordTrace (prefixWord ++ tailWord_3246876) baseStart_3246876 baseEnd_3246876 := by
    simpa [prefixWord, tailWord_3246876, baseEnd_3246876] using wordTrace_append hprefix tailTrace_3246876
  have hstable : (prefixWord ++ tailWord_3246876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246876).length < 2 ^ (prefixWord ++ tailWord_3246876).sum := by decide
  have hdescent : baseEnd_3246876 < baseStart_3246876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246879 : List Nat := [1, 1, 2, 4, 2, 2, 1, 2, 8]
def baseStart_3246879 : Nat := 118140960795 + 3246879 * 2 ^ 59
def prefixEnd_3246879 : Nat := 4983230072969 + 3 ^ 40 * 3246879 * 2
def baseEnd_3246879 : Nat := 185245505998856367186709

theorem tailTrace_3246879 : CollatzResearch.WordTrace tailWord_3246879 prefixEnd_3246879 185245505998856367186709 := by
  unfold tailWord_3246879
  simp only [CollatzResearch.WordTrace]
  refine ⟨118423406004119380630495691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78948937336079587086997127 118423406004119380630495691)
  ·
    refine ⟨177635109006179070945743537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118423406004119380630495691 177635109006179070945743537)
    ·
      refine ⟨133226331754634303209307653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177635109006179070945743537 133226331754634303209307653)
      ·
        refine ⟨24979937203993931851745185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133226331754634303209307653 24979937203993931851745185)
        ·
          refine ⟨18734952902995448888808889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24979937203993931851745185 18734952902995448888808889)
          ·
            refine ⟨14051214677246586666606667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18734952902995448888808889 14051214677246586666606667)
            ·
              refine ⟨21076822015869879999910001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14051214677246586666606667 21076822015869879999910001)
              ·
                refine ⟨15807616511902409999932501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21076822015869879999910001 15807616511902409999932501)
                ·
                  refine ⟨185245505998856367186709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15807616511902409999932501 185245505998856367186709)
                  ·
                    rfl

theorem cell23_3246879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 8].length) (baseStart_3246879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246879 prefixEnd_3246879 := by exact prefixLift 3246879
  have htrace : WordTrace (prefixWord ++ tailWord_3246879) baseStart_3246879 baseEnd_3246879 := by
    simpa [prefixWord, tailWord_3246879, baseEnd_3246879] using wordTrace_append hprefix tailTrace_3246879
  have hstable : (prefixWord ++ tailWord_3246879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246879).length < 2 ^ (prefixWord ++ tailWord_3246879).sum := by decide
  have hdescent : baseEnd_3246879 < baseStart_3246879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246889 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_3246889 : Nat := 118140960795 + 3246889 * 2 ^ 59
def prefixEnd_3246889 : Nat := 4983230072969 + 3 ^ 40 * 3246889 * 2
def baseEnd_3246889 : Nat := 1667214688796252265555335

theorem tailTrace_3246889 : CollatzResearch.WordTrace tailWord_3246889 prefixEnd_3246889 1667214688796252265555335 := by
  unfold tailWord_3246889
  simp only [CollatzResearch.WordTrace]
  refine ⟨118423770734083152338359721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78949180489388768225573147 118423770734083152338359721)
  ·
    refine ⟨88817828050562364253769791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118423770734083152338359721 88817828050562364253769791)
    ·
      refine ⟨133226742075843546380654687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88817828050562364253769791 133226742075843546380654687)
      ·
        refine ⟨199840113113765319570982031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133226742075843546380654687 199840113113765319570982031)
        ·
          refine ⟨299760169670647979356473047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199840113113765319570982031 299760169670647979356473047)
          ·
            refine ⟨449640254505971969034709571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299760169670647979356473047 449640254505971969034709571)
            ·
              refine ⟨674460381758957953552064357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449640254505971969034709571 674460381758957953552064357)
              ·
                refine ⟨126461321579804616291012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674460381758957953552064357 126461321579804616291012067)
                ·
                  refine ⟨189691982369706924436518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126461321579804616291012067 189691982369706924436518101)
                  ·
                    refine ⟨4445905836790006041480893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 189691982369706924436518101 4445905836790006041480893)
                    ·
                      refine ⟨1667214688796252265555335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4445905836790006041480893 1667214688796252265555335)
                      ·
                        rfl

theorem cell23_3246889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_3246889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246889 prefixEnd_3246889 := by exact prefixLift 3246889
  have htrace : WordTrace (prefixWord ++ tailWord_3246889) baseStart_3246889 baseEnd_3246889 := by
    simpa [prefixWord, tailWord_3246889, baseEnd_3246889] using wordTrace_append hprefix tailTrace_3246889
  have hstable : (prefixWord ++ tailWord_3246889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246889).length < 2 ^ (prefixWord ++ tailWord_3246889).sum := by decide
  have hdescent : baseEnd_3246889 < baseStart_3246889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246890 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3246890 : Nat := 118140960795 + 3246890 * 2 ^ 59
def prefixEnd_3246890 : Nat := 4983230072969 + 3 ^ 40 * 3246890 * 2
def baseEnd_3246890 : Nat := 1667215202276906761642831

theorem tailTrace_3246890 : CollatzResearch.WordTrace tailWord_3246890 prefixEnd_3246890 1667215202276906761642831 := by
  unfold tailWord_3246890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29605951801769882377286531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78949204804719686339430749 29605951801769882377286531)
  ·
    refine ⟨44408927702654823565929797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29605951801769882377286531 44408927702654823565929797)
    ·
      refine ⟨8326673944247779418611837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44408927702654823565929797 8326673944247779418611837)
      ·
        refine ⟨3122502729092917281979439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8326673944247779418611837 3122502729092917281979439)
        ·
          refine ⟨4683754093639375922969159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122502729092917281979439 4683754093639375922969159)
          ·
            refine ⟨7025631140459063884453739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683754093639375922969159 7025631140459063884453739)
            ·
              refine ⟨10538446710688595826680609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025631140459063884453739 10538446710688595826680609)
              ·
                refine ⟨7903835033016446870010457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10538446710688595826680609 7903835033016446870010457)
                ·
                  refine ⟨5927876274762335152507843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7903835033016446870010457 5927876274762335152507843)
                  ·
                    refine ⟨8891814412143502728761765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927876274762335152507843 8891814412143502728761765)
                    ·
                      refine ⟨1667215202276906761642831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8891814412143502728761765 1667215202276906761642831)
                      ·
                        rfl

theorem cell23_3246890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3246890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246890 prefixEnd_3246890 := by exact prefixLift 3246890
  have htrace : WordTrace (prefixWord ++ tailWord_3246890) baseStart_3246890 baseEnd_3246890 := by
    simpa [prefixWord, tailWord_3246890, baseEnd_3246890] using wordTrace_append hprefix tailTrace_3246890
  have hstable : (prefixWord ++ tailWord_3246890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246890).length < 2 ^ (prefixWord ++ tailWord_3246890).sum := by decide
  have hdescent : baseEnd_3246890 < baseStart_3246890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246943 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 1, 5]
def baseStart_3246943 : Nat := 118140960795 + 3246943 * 2 ^ 59
def prefixEnd_3246943 : Nat := 4983230072969 + 3 ^ 40 * 3246943 * 2
def baseEnd_3246943 : Nat := 555747472250531684760029

theorem tailTrace_3246943 : CollatzResearch.WordTrace tailWord_3246943 prefixEnd_3246943 555747472250531684760029 := by
  unfold tailWord_3246943
  simp only [CollatzResearch.WordTrace]
  refine ⟨118425740275887519560825483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78950493517258346373883655 118425740275887519560825483)
  ·
    refine ⟨177638610413831279341238225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118425740275887519560825483 177638610413831279341238225)
    ·
      refine ⟨133228957810373459505928669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177638610413831279341238225 133228957810373459505928669)
      ·
        refine ⟨49960859178890047314723251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133228957810373459505928669 49960859178890047314723251)
        ·
          refine ⟨74941288768335070972084877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49960859178890047314723251 74941288768335070972084877)
          ·
            refine ⟨28102983288125651614531829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74941288768335070972084877 28102983288125651614531829)
            ·
              refine ⟨2634654683261779838862359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28102983288125651614531829 2634654683261779838862359)
              ·
                refine ⟨3951982024892669758293539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634654683261779838862359 3951982024892669758293539)
                ·
                  refine ⟨5927973037339004637440309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951982024892669758293539 5927973037339004637440309)
                  ·
                    refine ⟨555747472250531684760029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5927973037339004637440309 555747472250531684760029)
                    ·
                      rfl

theorem cell23_3246943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 5].length) (baseStart_3246943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246943 prefixEnd_3246943 := by exact prefixLift 3246943
  have htrace : WordTrace (prefixWord ++ tailWord_3246943) baseStart_3246943 baseEnd_3246943 := by
    simpa [prefixWord, tailWord_3246943, baseEnd_3246943] using wordTrace_append hprefix tailTrace_3246943
  have hstable : (prefixWord ++ tailWord_3246943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246943).length < 2 ^ (prefixWord ++ tailWord_3246943).sum := by decide
  have hdescent : baseEnd_3246943 < baseStart_3246943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246959 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_3246959 : Nat := 118140960795 + 3246959 * 2 ^ 59
def prefixEnd_3246959 : Nat := 4983230072969 + 3 ^ 40 * 3246959 * 2
def baseEnd_3246959 : Nat := 1667250632442066991680013

theorem tailTrace_3246959 : CollatzResearch.WordTrace tailWord_3246959 prefixEnd_3246959 1667250632442066991680013 := by
  unfold tailWord_3246959
  simp only [CollatzResearch.WordTrace]
  refine ⟨118426323843829554293407931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78950882562553036195605287 118426323843829554293407931)
  ·
    refine ⟨177639485765744331440111897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118426323843829554293407931 177639485765744331440111897)
    ·
      refine ⟨133229614324308248580083923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177639485765744331440111897 133229614324308248580083923)
      ·
        refine ⟨199844421486462372870125885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133229614324308248580083923 199844421486462372870125885)
        ·
          refine ⟨74941658057423389826297207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199844421486462372870125885 74941658057423389826297207)
          ·
            refine ⟨112412487086135084739445811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74941658057423389826297207 112412487086135084739445811)
            ·
              refine ⟨168618730629202627109168717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112412487086135084739445811 168618730629202627109168717)
              ·
                refine ⟨63232023985950985165938269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168618730629202627109168717 63232023985950985165938269)
                ·
                  refine ⟨23712008994731619437226851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63232023985950985165938269 23712008994731619437226851)
                  ·
                    refine ⟨35568013492097429155840277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23712008994731619437226851 35568013492097429155840277)
                    ·
                      refine ⟨1667250632442066991680013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35568013492097429155840277 1667250632442066991680013)
                      ·
                        rfl

theorem cell23_3246959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_3246959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246959 prefixEnd_3246959 := by exact prefixLift 3246959
  have htrace : WordTrace (prefixWord ++ tailWord_3246959) baseStart_3246959 baseEnd_3246959 := by
    simpa [prefixWord, tailWord_3246959, baseEnd_3246959] using wordTrace_append hprefix tailTrace_3246959
  have hstable : (prefixWord ++ tailWord_3246959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246959).length < 2 ^ (prefixWord ++ tailWord_3246959).sum := by decide
  have hdescent : baseEnd_3246959 < baseStart_3246959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246973 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 2, 4]
def baseStart_3246973 : Nat := 118140960795 + 3246973 * 2 ^ 59
def prefixEnd_3246973 : Nat := 4983230072969 + 3 ^ 40 * 3246973 * 2
def baseEnd_3246973 : Nat := 555752607057076645634983

theorem tailTrace_3246973 : CollatzResearch.WordTrace tailWord_3246973 prefixEnd_3246973 555752607057076645634983 := by
  unfold tailWord_3246973
  simp only [CollatzResearch.WordTrace]
  refine ⟨118426834465778834684417573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78951222977185889789611715 118426834465778834684417573)
  ·
    refine ⟨22205031462333531503328295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118426834465778834684417573 22205031462333531503328295)
    ·
      refine ⟨33307547193500297254992443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22205031462333531503328295 33307547193500297254992443)
      ·
        refine ⟨49961320790250445882488665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33307547193500297254992443 49961320790250445882488665)
        ·
          refine ⟨37470990592687834411866499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49961320790250445882488665 37470990592687834411866499)
          ·
            refine ⟨56206485889031751617799749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37470990592687834411866499 56206485889031751617799749)
            ·
              refine ⟨10538716104193453428337453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56206485889031751617799749 10538716104193453428337453)
              ·
                refine ⟨3952018539072545035626545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10538716104193453428337453 3952018539072545035626545)
                ·
                  refine ⟨2964013904304408776719909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952018539072545035626545 2964013904304408776719909)
                  ·
                    refine ⟨555752607057076645634983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964013904304408776719909 555752607057076645634983)
                    ·
                      rfl

theorem cell23_3246973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_3246973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246973 prefixEnd_3246973 := by exact prefixLift 3246973
  have htrace : WordTrace (prefixWord ++ tailWord_3246973) baseStart_3246973 baseEnd_3246973 := by
    simpa [prefixWord, tailWord_3246973, baseEnd_3246973] using wordTrace_append hprefix tailTrace_3246973
  have hstable : (prefixWord ++ tailWord_3246973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246973).length < 2 ^ (prefixWord ++ tailWord_3246973).sum := by decide
  have hdescent : baseEnd_3246973 < baseStart_3246973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246983 : List Nat := [1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3]
def baseStart_3246983 : Nat := 118140960795 + 3246983 * 2 ^ 59
def prefixEnd_3246983 : Nat := 4983230072969 + 3 ^ 40 * 3246983 * 2
def baseEnd_3246983 : Nat := 1667262955977774897779903

theorem tailTrace_3246983 : CollatzResearch.WordTrace tailWord_3246983 prefixEnd_3246983 1667262955977774897779903 := by
  unfold tailWord_3246983
  simp only [CollatzResearch.WordTrace]
  refine ⟨118427199195742606392281603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78951466130495070928187735 118427199195742606392281603)
  ·
    refine ⟨177640798793613909588422405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118427199195742606392281603 177640798793613909588422405)
    ·
      refine ⟨33307649773802608047829201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177640798793613909588422405 33307649773802608047829201)
      ·
        refine ⟨24980737330351956035871901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33307649773802608047829201 24980737330351956035871901)
        ·
          refine ⟨9367776498881983513451963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24980737330351956035871901 9367776498881983513451963)
          ·
            refine ⟨14051664748322975270177945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9367776498881983513451963 14051664748322975270177945)
            ·
              refine ⟨10538748561242231452633459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14051664748322975270177945 10538748561242231452633459)
              ·
                refine ⟨15808122841863347178950189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538748561242231452633459 15808122841863347178950189)
                ·
                  refine ⟨5928046065698755192106321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15808122841863347178950189 5928046065698755192106321)
                  ·
                    refine ⟨4446034549274066394079741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928046065698755192106321 4446034549274066394079741)
                    ·
                      refine ⟨1667262955977774897779903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4446034549274066394079741 1667262955977774897779903)
                      ·
                        rfl

theorem cell23_3246983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 3].length) (baseStart_3246983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246983 prefixEnd_3246983 := by exact prefixLift 3246983
  have htrace : WordTrace (prefixWord ++ tailWord_3246983) baseStart_3246983 baseEnd_3246983 := by
    simpa [prefixWord, tailWord_3246983, baseEnd_3246983] using wordTrace_append hprefix tailTrace_3246983
  have hstable : (prefixWord ++ tailWord_3246983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246983).length < 2 ^ (prefixWord ++ tailWord_3246983).sum := by decide
  have hdescent : baseEnd_3246983 < baseStart_3246983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246994 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_3246994 : Nat := 118140960795 + 3246994 * 2 ^ 59
def prefixEnd_3246994 : Nat := 4983230072969 + 3 ^ 40 * 3246994 * 2
def baseEnd_3246994 : Nat := 555756201421658118247451

theorem tailTrace_3246994 : CollatzResearch.WordTrace tailWord_3246994 prefixEnd_3246994 555756201421658118247451 := by
  unfold tailWord_3246994
  simp only [CollatzResearch.WordTrace]
  refine ⟨29606900099675688817733009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78951733599135170180621357 29606900099675688817733009)
  ·
    refine ⟨22205175074756766613299757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29606900099675688817733009 22205175074756766613299757)
    ·
      refine ⟨8326940653033787479987409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22205175074756766613299757 8326940653033787479987409)
      ·
        refine ⟨6245205489775340609990557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8326940653033787479987409 6245205489775340609990557)
        ·
          refine ⟨2341952058665752728746459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6245205489775340609990557 2341952058665752728746459)
          ·
            refine ⟨3512928087998629093119689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341952058665752728746459 3512928087998629093119689)
            ·
              refine ⟨2634696065998971819839767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512928087998629093119689 2634696065998971819839767)
              ·
                refine ⟨3952044098998457729759651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634696065998971819839767 3952044098998457729759651)
                ·
                  refine ⟨5928066148497686594639477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952044098998457729759651 5928066148497686594639477)
                  ·
                    refine ⟨555756201421658118247451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5928066148497686594639477 555756201421658118247451)
                    ·
                      rfl

theorem cell23_3246994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_3246994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246994 prefixEnd_3246994 := by exact prefixLift 3246994
  have htrace : WordTrace (prefixWord ++ tailWord_3246994) baseStart_3246994 baseEnd_3246994 := by
    simpa [prefixWord, tailWord_3246994, baseEnd_3246994] using wordTrace_append hprefix tailTrace_3246994
  have hstable : (prefixWord ++ tailWord_3246994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246994).length < 2 ^ (prefixWord ++ tailWord_3246994).sum := by decide
  have hdescent : baseEnd_3246994 < baseStart_3246994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246997 : List Nat := [1, 3, 2, 1, 1, 4, 1, 5, 1, 2, 2]
def baseStart_3246997 : Nat := 118140960795 + 3246997 * 2 ^ 59
def prefixEnd_3246997 : Nat := 4983230072969 + 3 ^ 40 * 3246997 * 2
def baseEnd_3246997 : Nat := 1667270144706937843004839

theorem tailTrace_3246997 : CollatzResearch.WordTrace tailWord_3246997 prefixEnd_3246997 1667270144706937843004839 := by
  unfold tailWord_3246997
  simp only [CollatzResearch.WordTrace]
  refine ⟨118427709817691886783291245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78951806545127924522194163 118427709817691886783291245)
  ·
    refine ⟨44410391181634457543734217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118427709817691886783291245 44410391181634457543734217)
    ·
      refine ⟨33307793386225843157800663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44410391181634457543734217 33307793386225843157800663)
      ·
        refine ⟨49961690079338764736700995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33307793386225843157800663 49961690079338764736700995)
        ·
          refine ⟨74942535119008147105051493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49961690079338764736700995 74942535119008147105051493)
          ·
            refine ⟨14051725334814027582197155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74942535119008147105051493 14051725334814027582197155)
            ·
              refine ⟨21077588002221041373295733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14051725334814027582197155 21077588002221041373295733)
              ·
                refine ⟨1976023875208222628746475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21077588002221041373295733 1976023875208222628746475)
                ·
                  refine ⟨2964035812812333943119713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976023875208222628746475 2964035812812333943119713)
                  ·
                    refine ⟨2223026859609250457339785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964035812812333943119713 2223026859609250457339785)
                    ·
                      refine ⟨1667270144706937843004839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223026859609250457339785 1667270144706937843004839)
                      ·
                        rfl

theorem cell23_3246997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_3246997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3246997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3246997 prefixEnd_3246997 := by exact prefixLift 3246997
  have htrace : WordTrace (prefixWord ++ tailWord_3246997) baseStart_3246997 baseEnd_3246997 := by
    simpa [prefixWord, tailWord_3246997, baseEnd_3246997] using wordTrace_append hprefix tailTrace_3246997
  have hstable : (prefixWord ++ tailWord_3246997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246997).length < 2 ^ (prefixWord ++ tailWord_3246997).sum := by decide
  have hdescent : baseEnd_3246997 < baseStart_3246997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247023 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 3, 3, 2]
def baseStart_3247023 : Nat := 118140960795 + 3247023 * 2 ^ 59
def prefixEnd_3247023 : Nat := 4983230072969 + 3 ^ 40 * 3247023 * 2
def baseEnd_3247023 : Nat := 1667283495203954741279719

theorem tailTrace_3247023 : CollatzResearch.WordTrace tailWord_3247023 prefixEnd_3247023 1667283495203954741279719 := by
  unfold tailWord_3247023
  simp only [CollatzResearch.WordTrace]
  refine ⟨118428658115597693223737723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78952438743731795482491815 118428658115597693223737723)
  ·
    refine ⟨177642987173396539835606585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118428658115597693223737723 177642987173396539835606585)
    ·
      refine ⟨133232240380047404876704939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177642987173396539835606585 133232240380047404876704939)
      ·
        refine ⟨199848360570071107315057409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133232240380047404876704939 199848360570071107315057409)
        ·
          refine ⟨149886270427553330486293057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199848360570071107315057409 149886270427553330486293057)
          ·
            refine ⟨112414702820664997864719793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149886270427553330486293057 112414702820664997864719793)
            ·
              refine ⟨84311027115498748398539845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112414702820664997864719793 84311027115498748398539845)
              ·
                refine ⟨15808317584156015324726221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84311027115498748398539845 15808317584156015324726221)
                ·
                  refine ⟨5928119094058505746772333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15808317584156015324726221 5928119094058505746772333)
                  ·
                    refine ⟨2223044660271939655039625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5928119094058505746772333 2223044660271939655039625)
                    ·
                      refine ⟨1667283495203954741279719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223044660271939655039625 1667283495203954741279719)
                      ·
                        rfl

theorem cell23_3247023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 3, 2].length) (baseStart_3247023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247023 prefixEnd_3247023 := by exact prefixLift 3247023
  have htrace : WordTrace (prefixWord ++ tailWord_3247023) baseStart_3247023 baseEnd_3247023 := by
    simpa [prefixWord, tailWord_3247023, baseEnd_3247023] using wordTrace_append hprefix tailTrace_3247023
  have hstable : (prefixWord ++ tailWord_3247023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247023).length < 2 ^ (prefixWord ++ tailWord_3247023).sum := by decide
  have hdescent : baseEnd_3247023 < baseStart_3247023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247040 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2]
def baseStart_3247040 : Nat := 118140960795 + 3247040 * 2 ^ 59
def prefixEnd_3247040 : Nat := 4983230072969 + 3 ^ 40 * 3247040 * 2
def baseEnd_3247040 : Nat := 1667292224375081174767141

theorem tailTrace_3247040 : CollatzResearch.WordTrace tailWord_3247040 prefixEnd_3247040 1667292224375081174767141 := by
  unfold tailWord_3247040
  simp only [CollatzResearch.WordTrace]
  refine ⟨59214639078268052563553287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78952852104357403418071049 59214639078268052563553287)
  ·
    refine ⟨88821958617402078845329931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59214639078268052563553287 88821958617402078845329931)
    ·
      refine ⟨133232937926103118267994897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88821958617402078845329931 133232937926103118267994897)
      ·
        refine ⟨99924703444577338700996173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133232937926103118267994897 99924703444577338700996173)
        ·
          refine ⟨37471763791716502012873565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99924703444577338700996173 37471763791716502012873565)
          ·
            refine ⟨14051911421893688254827587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37471763791716502012873565 14051911421893688254827587)
            ·
              refine ⟨21077867132840532382241381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14051911421893688254827587 21077867132840532382241381)
              ·
                refine ⟨3952100087407599821670259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21077867132840532382241381 3952100087407599821670259)
                ·
                  refine ⟨5928150131111399732505389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952100087407599821670259 5928150131111399732505389)
                  ·
                    refine ⟨2223056299166774899689521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5928150131111399732505389 2223056299166774899689521)
                    ·
                      refine ⟨1667292224375081174767141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223056299166774899689521 1667292224375081174767141)
                      ·
                        rfl

theorem cell23_3247040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_3247040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247040 prefixEnd_3247040 := by exact prefixLift 3247040
  have htrace : WordTrace (prefixWord ++ tailWord_3247040) baseStart_3247040 baseEnd_3247040 := by
    simpa [prefixWord, tailWord_3247040, baseEnd_3247040] using wordTrace_append hprefix tailTrace_3247040
  have hstable : (prefixWord ++ tailWord_3247040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247040).length < 2 ^ (prefixWord ++ tailWord_3247040).sum := by decide
  have hdescent : baseEnd_3247040 < baseStart_3247040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247056 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3]
def baseStart_3247056 : Nat := 118140960795 + 3247056 * 2 ^ 59
def prefixEnd_3247056 : Nat := 4983230072969 + 3 ^ 40 * 3247056 * 2
def baseEnd_3247056 : Nat := 1667300440065553112167067

theorem tailTrace_3247056 : CollatzResearch.WordTrace tailWord_3247056 prefixEnd_3247056 1667300440065553112167067 := by
  unfold tailWord_3247056
  simp only [CollatzResearch.WordTrace]
  refine ⟨59214930862239069929844511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78953241149652093239792681 59214930862239069929844511)
  ·
    refine ⟨88822396293358604894766767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59214930862239069929844511 88822396293358604894766767)
    ·
      refine ⟨133233594440037907342150151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88822396293358604894766767 133233594440037907342150151)
      ·
        refine ⟨199850391660056861013225227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133233594440037907342150151 199850391660056861013225227)
        ·
          refine ⟨299775587490085291519837841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199850391660056861013225227 299775587490085291519837841)
          ·
            refine ⟨224831690617563968639878381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299775587490085291519837841 224831690617563968639878381)
            ·
              refine ⟨84311883981586488239954393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224831690617563968639878381 84311883981586488239954393)
              ·
                refine ⟨63233912986189866179965795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84311883981586488239954393 63233912986189866179965795)
                ·
                  refine ⟨94850869479284799269948693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63233912986189866179965795 94850869479284799269948693)
                  ·
                    refine ⟨4446134506841474965778845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94850869479284799269948693 4446134506841474965778845)
                    ·
                      refine ⟨1667300440065553112167067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4446134506841474965778845 1667300440065553112167067)
                      ·
                        rfl

theorem cell23_3247056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 3].length) (baseStart_3247056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247056 prefixEnd_3247056 := by exact prefixLift 3247056
  have htrace : WordTrace (prefixWord ++ tailWord_3247056) baseStart_3247056 baseEnd_3247056 := by
    simpa [prefixWord, tailWord_3247056, baseEnd_3247056] using wordTrace_append hprefix tailTrace_3247056
  have hstable : (prefixWord ++ tailWord_3247056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247056).length < 2 ^ (prefixWord ++ tailWord_3247056).sum := by decide
  have hdescent : baseEnd_3247056 < baseStart_3247056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247076 : List Nat := [2, 3, 1, 1, 1, 1, 2, 5, 7]
def baseStart_3247076 : Nat := 118140960795 + 3247076 * 2 ^ 59
def prefixEnd_3247076 : Nat := 4983230072969 + 3 ^ 40 * 3247076 * 2
def baseEnd_3247076 : Nat := 185256745519849225990775

theorem tailTrace_3247076 : CollatzResearch.WordTrace tailWord_3247076 prefixEnd_3247076 185256745519849225990775 := by
  unfold tailWord_3247076
  simp only [CollatzResearch.WordTrace]
  refine ⟨59215295592202841637708541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78953727456270455516944721 59215295592202841637708541)
  ·
    refine ⟨22205735847076065614140703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59215295592202841637708541 22205735847076065614140703)
    ·
      refine ⟨33308603770614098421211055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22205735847076065614140703 33308603770614098421211055)
      ·
        refine ⟨49962905655921147631816583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33308603770614098421211055 49962905655921147631816583)
        ·
          refine ⟨74944358483881721447724875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49962905655921147631816583 74944358483881721447724875)
          ·
            refine ⟨112416537725822582171587313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74944358483881721447724875 112416537725822582171587313)
            ·
              refine ⟨84312403294366936628690485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112416537725822582171587313 84312403294366936628690485)
              ·
                refine ⟨7904287808846900308939733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84312403294366936628690485 7904287808846900308939733)
                ·
                  refine ⟨185256745519849225990775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7904287808846900308939733 185256745519849225990775)
                  ·
                    rfl

theorem cell23_3247076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_3247076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247076 prefixEnd_3247076 := by exact prefixLift 3247076
  have htrace : WordTrace (prefixWord ++ tailWord_3247076) baseStart_3247076 baseEnd_3247076 := by
    simpa [prefixWord, tailWord_3247076, baseEnd_3247076] using wordTrace_append hprefix tailTrace_3247076
  have hstable : (prefixWord ++ tailWord_3247076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247076).length < 2 ^ (prefixWord ++ tailWord_3247076).sum := by decide
  have hdescent : baseEnd_3247076 < baseStart_3247076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247087 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 2, 2, 2]
def baseStart_3247087 : Nat := 118140960795 + 3247087 * 2 ^ 59
def prefixEnd_3247087 : Nat := 4983230072969 + 3 ^ 40 * 3247087 * 2
def baseEnd_3247087 : Nat := 1667316357965842490879425

theorem tailTrace_3247087 : CollatzResearch.WordTrace tailWord_3247087 prefixEnd_3247087 1667316357965842490879425 := by
  unfold tailWord_3247087
  simp only [CollatzResearch.WordTrace]
  refine ⟨118430992387365832154067515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78953994924910554769378343 118430992387365832154067515)
  ·
    refine ⟨177646488581048748231101273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118430992387365832154067515 177646488581048748231101273)
    ·
      refine ⟨133234866435786561173325955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177646488581048748231101273 133234866435786561173325955)
      ·
        refine ⟨199852299653679841759988933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133234866435786561173325955 199852299653679841759988933)
        ·
          refine ⟨37472306185064970329997925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199852299653679841759988933 37472306185064970329997925)
          ·
            refine ⟨7026057409699681936874611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37472306185064970329997925 7026057409699681936874611)
            ·
              refine ⟨10539086114549522905311917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026057409699681936874611 10539086114549522905311917)
              ·
                refine ⟨3952157292956071089491969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10539086114549522905311917 3952157292956071089491969)
                ·
                  refine ⟨2964117969717053317118977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952157292956071089491969 2964117969717053317118977)
                  ·
                    refine ⟨2223088477287789987839233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964117969717053317118977 2223088477287789987839233)
                    ·
                      refine ⟨1667316357965842490879425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223088477287789987839233 1667316357965842490879425)
                      ·
                        rfl

theorem cell23_3247087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 2, 2, 2].length) (baseStart_3247087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247087 prefixEnd_3247087 := by exact prefixLift 3247087
  have htrace : WordTrace (prefixWord ++ tailWord_3247087) baseStart_3247087 baseEnd_3247087 := by
    simpa [prefixWord, tailWord_3247087, baseEnd_3247087] using wordTrace_append hprefix tailTrace_3247087
  have hstable : (prefixWord ++ tailWord_3247087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247087).length < 2 ^ (prefixWord ++ tailWord_3247087).sum := by decide
  have hdescent : baseEnd_3247087 < baseStart_3247087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247113 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 4, 5, 2]
def baseStart_3247113 : Nat := 118140960795 + 3247113 * 2 ^ 59
def prefixEnd_3247113 : Nat := 4983230072969 + 3 ^ 40 * 3247113 * 2
def baseEnd_3247113 : Nat := 1667329708462859389154305

theorem tailTrace_3247113 : CollatzResearch.WordTrace tailWord_3247113 prefixEnd_3247113 1667329708462859389154305 := by
  unfold tailWord_3247113
  simp only [CollatzResearch.WordTrace]
  refine ⟨118431940685271638594513993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78954627123514425729675995 118431940685271638594513993)
  ·
    refine ⟨88823955513953728945885495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118431940685271638594513993 88823955513953728945885495)
    ·
      refine ⟨133235933270930593418828243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88823955513953728945885495 133235933270930593418828243)
      ·
        refine ⟨199853899906395890128242365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133235933270930593418828243 199853899906395890128242365)
        ·
          refine ⟨74945212464898458798090887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199853899906395890128242365 74945212464898458798090887)
          ·
            refine ⟨112417818697347688197136331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74945212464898458798090887 112417818697347688197136331)
            ·
              refine ⟨168626728046021532295704497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112417818697347688197136331 168626728046021532295704497)
              ·
                refine ⟨126470046034516149221778373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168626728046021532295704497 126470046034516149221778373)
                ·
                  refine ⟨23713133631471777979083445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126470046034516149221778373 23713133631471777979083445)
                  ·
                    refine ⟨2223106277950479185539073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23713133631471777979083445 2223106277950479185539073)
                    ·
                      refine ⟨1667329708462859389154305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223106277950479185539073 1667329708462859389154305)
                      ·
                        rfl

theorem cell23_3247113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 5, 2].length) (baseStart_3247113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247113 prefixEnd_3247113 := by exact prefixLift 3247113
  have htrace : WordTrace (prefixWord ++ tailWord_3247113) baseStart_3247113 baseEnd_3247113 := by
    simpa [prefixWord, tailWord_3247113, baseEnd_3247113] using wordTrace_append hprefix tailTrace_3247113
  have hstable : (prefixWord ++ tailWord_3247113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247113).length < 2 ^ (prefixWord ++ tailWord_3247113).sum := by decide
  have hdescent : baseEnd_3247113 < baseStart_3247113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247127 : List Nat := [1, 1, 3, 5, 1, 1, 4, 2, 5]
def baseStart_3247127 : Nat := 118140960795 + 3247127 * 2 ^ 59
def prefixEnd_3247127 : Nat := 4983230072969 + 3 ^ 40 * 3247127 * 2
def baseEnd_3247127 : Nat := 185259655243558037153249

theorem tailTrace_3247127 : CollatzResearch.WordTrace tailWord_3247127 prefixEnd_3247127 185259655243558037153249 := by
  unfold tailWord_3247127
  simp only [CollatzResearch.WordTrace]
  refine ⟨118432451307220918985523635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78954967538147279323682423 118432451307220918985523635)
  ·
    refine ⟨177648676960831378478285453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118432451307220918985523635 177648676960831378478285453)
    ·
      refine ⟨66618253860311766929357045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177648676960831378478285453 66618253860311766929357045)
      ·
        refine ⟨6245461299404228149627223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66618253860311766929357045 6245461299404228149627223)
        ·
          refine ⟨9368191949106342224440835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245461299404228149627223 9368191949106342224440835)
          ·
            refine ⟨14052287923659513336661253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368191949106342224440835 14052287923659513336661253)
            ·
              refine ⟨2634803985686158750623985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14052287923659513336661253 2634803985686158750623985)
              ·
                refine ⟨1976102989264619062967989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2634803985686158750623985 1976102989264619062967989)
                ·
                  refine ⟨185259655243558037153249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1976102989264619062967989 185259655243558037153249)
                  ·
                    rfl

theorem cell23_3247127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 4, 2, 5].length) (baseStart_3247127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247127 prefixEnd_3247127 := by exact prefixLift 3247127
  have htrace : WordTrace (prefixWord ++ tailWord_3247127) baseStart_3247127 baseEnd_3247127 := by
    simpa [prefixWord, tailWord_3247127, baseEnd_3247127] using wordTrace_append hprefix tailTrace_3247127
  have hstable : (prefixWord ++ tailWord_3247127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247127).length < 2 ^ (prefixWord ++ tailWord_3247127).sum := by decide
  have hdescent : baseEnd_3247127 < baseStart_3247127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247160 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4]
def baseStart_3247160 : Nat := 118140960795 + 3247160 * 2 ^ 59
def prefixEnd_3247160 : Nat := 4983230072969 + 3 ^ 40 * 3247160 * 2
def baseEnd_3247160 : Nat := 1667353842053620705266589

theorem tailTrace_3247160 : CollatzResearch.WordTrace tailWord_3247160 prefixEnd_3247160 1667353842053620705266589 := by
  unfold tailWord_3247160
  simp only [CollatzResearch.WordTrace]
  refine ⟨59216827458050682810737467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78955769944067577080983289 59216827458050682810737467)
  ·
    refine ⟨88825241187076024216106201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59216827458050682810737467 88825241187076024216106201)
    ·
      refine ⟨66618930890307018162079651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88825241187076024216106201 66618930890307018162079651)
      ·
        refine ⟨99928396335460527243119477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66618930890307018162079651 99928396335460527243119477)
        ·
          refine ⟨9368287156449424429042451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99928396335460527243119477 9368287156449424429042451)
          ·
            refine ⟨14052430734674136643563677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368287156449424429042451 14052430734674136643563677)
            ·
              refine ⟨5269661525502801241336379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14052430734674136643563677 5269661525502801241336379)
              ·
                refine ⟨7904492288254201862004569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269661525502801241336379 7904492288254201862004569)
                ·
                  refine ⟨5928369216190651396503427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904492288254201862004569 5928369216190651396503427)
                  ·
                    refine ⟨8892553824285977094755141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928369216190651396503427 8892553824285977094755141)
                    ·
                      refine ⟨1667353842053620705266589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8892553824285977094755141 1667353842053620705266589)
                      ·
                        rfl

theorem cell23_3247160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_3247160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247160 prefixEnd_3247160 := by exact prefixLift 3247160
  have htrace : WordTrace (prefixWord ++ tailWord_3247160) baseStart_3247160 baseEnd_3247160 := by
    simpa [prefixWord, tailWord_3247160, baseEnd_3247160] using wordTrace_append hprefix tailTrace_3247160
  have hstable : (prefixWord ++ tailWord_3247160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247160).length < 2 ^ (prefixWord ++ tailWord_3247160).sum := by decide
  have hdescent : baseEnd_3247160 < baseStart_3247160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247200 : List Nat := [2, 1, 1, 3, 2, 2, 5, 1, 6]
def baseStart_3247200 : Nat := 118140960795 + 3247200 * 2 ^ 59
def prefixEnd_3247200 : Nat := 4983230072969 + 3 ^ 40 * 3247200 * 2
def baseEnd_3247200 : Nat := 185263820142200060974045

theorem tailTrace_3247200 : CollatzResearch.WordTrace tailWord_3247200 prefixEnd_3247200 185263820142200060974045 := by
  unfold tailWord_3247200
  simp only [CollatzResearch.WordTrace]
  refine ⟨59217556917978226226465527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78956742557304301635287369 59217556917978226226465527)
  ·
    refine ⟨88826335376967339339698291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59217556917978226226465527 88826335376967339339698291)
    ·
      refine ⟨133239503065451009009547437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88826335376967339339698291 133239503065451009009547437)
      ·
        refine ⟨49964813649544128378580289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133239503065451009009547437 49964813649544128378580289)
        ·
          refine ⟨37473610237158096283935217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49964813649544128378580289 37473610237158096283935217)
          ·
            refine ⟨28105207677868572212951413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37473610237158096283935217 28105207677868572212951413)
            ·
              refine ⟨2634863219800178644964195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28105207677868572212951413 2634863219800178644964195)
              ·
                refine ⟨3952294829700267967446293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2634863219800178644964195 3952294829700267967446293)
                ·
                  refine ⟨185263820142200060974045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3952294829700267967446293 185263820142200060974045)
                  ·
                    rfl

theorem cell23_3247200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 6].length) (baseStart_3247200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247200 prefixEnd_3247200 := by exact prefixLift 3247200
  have htrace : WordTrace (prefixWord ++ tailWord_3247200) baseStart_3247200 baseEnd_3247200 := by
    simpa [prefixWord, tailWord_3247200, baseEnd_3247200] using wordTrace_append hprefix tailTrace_3247200
  have hstable : (prefixWord ++ tailWord_3247200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247200).length < 2 ^ (prefixWord ++ tailWord_3247200).sum := by decide
  have hdescent : baseEnd_3247200 < baseStart_3247200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247253 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3247253 : Nat := 118140960795 + 3247253 * 2 ^ 59
def prefixEnd_3247253 : Nat := 4983230072969 + 3 ^ 40 * 3247253 * 2
def baseEnd_3247253 : Nat := 1667401595754488841403661

theorem tailTrace_3247253 : CollatzResearch.WordTrace tailWord_3247253 prefixEnd_3247253 1667401595754488841403661 := by
  unfold tailWord_3247253
  simp only [CollatzResearch.WordTrace]
  refine ⟨118437046904764442504610413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78958031269842961669740275 118437046904764442504610413)
  ·
    refine ⟨44413892589286665939228905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118437046904764442504610413 44413892589286665939228905)
    ·
      refine ⟨33310419441964999454421679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44413892589286665939228905 33310419441964999454421679)
      ·
        refine ⟨49965629162947499181632519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33310419441964999454421679 49965629162947499181632519)
        ·
          refine ⟨74948443744421248772448779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49965629162947499181632519 74948443744421248772448779)
          ·
            refine ⟨112422665616631873158673169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74948443744421248772448779 112422665616631873158673169)
            ·
              refine ⟨84316999212473904869004877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112422665616631873158673169 84316999212473904869004877)
              ·
                refine ⟨31618874704677714325876829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84316999212473904869004877 31618874704677714325876829)
                ·
                  refine ⟨11857078014254142872203811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31618874704677714325876829 11857078014254142872203811)
                  ·
                    refine ⟨17785617021381214308305717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11857078014254142872203811 17785617021381214308305717)
                    ·
                      refine ⟨1667401595754488841403661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17785617021381214308305717 1667401595754488841403661)
                      ·
                        rfl

theorem cell23_3247253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3247253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247253 prefixEnd_3247253 := by exact prefixLift 3247253
  have htrace : WordTrace (prefixWord ++ tailWord_3247253) baseStart_3247253 baseEnd_3247253 := by
    simpa [prefixWord, tailWord_3247253, baseEnd_3247253] using wordTrace_append hprefix tailTrace_3247253
  have hstable : (prefixWord ++ tailWord_3247253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247253).length < 2 ^ (prefixWord ++ tailWord_3247253).sum := by decide
  have hdescent : baseEnd_3247253 < baseStart_3247253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247267 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 3, 2, 2]
def baseStart_3247267 : Nat := 118140960795 + 3247267 * 2 ^ 59
def prefixEnd_3247267 : Nat := 4983230072969 + 3 ^ 40 * 3247267 * 2
def baseEnd_3247267 : Nat := 1667408784483651786628597

theorem tailTrace_3247267 : CollatzResearch.WordTrace tailWord_3247267 prefixEnd_3247267 1667408784483651786628597 := by
  unfold tailWord_3247267
  simp only [CollatzResearch.WordTrace]
  refine ⟨118437557526713722895620055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78958371684475815263746703 118437557526713722895620055)
  ·
    refine ⟨177656336290070584343430083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118437557526713722895620055 177656336290070584343430083)
    ·
      refine ⟨266484504435105876515145125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177656336290070584343430083 266484504435105876515145125)
      ·
        refine ⟨49965844581582351846589711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266484504435105876515145125 49965844581582351846589711)
        ·
          refine ⟨74948766872373527769884567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49965844581582351846589711 74948766872373527769884567)
          ·
            refine ⟨112423150308560291654826851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74948766872373527769884567 112423150308560291654826851)
            ·
              refine ⟨168634725462840437482240277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112423150308560291654826851 168634725462840437482240277)
              ·
                refine ⟨7904752756070645506980013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168634725462840437482240277 7904752756070645506980013)
                ·
                  refine ⟨2964282283526492065117505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7904752756070645506980013 2964282283526492065117505)
                  ·
                    refine ⟨2223211712644869048838129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964282283526492065117505 2223211712644869048838129)
                    ·
                      refine ⟨1667408784483651786628597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223211712644869048838129 1667408784483651786628597)
                      ·
                        rfl

theorem cell23_3247267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_3247267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247267 prefixEnd_3247267 := by exact prefixLift 3247267
  have htrace : WordTrace (prefixWord ++ tailWord_3247267) baseStart_3247267 baseEnd_3247267 := by
    simpa [prefixWord, tailWord_3247267, baseEnd_3247267] using wordTrace_append hprefix tailTrace_3247267
  have hstable : (prefixWord ++ tailWord_3247267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247267).length < 2 ^ (prefixWord ++ tailWord_3247267).sum := by decide
  have hdescent : baseEnd_3247267 < baseStart_3247267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247277 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3247277 : Nat := 118140960795 + 3247277 * 2 ^ 59
def prefixEnd_3247277 : Nat := 4983230072969 + 3 ^ 40 * 3247277 * 2
def baseEnd_3247277 : Nat := 555804639763398915834517

theorem tailTrace_3247277 : CollatzResearch.WordTrace tailWord_3247277 prefixEnd_3247277 555804639763398915834517 := by
  unfold tailWord_3247277
  simp only [CollatzResearch.WordTrace]
  refine ⟨118437922256677494603484085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78958614837784996402322723 118437922256677494603484085)
  ·
    refine ⟨11103555211563515119076633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118437922256677494603484085 11103555211563515119076633)
    ·
      refine ⟨8327666408672636339307475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11103555211563515119076633 8327666408672636339307475)
      ·
        refine ⟨12491499613008954508961213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8327666408672636339307475 12491499613008954508961213)
        ·
          refine ⟨4684312354878357940860455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12491499613008954508961213 4684312354878357940860455)
          ·
            refine ⟨7026468532317536911290683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684312354878357940860455 7026468532317536911290683)
            ·
              refine ⟨10539702798476305366936025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026468532317536911290683 10539702798476305366936025)
              ·
                refine ⟨7904777098857229025202019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10539702798476305366936025 7904777098857229025202019)
                ·
                  refine ⟨11857165648285843537803029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904777098857229025202019 11857165648285843537803029)
                  ·
                    refine ⟨555804639763398915834517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11857165648285843537803029 555804639763398915834517)
                    ·
                      rfl

theorem cell23_3247277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3247277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247277 prefixEnd_3247277 := by exact prefixLift 3247277
  have htrace : WordTrace (prefixWord ++ tailWord_3247277) baseStart_3247277 baseEnd_3247277 := by
    simpa [prefixWord, tailWord_3247277, baseEnd_3247277] using wordTrace_append hprefix tailTrace_3247277
  have hstable : (prefixWord ++ tailWord_3247277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247277).length < 2 ^ (prefixWord ++ tailWord_3247277).sum := by decide
  have hdescent : baseEnd_3247277 < baseStart_3247277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247294 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_3247294 : Nat := 118140960795 + 3247294 * 2 ^ 59
def prefixEnd_3247294 : Nat := 4983230072969 + 3 ^ 40 * 3247294 * 2
def baseEnd_3247294 : Nat := 555807549487107726996991

theorem tailTrace_3247294 : CollatzResearch.WordTrace tailWord_3247294 prefixEnd_3247294 555807549487107726996991 := by
  unfold tailWord_3247294
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804817787201988313356617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78959028198410604337901957 14804817787201988313356617)
  ·
    refine ⟨11103613340401491235017463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14804817787201988313356617 11103613340401491235017463)
    ·
      refine ⟨16655420010602236852526195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11103613340401491235017463 16655420010602236852526195)
      ·
        refine ⟨24983130015903355278789293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16655420010602236852526195 24983130015903355278789293)
        ·
          refine ⟨9368673755963758229545985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24983130015903355278789293 9368673755963758229545985)
          ·
            refine ⟨7026505316972818672159489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9368673755963758229545985 7026505316972818672159489)
            ·
              refine ⟨5269878987729614004119617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026505316972818672159489 5269878987729614004119617)
              ·
                refine ⟨3952409240797210503089713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5269878987729614004119617 3952409240797210503089713)
                ·
                  refine ⟨2964306930597907877317285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952409240797210503089713 2964306930597907877317285)
                  ·
                    refine ⟨555807549487107726996991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964306930597907877317285 555807549487107726996991)
                    ·
                      rfl

theorem cell23_3247294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_3247294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247294 prefixEnd_3247294 := by exact prefixLift 3247294
  have htrace : WordTrace (prefixWord ++ tailWord_3247294) baseStart_3247294 baseEnd_3247294 := by
    simpa [prefixWord, tailWord_3247294, baseEnd_3247294] using wordTrace_append hprefix tailTrace_3247294
  have hstable : (prefixWord ++ tailWord_3247294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247294).length < 2 ^ (prefixWord ++ tailWord_3247294).sum := by decide
  have hdescent : baseEnd_3247294 < baseStart_3247294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247313 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3247313 : Nat := 118140960795 + 3247313 * 2 ^ 59
def prefixEnd_3247313 : Nat := 4983230072969 + 3 ^ 40 * 3247313 * 2
def baseEnd_3247313 : Nat := 1667432404593758606653385

theorem tailTrace_3247313 : CollatzResearch.WordTrace tailWord_3247313 prefixEnd_3247313 1667432404593758606653385 := by
  unfold tailWord_3247313
  simp only [CollatzResearch.WordTrace]
  refine ⟨118439235284547072751794593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78959490189698048501196395 118439235284547072751794593)
  ·
    refine ⟨88829426463410304563845945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118439235284547072751794593 88829426463410304563845945)
    ·
      refine ⟨66622069847557728422884459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88829426463410304563845945 66622069847557728422884459)
      ·
        refine ⟨99933104771336592634326689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66622069847557728422884459 99933104771336592634326689)
        ·
          refine ⟨74949828578502444475745017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99933104771336592634326689 74949828578502444475745017)
          ·
            refine ⟨56212371433876833356808763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74949828578502444475745017 56212371433876833356808763)
            ·
              refine ⟨84318557150815250035213145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56212371433876833356808763 84318557150815250035213145)
              ·
                refine ⟨63238917863111437526409859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84318557150815250035213145 63238917863111437526409859)
                ·
                  refine ⟨94858376794667156289614789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63238917863111437526409859 94858376794667156289614789)
                  ·
                    refine ⟨17785945649000091804302773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94858376794667156289614789 17785945649000091804302773)
                    ·
                      refine ⟨1667432404593758606653385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17785945649000091804302773 1667432404593758606653385)
                      ·
                        rfl

theorem cell23_3247313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3247313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247313 prefixEnd_3247313 := by exact prefixLift 3247313
  have htrace : WordTrace (prefixWord ++ tailWord_3247313) baseStart_3247313 baseEnd_3247313 := by
    simpa [prefixWord, tailWord_3247313, baseEnd_3247313] using wordTrace_append hprefix tailTrace_3247313
  have hstable : (prefixWord ++ tailWord_3247313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247313).length < 2 ^ (prefixWord ++ tailWord_3247313).sum := by decide
  have hdescent : baseEnd_3247313 < baseStart_3247313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247317 : List Nat := [1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3247317 : Nat := 118140960795 + 3247317 * 2 ^ 59
def prefixEnd_3247317 : Nat := 4983230072969 + 3 ^ 40 * 3247317 * 2
def baseEnd_3247317 : Nat := 1667434458516376591003367

theorem tailTrace_3247317 : CollatzResearch.WordTrace tailWord_3247317 prefixEnd_3247317 1667434458516376591003367 := by
  unfold tailWord_3247317
  simp only [CollatzResearch.WordTrace]
  refine ⟨118439381176532581434940205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78959587451021720956626803 118439381176532581434940205)
  ·
    refine ⟨44414767941199718038102577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118439381176532581434940205 44414767941199718038102577)
    ·
      refine ⟨33311075955899788528576933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44414767941199718038102577 33311075955899788528576933)
      ·
        refine ⟨6245826741731210349108175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33311075955899788528576933 6245826741731210349108175)
        ·
          refine ⟨9368740112596815523662263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245826741731210349108175 9368740112596815523662263)
          ·
            refine ⟨14053110168895223285493395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368740112596815523662263 14053110168895223285493395)
            ·
              refine ⟨21079665253342834928240093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14053110168895223285493395 21079665253342834928240093)
              ·
                refine ⟨7904874470003563098090035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21079665253342834928240093 7904874470003563098090035)
                ·
                  refine ⟨11857311705005344647135053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904874470003563098090035 11857311705005344647135053)
                  ·
                    refine ⟨4446491889377004242675645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11857311705005344647135053 4446491889377004242675645)
                    ·
                      refine ⟨1667434458516376591003367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4446491889377004242675645 1667434458516376591003367)
                      ·
                        rfl

theorem cell23_3247317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3247317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247317 prefixEnd_3247317 := by exact prefixLift 3247317
  have htrace : WordTrace (prefixWord ++ tailWord_3247317) baseStart_3247317 baseEnd_3247317 := by
    simpa [prefixWord, tailWord_3247317, baseEnd_3247317] using wordTrace_append hprefix tailTrace_3247317
  have hstable : (prefixWord ++ tailWord_3247317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247317).length < 2 ^ (prefixWord ++ tailWord_3247317).sum := by decide
  have hdescent : baseEnd_3247317 < baseStart_3247317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247318 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 3, 2, 2]
def baseStart_3247318 : Nat := 118140960795 + 3247318 * 2 ^ 59
def prefixEnd_3247318 : Nat := 4983230072969 + 3 ^ 40 * 3247318 * 2
def baseEnd_3247318 : Nat := 1667434971997031087090863

theorem tailTrace_3247318 : CollatzResearch.WordTrace tailWord_3247318 prefixEnd_3247318 1667434971997031087090863 := by
  unfold tailWord_3247318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402463603095559912857913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78959611766352639070484405 7402463603095559912857913)
  ·
    refine ⟨5551847702321669934643435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7402463603095559912857913 5551847702321669934643435)
    ·
      refine ⟨8327771553482504901965153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551847702321669934643435 8327771553482504901965153)
      ·
        refine ⟨6245828665111878676473865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8327771553482504901965153 6245828665111878676473865)
        ·
          refine ⟨4684371498833909007355399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6245828665111878676473865 4684371498833909007355399)
          ·
            refine ⟨7026557248250863511033099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684371498833909007355399 7026557248250863511033099)
            ·
              refine ⟨10539835872376295266549649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026557248250863511033099 10539835872376295266549649)
              ·
                refine ⟨7904876904282221449912237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10539835872376295266549649 7904876904282221449912237)
                ·
                  refine ⟨2964328839105833043717089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7904876904282221449912237 2964328839105833043717089)
                  ·
                    refine ⟨2223246629329374782787817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964328839105833043717089 2223246629329374782787817)
                    ·
                      refine ⟨1667434971997031087090863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223246629329374782787817 1667434971997031087090863)
                      ·
                        rfl

theorem cell23_3247318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_3247318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247318 prefixEnd_3247318 := by exact prefixLift 3247318
  have htrace : WordTrace (prefixWord ++ tailWord_3247318) baseStart_3247318 baseEnd_3247318 := by
    simpa [prefixWord, tailWord_3247318, baseEnd_3247318] using wordTrace_append hprefix tailTrace_3247318
  have hstable : (prefixWord ++ tailWord_3247318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247318).length < 2 ^ (prefixWord ++ tailWord_3247318).sum := by decide
  have hdescent : baseEnd_3247318 < baseStart_3247318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247323 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4]
def baseStart_3247323 : Nat := 118140960795 + 3247323 * 2 ^ 59
def prefixEnd_3247323 : Nat := 4983230072969 + 3 ^ 40 * 3247323 * 2
def baseEnd_3247323 : Nat := 1667437539400303567528339

theorem tailTrace_3247323 : CollatzResearch.WordTrace tailWord_3247323 prefixEnd_3247323 1667437539400303567528339 := by
  unfold tailWord_3247323
  simp only [CollatzResearch.WordTrace]
  refine ⟨118439600014510844459658623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78959733343007229639772415 118439600014510844459658623)
  ·
    refine ⟨177659400021766266689487935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118439600014510844459658623 177659400021766266689487935)
    ·
      refine ⟨266489100032649400034231903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177659400021766266689487935 266489100032649400034231903)
      ·
        refine ⟨399733650048974100051347855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266489100032649400034231903 399733650048974100051347855)
        ·
          refine ⟨599600475073461150077021783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399733650048974100051347855 599600475073461150077021783)
          ·
            refine ⟨899400712610191725115532675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599600475073461150077021783 899400712610191725115532675)
            ·
              refine ⟨1349101068915287587673299013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899400712610191725115532675 1349101068915287587673299013)
              ·
                refine ⟨252956450421616422688743565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1349101068915287587673299013 252956450421616422688743565)
                ·
                  refine ⟨94858668908106158508278837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 252956450421616422688743565 94858668908106158508278837)
                  ·
                    refine ⟨8893000210134952360151141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94858668908106158508278837 8893000210134952360151141)
                    ·
                      refine ⟨1667437539400303567528339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8893000210134952360151141 1667437539400303567528339)
                      ·
                        rfl

theorem cell23_3247323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 5, 4].length) (baseStart_3247323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247323 prefixEnd_3247323 := by exact prefixLift 3247323
  have htrace : WordTrace (prefixWord ++ tailWord_3247323) baseStart_3247323 baseEnd_3247323 := by
    simpa [prefixWord, tailWord_3247323, baseEnd_3247323] using wordTrace_append hprefix tailTrace_3247323
  have hstable : (prefixWord ++ tailWord_3247323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247323).length < 2 ^ (prefixWord ++ tailWord_3247323).sum := by decide
  have hdescent : baseEnd_3247323 < baseStart_3247323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247327 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 3, 3, 2]
def baseStart_3247327 : Nat := 118140960795 + 3247327 * 2 ^ 59
def prefixEnd_3247327 : Nat := 4983230072969 + 3 ^ 40 * 3247327 * 2
def baseEnd_3247327 : Nat := 1667439593322921551878321

theorem tailTrace_3247327 : CollatzResearch.WordTrace tailWord_3247327 prefixEnd_3247327 1667439593322921551878321 := by
  unfold tailWord_3247327
  simp only [CollatzResearch.WordTrace]
  refine ⟨118439745906496353142804235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78959830604330902095202823 118439745906496353142804235)
  ·
    refine ⟨177659618859744529714206353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118439745906496353142804235 177659618859744529714206353)
    ·
      refine ⟨133244714144808397285654765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177659618859744529714206353 133244714144808397285654765)
      ·
        refine ⟨49966767804303148982120537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133244714144808397285654765 49966767804303148982120537)
        ·
          refine ⟨37475075853227361736590403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49966767804303148982120537 37475075853227361736590403)
          ·
            refine ⟨56212613779841042604885605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37475075853227361736590403 56212613779841042604885605)
            ·
              refine ⟨10539865083720195488416051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56212613779841042604885605 10539865083720195488416051)
              ·
                refine ⟨15809797625580293232624077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10539865083720195488416051 15809797625580293232624077)
                ·
                  refine ⟨5928674109592609962234029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15809797625580293232624077 5928674109592609962234029)
                  ·
                    refine ⟨2223252791097228735837761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5928674109592609962234029 2223252791097228735837761)
                    ·
                      refine ⟨1667439593322921551878321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223252791097228735837761 1667439593322921551878321)
                      ·
                        rfl

theorem cell23_3247327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_3247327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247327 prefixEnd_3247327 := by exact prefixLift 3247327
  have htrace : WordTrace (prefixWord ++ tailWord_3247327) baseStart_3247327 baseEnd_3247327 := by
    simpa [prefixWord, tailWord_3247327, baseEnd_3247327] using wordTrace_append hprefix tailTrace_3247327
  have hstable : (prefixWord ++ tailWord_3247327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247327).length < 2 ^ (prefixWord ++ tailWord_3247327).sum := by decide
  have hdescent : baseEnd_3247327 < baseStart_3247327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247374 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3247374 : Nat := 118140960795 + 3247374 * 2 ^ 59
def prefixEnd_3247374 : Nat := 4983230072969 + 3 ^ 40 * 3247374 * 2
def baseEnd_3247374 : Nat := 1667463726913682867990605

theorem tailTrace_3247374 : CollatzResearch.WordTrace tailWord_3247374 prefixEnd_3247374 1667463726913682867990605 := by
  unfold tailWord_3247374
  simp only [CollatzResearch.WordTrace]
  refine ⟨14805182517165760021220647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78960973424884053446510117 14805182517165760021220647)
  ·
    refine ⟨22207773775748640031830971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14805182517165760021220647 22207773775748640031830971)
    ·
      refine ⟨33311660663622960047746457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22207773775748640031830971 33311660663622960047746457)
      ·
        refine ⟨24983745497717220035809843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33311660663622960047746457 24983745497717220035809843)
        ·
          refine ⟨37475618246575830053714765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24983745497717220035809843 37475618246575830053714765)
          ·
            refine ⟨14053356842465936270143037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37475618246575830053714765 14053356842465936270143037)
            ·
              refine ⟨5270008815924726101303639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14053356842465936270143037 5270008815924726101303639)
              ·
                refine ⟨7905013223887089151955459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270008815924726101303639 7905013223887089151955459)
                ·
                  refine ⟨11857519835830633727933189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7905013223887089151955459 11857519835830633727933189)
                  ·
                    refine ⟨2223284969218243823987473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11857519835830633727933189 2223284969218243823987473)
                    ·
                      refine ⟨1667463726913682867990605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223284969218243823987473 1667463726913682867990605)
                      ·
                        rfl

theorem cell23_3247374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3247374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247374 prefixEnd_3247374 := by exact prefixLift 3247374
  have htrace : WordTrace (prefixWord ++ tailWord_3247374) baseStart_3247374 baseEnd_3247374 := by
    simpa [prefixWord, tailWord_3247374, baseEnd_3247374] using wordTrace_append hprefix tailTrace_3247374
  have hstable : (prefixWord ++ tailWord_3247374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247374).length < 2 ^ (prefixWord ++ tailWord_3247374).sum := by decide
  have hdescent : baseEnd_3247374 < baseStart_3247374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247420 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3247420 : Nat := 118140960795 + 3247420 * 2 ^ 59
def prefixEnd_3247420 : Nat := 4983230072969 + 3 ^ 40 * 3247420 * 2
def baseEnd_3247420 : Nat := 1667487347023789688015393

theorem tailTrace_3247420 : CollatzResearch.WordTrace tailWord_3247420 prefixEnd_3247420 1667487347023789688015393 := by
  unfold tailWord_3247420
  simp only [CollatzResearch.WordTrace]
  refine ⟨59221568947579715012969857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78962091930106286683959809 59221568947579715012969857)
  ·
    refine ⟨44416176710684786259727393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59221568947579715012969857 44416176710684786259727393)
    ·
      refine ⟨33312132533013589694795545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44416176710684786259727393 33312132533013589694795545)
      ·
        refine ⟨24984099399760192271096659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33312132533013589694795545 24984099399760192271096659)
        ·
          refine ⟨37476149099640288406644989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24984099399760192271096659 37476149099640288406644989)
          ·
            refine ⟨14053555912365108152491871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37476149099640288406644989 14053555912365108152491871)
            ·
              refine ⟨21080333868547662228737807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14053555912365108152491871 21080333868547662228737807)
              ·
                refine ⟨31620500802821493343106711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21080333868547662228737807 31620500802821493343106711)
                ·
                  refine ⟨47430751204232240014660067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31620500802821493343106711 47430751204232240014660067)
                  ·
                    refine ⟨71146126806348360021990101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47430751204232240014660067 71146126806348360021990101)
                    ·
                      refine ⟨1667487347023789688015393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71146126806348360021990101 1667487347023789688015393)
                      ·
                        rfl

theorem cell23_3247420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3247420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247420 prefixEnd_3247420 := by exact prefixLift 3247420
  have htrace : WordTrace (prefixWord ++ tailWord_3247420) baseStart_3247420 baseEnd_3247420 := by
    simpa [prefixWord, tailWord_3247420, baseEnd_3247420] using wordTrace_append hprefix tailTrace_3247420
  have hstable : (prefixWord ++ tailWord_3247420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247420).length < 2 ^ (prefixWord ++ tailWord_3247420).sum := by decide
  have hdescent : baseEnd_3247420 < baseStart_3247420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247425 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3247425 : Nat := 118140960795 + 3247425 * 2 ^ 59
def prefixEnd_3247425 : Nat := 4983230072969 + 3 ^ 40 * 3247425 * 2
def baseEnd_3247425 : Nat := 1667489914427062168452871

theorem tailTrace_3247425 : CollatzResearch.WordTrace tailWord_3247425 prefixEnd_3247425 1667489914427062168452871 := by
  unfold tailWord_3247425
  simp only [CollatzResearch.WordTrace]
  refine ⟨118443320260141315879871729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78962213506760877253247819 118443320260141315879871729)
  ·
    refine ⟨88832490195105986909903797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118443320260141315879871729 88832490195105986909903797)
    ·
      refine ⟨8328045955791186272803481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88832490195105986909903797 8328045955791186272803481)
      ·
        refine ⟨6246034466843389704602611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8328045955791186272803481 6246034466843389704602611)
        ·
          refine ⟨9369051700265084556903917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6246034466843389704602611 9369051700265084556903917)
          ·
            refine ⟨3513394387599406708838969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9369051700265084556903917 3513394387599406708838969)
            ·
              refine ⟨2635045790699555031629227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513394387599406708838969 2635045790699555031629227)
              ·
                refine ⟨3952568686049332547443841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635045790699555031629227 3952568686049332547443841)
                ·
                  refine ⟨2964426514536999410582881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3952568686049332547443841 2964426514536999410582881)
                  ·
                    refine ⟨2223319885902749557937161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964426514536999410582881 2223319885902749557937161)
                    ·
                      refine ⟨1667489914427062168452871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223319885902749557937161 1667489914427062168452871)
                      ·
                        rfl

theorem cell23_3247425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3247425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247425 prefixEnd_3247425 := by exact prefixLift 3247425
  have htrace : WordTrace (prefixWord ++ tailWord_3247425) baseStart_3247425 baseEnd_3247425 := by
    simpa [prefixWord, tailWord_3247425, baseEnd_3247425] using wordTrace_append hprefix tailTrace_3247425
  have hstable : (prefixWord ++ tailWord_3247425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247425).length < 2 ^ (prefixWord ++ tailWord_3247425).sum := by decide
  have hdescent : baseEnd_3247425 < baseStart_3247425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247447 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3247447 : Nat := 118140960795 + 3247447 * 2 ^ 59
def prefixEnd_3247447 : Nat := 4983230072969 + 3 ^ 40 * 3247447 * 2
def baseEnd_3247447 : Nat := 1667501211001461082377769

theorem tailTrace_3247447 : CollatzResearch.WordTrace tailWord_3247447 prefixEnd_3247447 1667501211001461082377769 := by
  unfold tailWord_3247447
  simp only [CollatzResearch.WordTrace]
  refine ⟨118444122666061613637172595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78962748444041075758115063 118444122666061613637172595)
  ·
    refine ⟨177666183999092420455758893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118444122666061613637172595 177666183999092420455758893)
    ·
      refine ⟨66624818999659657670909585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177666183999092420455758893 66624818999659657670909585)
      ·
        refine ⟨49968614249744743253182189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66624818999659657670909585 49968614249744743253182189)
        ·
          refine ⟨18738230343654278719943321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49968614249744743253182189 18738230343654278719943321)
          ·
            refine ⟨14053672757740709039957491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18738230343654278719943321 14053672757740709039957491)
            ·
              refine ⟨21080509136611063559936237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14053672757740709039957491 21080509136611063559936237)
              ·
                refine ⟨7905190926229148834976089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21080509136611063559936237 7905190926229148834976089)
                ·
                  refine ⟨5928893194671861626232067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7905190926229148834976089 5928893194671861626232067)
                  ·
                    refine ⟨8893339792007792439348101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928893194671861626232067 8893339792007792439348101)
                    ·
                      refine ⟨1667501211001461082377769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8893339792007792439348101 1667501211001461082377769)
                      ·
                        rfl

theorem cell23_3247447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3247447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247447 prefixEnd_3247447 := by exact prefixLift 3247447
  have htrace : WordTrace (prefixWord ++ tailWord_3247447) baseStart_3247447 baseEnd_3247447 := by
    simpa [prefixWord, tailWord_3247447, baseEnd_3247447] using wordTrace_append hprefix tailTrace_3247447
  have hstable : (prefixWord ++ tailWord_3247447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247447).length < 2 ^ (prefixWord ++ tailWord_3247447).sum := by decide
  have hdescent : baseEnd_3247447 < baseStart_3247447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247508 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_3247508 : Nat := 118140960795 + 3247508 * 2 ^ 59
def prefixEnd_3247508 : Nat := 4983230072969 + 3 ^ 40 * 3247508 * 2
def baseEnd_3247508 : Nat := 555844177773795114571663

theorem tailTrace_3247508 : CollatzResearch.WordTrace tailWord_3247508 prefixEnd_3247508 555844177773795114571663 := by
  unfold tailWord_3247508
  simp only [CollatzResearch.WordTrace]
  refine ⟨59223173759420310527571589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78964231679227080703428785 59223173759420310527571589)
  ·
    refine ⟨11104345079891308223919673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59223173759420310527571589 11104345079891308223919673)
    ·
      refine ⟨8328258809918481167939755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11104345079891308223919673 8328258809918481167939755)
      ·
        refine ⟨12492388214877721751909633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8328258809918481167939755 12492388214877721751909633)
        ·
          refine ⟨9369291161158291313932225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12492388214877721751909633 9369291161158291313932225)
          ·
            refine ⟨7026968370868718485449169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9369291161158291313932225 7026968370868718485449169)
            ·
              refine ⟨5270226278151538864086877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026968370868718485449169 5270226278151538864086877)
              ·
                refine ⟨1976334854306827074032579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5270226278151538864086877 1976334854306827074032579)
                ·
                  refine ⟨2964502281460240611048869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976334854306827074032579 2964502281460240611048869)
                  ·
                    refine ⟨555844177773795114571663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964502281460240611048869 555844177773795114571663)
                    ·
                      rfl

theorem cell23_3247508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_3247508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247508 prefixEnd_3247508 := by exact prefixLift 3247508
  have htrace : WordTrace (prefixWord ++ tailWord_3247508) baseStart_3247508 baseEnd_3247508 := by
    simpa [prefixWord, tailWord_3247508, baseEnd_3247508] using wordTrace_append hprefix tailTrace_3247508
  have hstable : (prefixWord ++ tailWord_3247508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247508).length < 2 ^ (prefixWord ++ tailWord_3247508).sum := by decide
  have hdescent : baseEnd_3247508 < baseStart_3247508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247514 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3247514 : Nat := 118140960795 + 3247514 * 2 ^ 59
def prefixEnd_3247514 : Nat := 4983230072969 + 3 ^ 40 * 3247514 * 2
def baseEnd_3247514 : Nat := 1667535614205312320239961

theorem tailTrace_3247514 : CollatzResearch.WordTrace tailWord_3247514 prefixEnd_3247514 1667535614205312320239961 := by
  unfold tailWord_3247514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29611641589204721019965399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78964377571212589386574397 29611641589204721019965399)
  ·
    refine ⟨44417462383807081529948099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29611641589204721019965399 44417462383807081529948099)
    ·
      refine ⟨66626193575710622294922149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44417462383807081529948099 66626193575710622294922149)
      ·
        refine ⟨12492411295445741680297903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66626193575710622294922149 12492411295445741680297903)
        ·
          refine ⟨18738616943168612520446855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12492411295445741680297903 18738616943168612520446855)
          ·
            refine ⟨28107925414752918780670283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18738616943168612520446855 28107925414752918780670283)
            ·
              refine ⟨42161888122129378171005425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28107925414752918780670283 42161888122129378171005425)
              ·
                refine ⟨31621416091597033628254069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42161888122129378171005425 31621416091597033628254069)
                ·
                  refine ⟨2964507758587221902648819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31621416091597033628254069 2964507758587221902648819)
                  ·
                    refine ⟨4446761637880832853973229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2964507758587221902648819 4446761637880832853973229)
                    ·
                      refine ⟨1667535614205312320239961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4446761637880832853973229 1667535614205312320239961)
                      ·
                        rfl

theorem cell23_3247514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3247514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247514 prefixEnd_3247514 := by exact prefixLift 3247514
  have htrace : WordTrace (prefixWord ++ tailWord_3247514) baseStart_3247514 baseEnd_3247514 := by
    simpa [prefixWord, tailWord_3247514, baseEnd_3247514] using wordTrace_append hprefix tailTrace_3247514
  have hstable : (prefixWord ++ tailWord_3247514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247514).length < 2 ^ (prefixWord ++ tailWord_3247514).sum := by decide
  have hdescent : baseEnd_3247514 < baseStart_3247514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247524 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_3247524 : Nat := 118140960795 + 3247524 * 2 ^ 59
def prefixEnd_3247524 : Nat := 4983230072969 + 3 ^ 40 * 3247524 * 2
def baseEnd_3247524 : Nat := 1667540749011857281114915

theorem tailTrace_3247524 : CollatzResearch.WordTrace tailWord_3247524 prefixEnd_3247524 1667540749011857281114915 := by
  unfold tailWord_3247524
  simp only [CollatzResearch.WordTrace]
  refine ⟨59223465543391327893862813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78964620724521770525150417 59223465543391327893862813)
  ·
    refine ⟨22208799578771747960198555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59223465543391327893862813 22208799578771747960198555)
    ·
      refine ⟨33313199368157621940297833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22208799578771747960198555 33313199368157621940297833)
      ·
        refine ⟨24984899526118216455223375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33313199368157621940297833 24984899526118216455223375)
        ·
          refine ⟨37477349289177324682835063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24984899526118216455223375 37477349289177324682835063)
          ·
            refine ⟨56216023933765987024252595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37477349289177324682835063 56216023933765987024252595)
            ·
              refine ⟨84324035900648980536378893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56216023933765987024252595 84324035900648980536378893)
              ·
                refine ⟨31621513462743367701142085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84324035900648980536378893 31621513462743367701142085)
                ·
                  refine ⟨5929033774264381443964141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31621513462743367701142085 5929033774264381443964141)
                  ·
                    refine ⟨2223387665349143041486553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5929033774264381443964141 2223387665349143041486553)
                    ·
                      refine ⟨1667540749011857281114915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223387665349143041486553 1667540749011857281114915)
                      ·
                        rfl

theorem cell23_3247524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_3247524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247524 prefixEnd_3247524 := by exact prefixLift 3247524
  have htrace : WordTrace (prefixWord ++ tailWord_3247524) baseStart_3247524 baseEnd_3247524 := by
    simpa [prefixWord, tailWord_3247524, baseEnd_3247524] using wordTrace_append hprefix tailTrace_3247524
  have hstable : (prefixWord ++ tailWord_3247524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247524).length < 2 ^ (prefixWord ++ tailWord_3247524).sum := by decide
  have hdescent : baseEnd_3247524 < baseStart_3247524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247564 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 4, 4]
def baseStart_3247564 : Nat := 118140960795 + 3247564 * 2 ^ 59
def prefixEnd_3247564 : Nat := 4983230072969 + 3 ^ 40 * 3247564 * 2
def baseEnd_3247564 : Nat := 555853762746012374871577

theorem tailTrace_3247564 : CollatzResearch.WordTrace tailWord_3247564 prefixEnd_3247564 555853762746012374871577 := by
  unfold tailWord_3247564
  simp only [CollatzResearch.WordTrace]
  refine ⟨59224195003318871309590873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78965593337758495079454497 59224195003318871309590873)
  ·
    refine ⟨44418146252489153482193155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59224195003318871309590873 44418146252489153482193155)
    ·
      refine ⟨66627219378733730223289733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44418146252489153482193155 66627219378733730223289733)
      ·
        refine ⟨12492603633512574416866825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66627219378733730223289733 12492603633512574416866825)
        ·
          refine ⟨9369452725134430812650119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12492603633512574416866825 9369452725134430812650119)
          ·
            refine ⟨14054179087701646218975179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369452725134430812650119 14054179087701646218975179)
            ·
              refine ⟨21081268631552469328462769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054179087701646218975179 21081268631552469328462769)
              ·
                refine ⟨15810951473664351996347077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21081268631552469328462769 15810951473664351996347077)
                ·
                  refine ⟨2964553401312065999315077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15810951473664351996347077 2964553401312065999315077)
                  ·
                    refine ⟨555853762746012374871577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2964553401312065999315077 555853762746012374871577)
                    ·
                      rfl

theorem cell23_3247564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 4].length) (baseStart_3247564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247564 prefixEnd_3247564 := by exact prefixLift 3247564
  have htrace : WordTrace (prefixWord ++ tailWord_3247564) baseStart_3247564 baseEnd_3247564 := by
    simpa [prefixWord, tailWord_3247564, baseEnd_3247564] using wordTrace_append hprefix tailTrace_3247564
  have hstable : (prefixWord ++ tailWord_3247564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247564).length < 2 ^ (prefixWord ++ tailWord_3247564).sum := by decide
  have hdescent : baseEnd_3247564 < baseStart_3247564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247567 : List Nat := [1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4]
def baseStart_3247567 : Nat := 118140960795 + 3247567 * 2 ^ 59
def prefixEnd_3247567 : Nat := 4983230072969 + 3 ^ 40 * 3247567 * 2
def baseEnd_3247567 : Nat := 1667562828680000612877217

theorem tailTrace_3247567 : CollatzResearch.WordTrace tailWord_3247567 prefixEnd_3247567 1667562828680000612877217 := by
  unfold tailWord_3247567
  simp only [CollatzResearch.WordTrace]
  refine ⟨118448499425626874131540955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78965666283751249421027303 118448499425626874131540955)
  ·
    refine ⟨177672749138440311197311433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118448499425626874131540955 177672749138440311197311433)
    ·
      refine ⟨133254561853830233397983575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177672749138440311197311433 133254561853830233397983575)
      ·
        refine ⟨199881842780745350096975363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133254561853830233397983575 199881842780745350096975363)
        ·
          refine ⟨299822764171118025145463045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199881842780745350096975363 299822764171118025145463045)
          ·
            refine ⟨56216768282084629714774321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299822764171118025145463045 56216768282084629714774321)
            ·
              refine ⟨42162576211563472286080741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56216768282084629714774321 42162576211563472286080741)
              ·
                refine ⟨7905483039668151053640139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42162576211563472286080741 7905483039668151053640139)
                ·
                  refine ⟨11858224559502226580460209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7905483039668151053640139 11858224559502226580460209)
                  ·
                    refine ⟨8893668419626669935345157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11858224559502226580460209 8893668419626669935345157)
                    ·
                      refine ⟨1667562828680000612877217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8893668419626669935345157 1667562828680000612877217)
                      ·
                        rfl

theorem cell23_3247567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_3247567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247567 prefixEnd_3247567 := by exact prefixLift 3247567
  have htrace : WordTrace (prefixWord ++ tailWord_3247567) baseStart_3247567 baseEnd_3247567 := by
    simpa [prefixWord, tailWord_3247567, baseEnd_3247567] using wordTrace_append hprefix tailTrace_3247567
  have hstable : (prefixWord ++ tailWord_3247567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247567).length < 2 ^ (prefixWord ++ tailWord_3247567).sum := by decide
  have hdescent : baseEnd_3247567 < baseStart_3247567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247577 : List Nat := [1, 2, 1, 2, 4, 4, 9]
def baseStart_3247577 : Nat := 118140960795 + 3247577 * 2 ^ 59
def prefixEnd_3247577 : Nat := 4983230072969 + 3 ^ 40 * 3247577 * 2
def baseEnd_3247577 : Nat := 20587258808475871280891

theorem tailTrace_3247577 : CollatzResearch.WordTrace tailWord_3247577 prefixEnd_3247577 20587258808475871280891 := by
  unfold tailWord_3247577
  simp only [CollatzResearch.WordTrace]
  refine ⟨118448864155590645839404985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78965909437060430559603323 118448864155590645839404985)
  ·
    refine ⟨88836648116692984379553739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118448864155590645839404985 88836648116692984379553739)
    ·
      refine ⟨133254972175039476569330609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88836648116692984379553739 133254972175039476569330609)
      ·
        refine ⟨99941229131279607426997957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133254972175039476569330609 99941229131279607426997957)
        ·
          refine ⟨18738980462114926392562117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99941229131279607426997957 18738980462114926392562117)
          ·
            refine ⟨3513558836646548698605397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18738980462114926392562117 3513558836646548698605397)
            ·
              refine ⟨20587258808475871280891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3513558836646548698605397 20587258808475871280891)
              ·
                rfl

theorem cell23_3247577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 9].length) (baseStart_3247577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247577 prefixEnd_3247577 := by exact prefixLift 3247577
  have htrace : WordTrace (prefixWord ++ tailWord_3247577) baseStart_3247577 baseEnd_3247577 := by
    simpa [prefixWord, tailWord_3247577, baseEnd_3247577] using wordTrace_append hprefix tailTrace_3247577
  have hstable : (prefixWord ++ tailWord_3247577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247577).length < 2 ^ (prefixWord ++ tailWord_3247577).sum := by decide
  have hdescent : baseEnd_3247577 < baseStart_3247577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247588 : List Nat := [2, 3, 1, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_3247588 : Nat := 118140960795 + 3247588 * 2 ^ 59
def prefixEnd_3247588 : Nat := 4983230072969 + 3 ^ 40 * 3247588 * 2
def baseEnd_3247588 : Nat := 1667573611773745030714621

theorem tailTrace_3247588 : CollatzResearch.WordTrace tailWord_3247588 prefixEnd_3247588 1667573611773745030714621 := by
  unfold tailWord_3247588
  simp only [CollatzResearch.WordTrace]
  refine ⟨59224632679275397359027709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78966176905700529812036945 59224632679275397359027709)
  ·
    refine ⟨22209237254728274009635391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59224632679275397359027709 22209237254728274009635391)
    ·
      refine ⟨33313855882092411014453087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22209237254728274009635391 33313855882092411014453087)
      ·
        refine ⟨49970783823138616521679631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33313855882092411014453087 49970783823138616521679631)
        ·
          refine ⟨74956175734707924782519447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49970783823138616521679631 74956175734707924782519447)
          ·
            refine ⟨112434263602061887173779171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74956175734707924782519447 112434263602061887173779171)
            ·
              refine ⟨168651395403092830760668757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112434263602061887173779171 168651395403092830760668757)
              ·
                refine ⟨1976383539879994110476587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168651395403092830760668757 1976383539879994110476587)
                ·
                  refine ⟨2964575309819991165714881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976383539879994110476587 2964575309819991165714881)
                  ·
                    refine ⟨2223431482364993374286161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964575309819991165714881 2223431482364993374286161)
                    ·
                      refine ⟨1667573611773745030714621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223431482364993374286161 1667573611773745030714621)
                      ·
                        rfl

theorem cell23_3247588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_3247588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247588 prefixEnd_3247588 := by exact prefixLift 3247588
  have htrace : WordTrace (prefixWord ++ tailWord_3247588) baseStart_3247588 baseEnd_3247588 := by
    simpa [prefixWord, tailWord_3247588, baseEnd_3247588] using wordTrace_append hprefix tailTrace_3247588
  have hstable : (prefixWord ++ tailWord_3247588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247588).length < 2 ^ (prefixWord ++ tailWord_3247588).sum := by decide
  have hdescent : baseEnd_3247588 < baseStart_3247588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247594 : List Nat := [3, 1, 3, 1, 4, 1, 2, 8]
def baseStart_3247594 : Nat := 118140960795 + 3247594 * 2 ^ 59
def prefixEnd_3247594 : Nat := 4983230072969 + 3 ^ 40 * 3247594 * 2
def baseEnd_3247594 : Nat := 61762099728061926194059

theorem tailTrace_3247594 : CollatzResearch.WordTrace tailWord_3247594 prefixEnd_3247594 61762099728061926194059 := by
  unfold tailWord_3247594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29612371049132264435693459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78966322797686038495182557 29612371049132264435693459)
  ·
    refine ⟨44418556573698396653540189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29612371049132264435693459 44418556573698396653540189)
    ·
      refine ⟨16656958715136898745077571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44418556573698396653540189 16656958715136898745077571)
      ·
        refine ⟨24985438072705348117616357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16656958715136898745077571 24985438072705348117616357)
        ·
          refine ⟨4684769638632252772053067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24985438072705348117616357 4684769638632252772053067)
          ·
            refine ⟨7027154457948379158079601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4684769638632252772053067 7027154457948379158079601)
            ·
              refine ⟨5270365843461284368559701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027154457948379158079601 5270365843461284368559701)
              ·
                refine ⟨61762099728061926194059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5270365843461284368559701 61762099728061926194059)
                ·
                  rfl

theorem cell23_3247594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_3247594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247594 prefixEnd_3247594 := by exact prefixLift 3247594
  have htrace : WordTrace (prefixWord ++ tailWord_3247594) baseStart_3247594 baseEnd_3247594 := by
    simpa [prefixWord, tailWord_3247594, baseEnd_3247594] using wordTrace_append hprefix tailTrace_3247594
  have hstable : (prefixWord ++ tailWord_3247594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247594).length < 2 ^ (prefixWord ++ tailWord_3247594).sum := by decide
  have hdescent : baseEnd_3247594 < baseStart_3247594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247647 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3247647 : Nat := 118140960795 + 3247647 * 2 ^ 59
def prefixEnd_3247647 : Nat := 4983230072969 + 3 ^ 40 * 3247647 * 2
def baseEnd_3247647 : Nat := 1667603907132360299876849

theorem tailTrace_3247647 : CollatzResearch.WordTrace tailWord_3247647 prefixEnd_3247647 1667603907132360299876849 := by
  unfold tailWord_3247647
  simp only [CollatzResearch.WordTrace]
  refine ⟨118451417265337047794453195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78967611510224698529635463 118451417265337047794453195)
  ·
    refine ⟨177677125898005571691679793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118451417265337047794453195 177677125898005571691679793)
    ·
      refine ⟨133257844423504178768759845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177677125898005571691679793 133257844423504178768759845)
      ·
        refine ⟨24985845829407033519142471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133257844423504178768759845 24985845829407033519142471)
        ·
          refine ⟨37478768744110550278713707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24985845829407033519142471 37478768744110550278713707)
          ·
            refine ⟨56218153116165825418070561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37478768744110550278713707 56218153116165825418070561)
            ·
              refine ⟨42163614837124369063552921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56218153116165825418070561 42163614837124369063552921)
              ·
                refine ⟨31622711127843276797664691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42163614837124369063552921 31622711127843276797664691)
                ·
                  refine ⟨47434066691764915196497037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31622711127843276797664691 47434066691764915196497037)
                  ·
                    refine ⟨17787775009411843198686389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47434066691764915196497037 17787775009411843198686389)
                    ·
                      refine ⟨1667603907132360299876849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17787775009411843198686389 1667603907132360299876849)
                      ·
                        rfl

theorem cell23_3247647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3247647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247647 prefixEnd_3247647 := by exact prefixLift 3247647
  have htrace : WordTrace (prefixWord ++ tailWord_3247647) baseStart_3247647 baseEnd_3247647 := by
    simpa [prefixWord, tailWord_3247647, baseEnd_3247647] using wordTrace_append hprefix tailTrace_3247647
  have hstable : (prefixWord ++ tailWord_3247647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247647).length < 2 ^ (prefixWord ++ tailWord_3247647).sum := by decide
  have hdescent : baseEnd_3247647 < baseStart_3247647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247667 : List Nat := [1, 1, 1, 2, 4, 3, 1, 1, 9]
def baseStart_3247667 : Nat := 118140960795 + 3247667 * 2 ^ 59
def prefixEnd_3247667 : Nat := 4983230072969 + 3 ^ 40 * 3247667 * 2
def baseEnd_3247667 : Nat := 185290464082827802402973

theorem tailTrace_3247667 : CollatzResearch.WordTrace tailWord_3247667 prefixEnd_3247667 185290464082827802402973 := by
  unfold tailWord_3247667
  simp only [CollatzResearch.WordTrace]
  refine ⟨118452146725264591210181255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78968097816843060806787503 118452146725264591210181255)
  ·
    refine ⟨177678220087896886815271883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118452146725264591210181255 177678220087896886815271883)
    ·
      refine ⟨266517330131845330222907825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177678220087896886815271883 266517330131845330222907825)
      ·
        refine ⟨199887997598883997667180869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266517330131845330222907825 199887997598883997667180869)
        ·
          refine ⟨37478999549790749562596413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199887997598883997667180869 37478999549790749562596413)
          ·
            refine ⟨14054624831171531085973655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37478999549790749562596413 14054624831171531085973655)
            ·
              refine ⟨21081937246757296628960483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054624831171531085973655 21081937246757296628960483)
              ·
                refine ⟨31622905870135944943440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21081937246757296628960483 31622905870135944943440725)
                ·
                  refine ⟨185290464082827802402973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31622905870135944943440725 185290464082827802402973)
                  ·
                    rfl

theorem cell23_3247667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 9].length) (baseStart_3247667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247667 prefixEnd_3247667 := by exact prefixLift 3247667
  have htrace : WordTrace (prefixWord ++ tailWord_3247667) baseStart_3247667 baseEnd_3247667 := by
    simpa [prefixWord, tailWord_3247667, baseEnd_3247667] using wordTrace_append hprefix tailTrace_3247667
  have hstable : (prefixWord ++ tailWord_3247667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247667).length < 2 ^ (prefixWord ++ tailWord_3247667).sum := by decide
  have hdescent : baseEnd_3247667 < baseStart_3247667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247727 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 10]
def baseStart_3247727 : Nat := 118140960795 + 3247727 * 2 ^ 59
def prefixEnd_3247727 : Nat := 4983230072969 + 3 ^ 40 * 3247727 * 2
def baseEnd_3247727 : Nat := 555881661861573328958827

theorem tailTrace_3247727 : CollatzResearch.WordTrace tailWord_3247727 prefixEnd_3247727 555881661861573328958827 := by
  unfold tailWord_3247727
  simp only [CollatzResearch.WordTrace]
  refine ⟨118454335105047221457365435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78969556736698147638243623 118454335105047221457365435)
  ·
    refine ⟨177681502657570832186048153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118454335105047221457365435 177681502657570832186048153)
    ·
      refine ⟨133261126993178124139536115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177681502657570832186048153 133261126993178124139536115)
      ·
        refine ⟨199891690489767186209304173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133261126993178124139536115 199891690489767186209304173)
        ·
          refine ⟨74959383933662694828489065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199891690489767186209304173 74959383933662694828489065)
          ·
            refine ⟨56219537950247021121366799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74959383933662694828489065 56219537950247021121366799)
            ·
              refine ⟨84329306925370531682050199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56219537950247021121366799 84329306925370531682050199)
              ·
                refine ⟨126493960388055797523075299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84329306925370531682050199 126493960388055797523075299)
                ·
                  refine ⟨189740940582083696284612949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126493960388055797523075299 189740940582083696284612949)
                  ·
                    refine ⟨555881661861573328958827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 189740940582083696284612949 555881661861573328958827)
                    ·
                      rfl

theorem cell23_3247727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_3247727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247727 prefixEnd_3247727 := by exact prefixLift 3247727
  have htrace : WordTrace (prefixWord ++ tailWord_3247727) baseStart_3247727 baseEnd_3247727 := by
    simpa [prefixWord, tailWord_3247727, baseEnd_3247727] using wordTrace_append hprefix tailTrace_3247727
  have hstable : (prefixWord ++ tailWord_3247727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247727).length < 2 ^ (prefixWord ++ tailWord_3247727).sum := by decide
  have hdescent : baseEnd_3247727 < baseStart_3247727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247751 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4]
def baseStart_3247751 : Nat := 118140960795 + 3247751 * 2 ^ 59
def prefixEnd_3247751 : Nat := 4983230072969 + 3 ^ 40 * 3247751 * 2
def baseEnd_3247751 : Nat := 1667657309120427892976371

theorem tailTrace_3247751 : CollatzResearch.WordTrace tailWord_3247751 prefixEnd_3247751 1667657309120427892976371 := by
  unfold tailWord_3247751
  simp only [CollatzResearch.WordTrace]
  refine ⟨118455210456960273556239107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78970140304640182370826071 118455210456960273556239107)
  ·
    refine ⟨177682815685440410334358661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118455210456960273556239107 177682815685440410334358661)
    ·
      refine ⟨33315527941020076937692249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177682815685440410334358661 33315527941020076937692249)
      ·
        refine ⟨24986645955765057703269187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33315527941020076937692249 24986645955765057703269187)
        ·
          refine ⟨37479968933647586554903781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24986645955765057703269187 37479968933647586554903781)
          ·
            refine ⟨7027494175058922479044459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37479968933647586554903781 7027494175058922479044459)
            ·
              refine ⟨10541241262588383718566689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7027494175058922479044459 10541241262588383718566689)
              ·
                refine ⟨7905930946941287788925017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10541241262588383718566689 7905930946941287788925017)
                ·
                  refine ⟨5929448210205965841693763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7905930946941287788925017 5929448210205965841693763)
                  ·
                    refine ⟨8894172315308948762540645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929448210205965841693763 8894172315308948762540645)
                    ·
                      refine ⟨1667657309120427892976371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8894172315308948762540645 1667657309120427892976371)
                      ·
                        rfl

theorem cell23_3247751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_3247751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247751 prefixEnd_3247751 := by exact prefixLift 3247751
  have htrace : WordTrace (prefixWord ++ tailWord_3247751) baseStart_3247751 baseEnd_3247751 := by
    simpa [prefixWord, tailWord_3247751, baseEnd_3247751] using wordTrace_append hprefix tailTrace_3247751
  have hstable : (prefixWord ++ tailWord_3247751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247751).length < 2 ^ (prefixWord ++ tailWord_3247751).sum := by decide
  have hdescent : baseEnd_3247751 < baseStart_3247751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247858 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3247858 : Nat := 118140960795 + 3247858 * 2 ^ 59
def prefixEnd_3247858 : Nat := 4983230072969 + 3 ^ 40 * 3247858 * 2
def baseEnd_3247858 : Nat := 1667712251550458974338379

theorem tailTrace_3247858 : CollatzResearch.WordTrace tailWord_3247858 prefixEnd_3247858 1667712251550458974338379 := by
  unfold tailWord_3247858
  simp only [CollatzResearch.WordTrace]
  refine ⟨29614778266893157707596057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78972742045048420553589485 29614778266893157707596057)
  ·
    refine ⟨22211083700169868280697043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29614778266893157707596057 22211083700169868280697043)
    ·
      refine ⟨33316625550254802421045565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22211083700169868280697043 33316625550254802421045565)
      ·
        refine ⟨12493734581345550907892087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33316625550254802421045565 12493734581345550907892087)
        ·
          refine ⟨18740601872018326361838131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12493734581345550907892087 18740601872018326361838131)
          ·
            refine ⟨28110902808027489542757197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18740601872018326361838131 28110902808027489542757197)
            ·
              refine ⟨10541588553010308578533949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28110902808027489542757197 10541588553010308578533949)
              ·
                refine ⟨3953095707378865716950231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10541588553010308578533949 3953095707378865716950231)
                ·
                  refine ⟨5929643561068298575425347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953095707378865716950231 5929643561068298575425347)
                  ·
                    refine ⟨8894465341602447863138021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5929643561068298575425347 8894465341602447863138021)
                    ·
                      refine ⟨1667712251550458974338379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8894465341602447863138021 1667712251550458974338379)
                      ·
                        rfl

theorem cell23_3247858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3247858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247858 prefixEnd_3247858 := by exact prefixLift 3247858
  have htrace : WordTrace (prefixWord ++ tailWord_3247858) baseStart_3247858 baseEnd_3247858 := by
    simpa [prefixWord, tailWord_3247858, baseEnd_3247858] using wordTrace_append hprefix tailTrace_3247858
  have hstable : (prefixWord ++ tailWord_3247858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247858).length < 2 ^ (prefixWord ++ tailWord_3247858).sum := by decide
  have hdescent : baseEnd_3247858 < baseStart_3247858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247891 : List Nat := [1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3]
def baseStart_3247891 : Nat := 118140960795 + 3247891 * 2 ^ 59
def prefixEnd_3247891 : Nat := 4983230072969 + 3 ^ 40 * 3247891 * 2
def baseEnd_3247891 : Nat := 1667729196412057345225727

theorem tailTrace_3247891 : CollatzResearch.WordTrace tailWord_3247891 prefixEnd_3247891 1667729196412057345225727 := by
  unfold tailWord_3247891
  simp only [CollatzResearch.WordTrace]
  refine ⟨118460316676453077466335527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78973544450968718310890351 118460316676453077466335527)
  ·
    refine ⟨177690475014679616199503291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118460316676453077466335527 177690475014679616199503291)
    ·
      refine ⟨266535712522019424299254937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177690475014679616199503291 266535712522019424299254937)
      ·
        refine ⟨199901784391514568224441203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266535712522019424299254937 199901784391514568224441203)
        ·
          refine ⟨299852676587271852336661805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199901784391514568224441203 299852676587271852336661805)
          ·
            refine ⟨112444753720226944626248177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299852676587271852336661805 112444753720226944626248177)
            ·
              refine ⟨84333565290170208469686133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112444753720226944626248177 84333565290170208469686133)
              ·
                refine ⟨7906271745953457044033075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84333565290170208469686133 7906271745953457044033075)
                ·
                  refine ⟨11859407618930185566049613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7906271745953457044033075 11859407618930185566049613)
                  ·
                    refine ⟨4447277857098819587268605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11859407618930185566049613 4447277857098819587268605)
                    ·
                      refine ⟨1667729196412057345225727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447277857098819587268605 1667729196412057345225727)
                      ·
                        rfl

theorem cell23_3247891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 3].length) (baseStart_3247891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247891 prefixEnd_3247891 := by exact prefixLift 3247891
  have htrace : WordTrace (prefixWord ++ tailWord_3247891) baseStart_3247891 baseEnd_3247891 := by
    simpa [prefixWord, tailWord_3247891, baseEnd_3247891] using wordTrace_append hprefix tailTrace_3247891
  have hstable : (prefixWord ++ tailWord_3247891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247891).length < 2 ^ (prefixWord ++ tailWord_3247891).sum := by decide
  have hdescent : baseEnd_3247891 < baseStart_3247891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247895 : List Nat := [1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 3]
def baseStart_3247895 : Nat := 118140960795 + 3247895 * 2 ^ 59
def prefixEnd_3247895 : Nat := 4983230072969 + 3 ^ 40 * 3247895 * 2
def baseEnd_3247895 : Nat := 1667731250334675329575709

theorem tailTrace_3247895 : CollatzResearch.WordTrace tailWord_3247895 prefixEnd_3247895 1667731250334675329575709 := by
  unfold tailWord_3247895
  simp only [CollatzResearch.WordTrace]
  refine ⟨118460462568438586149481139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78973641712292390766320759 118460462568438586149481139)
  ·
    refine ⟨177690693852657879224221709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118460462568438586149481139 177690693852657879224221709)
    ·
      refine ⟨66634010194746704709083141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177690693852657879224221709 66634010194746704709083141)
      ·
        refine ⟨12493876911515007132953089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66634010194746704709083141 12493876911515007132953089)
        ·
          refine ⟨9370407683636255349714817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12493876911515007132953089 9370407683636255349714817)
          ·
            refine ⟨7027805762727191512286113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9370407683636255349714817 7027805762727191512286113)
            ·
              refine ⟨5270854322045393634214585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7027805762727191512286113 5270854322045393634214585)
              ·
                refine ⟨3953140741534045225660939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5270854322045393634214585 3953140741534045225660939)
                ·
                  refine ⟨5929711112301067838491409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953140741534045225660939 5929711112301067838491409)
                  ·
                    refine ⟨4447283334225800878868557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5929711112301067838491409 4447283334225800878868557)
                    ·
                      refine ⟨1667731250334675329575709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447283334225800878868557 1667731250334675329575709)
                      ·
                        rfl

theorem cell23_3247895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_3247895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247895 prefixEnd_3247895 := by exact prefixLift 3247895
  have htrace : WordTrace (prefixWord ++ tailWord_3247895) baseStart_3247895 baseEnd_3247895 := by
    simpa [prefixWord, tailWord_3247895, baseEnd_3247895] using wordTrace_append hprefix tailTrace_3247895
  have hstable : (prefixWord ++ tailWord_3247895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247895).length < 2 ^ (prefixWord ++ tailWord_3247895).sum := by decide
  have hdescent : baseEnd_3247895 < baseStart_3247895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247898 : List Nat := [3, 1, 1, 3, 2, 4, 2, 7]
def baseStart_3247898 : Nat := 118140960795 + 3247898 * 2 ^ 59
def prefixEnd_3247898 : Nat := 4983230072969 + 3 ^ 40 * 3247898 * 2
def baseEnd_3247898 : Nat := 61767881139875511771785

theorem tailTrace_3247898 : CollatzResearch.WordTrace tailWord_3247898 prefixEnd_3247898 61767881139875511771785 := by
  unfold tailWord_3247898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29615142996856929415460087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78973714658285145107893565 29615142996856929415460087)
  ·
    refine ⟨44422714495285394123190131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29615142996856929415460087 44422714495285394123190131)
    ·
      refine ⟨66634071742928091184785197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44422714495285394123190131 66634071742928091184785197)
      ·
        refine ⟨24987776903598034194294449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66634071742928091184785197 24987776903598034194294449)
        ·
          refine ⟨18740832677698525645720837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24987776903598034194294449 18740832677698525645720837)
          ·
            refine ⟨3513906127068473558572657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18740832677698525645720837 3513906127068473558572657)
            ·
              refine ⟨2635429595301355168929493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3513906127068473558572657 2635429595301355168929493)
              ·
                refine ⟨61767881139875511771785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2635429595301355168929493 61767881139875511771785)
                ·
                  rfl

theorem cell23_3247898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_3247898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247898 prefixEnd_3247898 := by exact prefixLift 3247898
  have htrace : WordTrace (prefixWord ++ tailWord_3247898) baseStart_3247898 baseEnd_3247898 := by
    simpa [prefixWord, tailWord_3247898, baseEnd_3247898] using wordTrace_append hprefix tailTrace_3247898
  have hstable : (prefixWord ++ tailWord_3247898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247898).length < 2 ^ (prefixWord ++ tailWord_3247898).sum := by decide
  have hdescent : baseEnd_3247898 < baseStart_3247898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247909 : List Nat := [1, 3, 1, 2, 3, 4, 1, 3, 1, 2, 2]
def baseStart_3247909 : Nat := 118140960795 + 3247909 * 2 ^ 59
def prefixEnd_3247909 : Nat := 4983230072969 + 3 ^ 40 * 3247909 * 2
def baseEnd_3247909 : Nat := 1667738439063838274800645

theorem tailTrace_3247909 : CollatzResearch.WordTrace tailWord_3247909 prefixEnd_3247909 1667738439063838274800645 := by
  unfold tailWord_3247909
  simp only [CollatzResearch.WordTrace]
  refine ⟨118460973190387866540490781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78973982126925244360327187 118460973190387866540490781)
  ·
    refine ⟨44422864946395449952684043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118460973190387866540490781 44422864946395449952684043)
    ·
      refine ⟨66634297419593174929026065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44422864946395449952684043 66634297419593174929026065)
      ·
        refine ⟨49975723064694881196769549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66634297419593174929026065 49975723064694881196769549)
        ·
          refine ⟨18740896149260580448788581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49975723064694881196769549 18740896149260580448788581)
          ·
            refine ⟨3513918027986358834147859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18740896149260580448788581 3513918027986358834147859)
            ·
              refine ⟨5270877041979538251221789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3513918027986358834147859 5270877041979538251221789)
              ·
                refine ⟨1976578890742326844208171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5270877041979538251221789 1976578890742326844208171)
                ·
                  refine ⟨2964868336113490266312257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976578890742326844208171 2964868336113490266312257)
                  ·
                    refine ⟨2223651252085117699734193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2964868336113490266312257 2223651252085117699734193)
                    ·
                      refine ⟨1667738439063838274800645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223651252085117699734193 1667738439063838274800645)
                      ·
                        rfl

theorem cell23_3247909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 1, 3, 1, 2, 2].length) (baseStart_3247909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247909 prefixEnd_3247909 := by exact prefixLift 3247909
  have htrace : WordTrace (prefixWord ++ tailWord_3247909) baseStart_3247909 baseEnd_3247909 := by
    simpa [prefixWord, tailWord_3247909, baseEnd_3247909] using wordTrace_append hprefix tailTrace_3247909
  have hstable : (prefixWord ++ tailWord_3247909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247909).length < 2 ^ (prefixWord ++ tailWord_3247909).sum := by decide
  have hdescent : baseEnd_3247909 < baseStart_3247909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3247981 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3247981 : Nat := 118140960795 + 3247981 * 2 ^ 59
def prefixEnd_3247981 : Nat := 4983230072969 + 3 ^ 40 * 3247981 * 2
def baseEnd_3247981 : Nat := 1667775409670961993100313

theorem tailTrace_3247981 : CollatzResearch.WordTrace tailWord_3247981 prefixEnd_3247981 1667775409670961993100313 := by
  unfold tailWord_3247981
  simp only [CollatzResearch.WordTrace]
  refine ⟨118463599246127022837111797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78975732830751348558074531 118463599246127022837111797)
  ·
    refine ⟨11105962429324408390979231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118463599246127022837111797 11105962429324408390979231)
    ·
      refine ⟨16658943643986612586468847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11105962429324408390979231 16658943643986612586468847)
      ·
        refine ⟨24988415465979918879703271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16658943643986612586468847 24988415465979918879703271)
        ·
          refine ⟨37482623198969878319554907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24988415465979918879703271 37482623198969878319554907)
          ·
            refine ⟨56223934798454817479332361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37482623198969878319554907 56223934798454817479332361)
            ·
              refine ⟨42167951098841113109499271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56223934798454817479332361 42167951098841113109499271)
              ·
                refine ⟨63251926648261669664248907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42167951098841113109499271 63251926648261669664248907)
                ·
                  refine ⟨94877889972392504496373361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63251926648261669664248907 94877889972392504496373361)
                  ·
                    refine ⟨71158417479294378372280021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94877889972392504496373361 71158417479294378372280021)
                    ·
                      refine ⟨1667775409670961993100313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71158417479294378372280021 1667775409670961993100313)
                      ·
                        rfl

theorem cell23_3247981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3247981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3247981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3247981 prefixEnd_3247981 := by exact prefixLift 3247981
  have htrace : WordTrace (prefixWord ++ tailWord_3247981) baseStart_3247981 baseEnd_3247981 := by
    simpa [prefixWord, tailWord_3247981, baseEnd_3247981] using wordTrace_append hprefix tailTrace_3247981
  have hstable : (prefixWord ++ tailWord_3247981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3247981).length < 2 ^ (prefixWord ++ tailWord_3247981).sum := by decide
  have hdescent : baseEnd_3247981 < baseStart_3247981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3247981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248051 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6]
def baseStart_3248051 : Nat := 118140960795 + 3248051 * 2 ^ 59
def prefixEnd_3248051 : Nat := 4983230072969 + 3 ^ 40 * 3248051 * 2
def baseEnd_3248051 : Nat := 1667811353316776719224991

theorem tailTrace_3248051 : CollatzResearch.WordTrace tailWord_3248051 prefixEnd_3248051 1667811353316776719224991 := by
  unfold tailWord_3248051
  simp only [CollatzResearch.WordTrace]
  refine ⟨118466152355873424792160007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78977434903915616528106671 118466152355873424792160007)
  ·
    refine ⟨177699228533810137188240011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118466152355873424792160007 177699228533810137188240011)
    ·
      refine ⟨266548842800715205782360017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177699228533810137188240011 266548842800715205782360017)
      ·
        refine ⟨199911632100536404336770013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266548842800715205782360017 199911632100536404336770013)
        ·
          refine ⟨74966862037701151626288755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199911632100536404336770013 74966862037701151626288755)
          ·
            refine ⟨112450293056551727439433133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74966862037701151626288755 112450293056551727439433133)
            ·
              refine ⟨42168859896206897789787425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112450293056551727439433133 42168859896206897789787425)
              ·
                refine ⟨31626644922155173342340569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42168859896206897789787425 31626644922155173342340569)
                ·
                  refine ⟨23719983691616380006755427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31626644922155173342340569 23719983691616380006755427)
                  ·
                    refine ⟨35579975537424570010133141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23719983691616380006755427 35579975537424570010133141)
                    ·
                      refine ⟨1667811353316776719224991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35579975537424570010133141 1667811353316776719224991)
                      ·
                        rfl

theorem cell23_3248051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_3248051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248051 prefixEnd_3248051 := by exact prefixLift 3248051
  have htrace : WordTrace (prefixWord ++ tailWord_3248051) baseStart_3248051 baseEnd_3248051 := by
    simpa [prefixWord, tailWord_3248051, baseEnd_3248051] using wordTrace_append hprefix tailTrace_3248051
  have hstable : (prefixWord ++ tailWord_3248051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248051).length < 2 ^ (prefixWord ++ tailWord_3248051).sum := by decide
  have hdescent : baseEnd_3248051 < baseStart_3248051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248058 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3]
def baseStart_3248058 : Nat := 118140960795 + 3248058 * 2 ^ 59
def prefixEnd_3248058 : Nat := 4983230072969 + 3 ^ 40 * 3248058 * 2
def baseEnd_3248058 : Nat := 1667814947681358191837459

theorem tailTrace_3248058 : CollatzResearch.WordTrace tailWord_3248058 prefixEnd_3248058 1667814947681358191837459 := by
  unfold tailWord_3248058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29616601916712016246916207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78977605111232043325109885 29616601916712016246916207)
  ·
    refine ⟨44424902875068024370374311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29616601916712016246916207 44424902875068024370374311)
    ·
      refine ⟨66637354312602036555561467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44424902875068024370374311 66637354312602036555561467)
      ·
        refine ⟨99956031468903054833342201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66637354312602036555561467 99956031468903054833342201)
        ·
          refine ⟨74967023601677291125006651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99956031468903054833342201 74967023601677291125006651)
          ·
            refine ⟨112450535402515936687509977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74967023601677291125006651 112450535402515936687509977)
            ·
              refine ⟨84337901551886952515632483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112450535402515936687509977 84337901551886952515632483)
              ·
                refine ⟨126506852327830428773448725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84337901551886952515632483 126506852327830428773448725)
                ·
                  refine ⟨5930008702867051348755409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126506852327830428773448725 5930008702867051348755409)
                  ·
                    refine ⟨4447506527150288511566557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930008702867051348755409 4447506527150288511566557)
                    ·
                      refine ⟨1667814947681358191837459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447506527150288511566557 1667814947681358191837459)
                      ·
                        rfl

theorem cell23_3248058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3].length) (baseStart_3248058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248058 prefixEnd_3248058 := by exact prefixLift 3248058
  have htrace : WordTrace (prefixWord ++ tailWord_3248058) baseStart_3248058 baseEnd_3248058 := by
    simpa [prefixWord, tailWord_3248058, baseEnd_3248058] using wordTrace_append hprefix tailTrace_3248058
  have hstable : (prefixWord ++ tailWord_3248058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248058).length < 2 ^ (prefixWord ++ tailWord_3248058).sum := by decide
  have hdescent : baseEnd_3248058 < baseStart_3248058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248081 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_3248081 : Nat := 118140960795 + 3248081 * 2 ^ 59
def prefixEnd_3248081 : Nat := 4983230072969 + 3 ^ 40 * 3248081 * 2
def baseEnd_3248081 : Nat := 1667826757736411601849853

theorem tailTrace_3248081 : CollatzResearch.WordTrace tailWord_3248081 prefixEnd_3248081 1667826757736411601849853 := by
  unfold tailWord_3248081
  simp only [CollatzResearch.WordTrace]
  refine ⟨118467246545764739915752097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78978164363843159943834731 118467246545764739915752097)
  ·
    refine ⟨88850434909323554936814073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118467246545764739915752097 88850434909323554936814073)
    ·
      refine ⟨66637826181992666202610555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88850434909323554936814073 66637826181992666202610555)
      ·
        refine ⟨99956739272988999303915833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66637826181992666202610555 99956739272988999303915833)
        ·
          refine ⟨74967554454741749477936875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99956739272988999303915833 74967554454741749477936875)
          ·
            refine ⟨112451331682112624216905313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74967554454741749477936875 112451331682112624216905313)
            ·
              refine ⟨84338498761584468162678985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112451331682112624216905313 84338498761584468162678985)
              ·
                refine ⟨63253874071188351122009239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84338498761584468162678985 63253874071188351122009239)
                ·
                  refine ⟨94880811106782526683013859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63253874071188351122009239 94880811106782526683013859)
                  ·
                    refine ⟨142321216660173790024520789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94880811106782526683013859 142321216660173790024520789)
                    ·
                      refine ⟨1667826757736411601849853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 142321216660173790024520789 1667826757736411601849853)
                      ·
                        rfl

theorem cell23_3248081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_3248081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248081 prefixEnd_3248081 := by exact prefixLift 3248081
  have htrace : WordTrace (prefixWord ++ tailWord_3248081) baseStart_3248081 baseEnd_3248081 := by
    simpa [prefixWord, tailWord_3248081, baseEnd_3248081] using wordTrace_append hprefix tailTrace_3248081
  have hstable : (prefixWord ++ tailWord_3248081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248081).length < 2 ^ (prefixWord ++ tailWord_3248081).sum := by decide
  have hdescent : baseEnd_3248081 < baseStart_3248081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248099 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 1, 4]
def baseStart_3248099 : Nat := 118140960795 + 3248099 * 2 ^ 59
def prefixEnd_3248099 : Nat := 4983230072969 + 3 ^ 40 * 3248099 * 2
def baseEnd_3248099 : Nat := 555945333462730843808257

theorem tailTrace_3248099 : CollatzResearch.WordTrace tailWord_3248099 prefixEnd_3248099 555945333462730843808257 := by
  unfold tailWord_3248099
  simp only [CollatzResearch.WordTrace]
  refine ⟨118467903059699528989907351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78978602039799685993271567 118467903059699528989907351)
  ·
    refine ⟨177701854589549293484861027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118467903059699528989907351 177701854589549293484861027)
    ·
      refine ⟨266552781884323940227291541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177701854589549293484861027 266552781884323940227291541)
      ·
        refine ⟨12494661650827684698154291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266552781884323940227291541 12494661650827684698154291)
        ·
          refine ⟨18741992476241527047231437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494661650827684698154291 18741992476241527047231437)
          ·
            refine ⟨7028247178590572642711789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18741992476241527047231437 7028247178590572642711789)
            ·
              refine ⟨2635592691971464741016921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7028247178590572642711789 2635592691971464741016921)
              ·
                refine ⟨1976694518978598555762691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635592691971464741016921 1976694518978598555762691)
                ·
                  refine ⟨2965041778467897833644037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976694518978598555762691 2965041778467897833644037)
                  ·
                    refine ⟨555945333462730843808257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965041778467897833644037 555945333462730843808257)
                    ·
                      rfl

theorem cell23_3248099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 4].length) (baseStart_3248099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248099 prefixEnd_3248099 := by exact prefixLift 3248099
  have htrace : WordTrace (prefixWord ++ tailWord_3248099) baseStart_3248099 baseEnd_3248099 := by
    simpa [prefixWord, tailWord_3248099, baseEnd_3248099] using wordTrace_append hprefix tailTrace_3248099
  have hstable : (prefixWord ++ tailWord_3248099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248099).length < 2 ^ (prefixWord ++ tailWord_3248099).sum := by decide
  have hdescent : baseEnd_3248099 < baseStart_3248099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248125 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 1, 5]
def baseStart_3248125 : Nat := 118140960795 + 3248125 * 2 ^ 59
def prefixEnd_3248125 : Nat := 4983230072969 + 3 ^ 40 * 3248125 * 2
def baseEnd_3248125 : Nat := 555949783628403143233217

theorem tailTrace_3248125 : CollatzResearch.WordTrace tailWord_3248125 prefixEnd_3248125 555949783628403143233217 := by
  unfold tailWord_3248125
  simp only [CollatzResearch.WordTrace]
  refine ⟨118468851357605335430353829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78979234238403556953569219 118468851357605335430353829)
  ·
    refine ⟨22212909629551000393191343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118468851357605335430353829 22212909629551000393191343)
    ·
      refine ⟨33319364444326500589787015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22212909629551000393191343 33319364444326500589787015)
      ·
        refine ⟨49979046666489750884680523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33319364444326500589787015 49979046666489750884680523)
        ·
          refine ⟨74968569999734626327020785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49979046666489750884680523 74968569999734626327020785)
          ·
            refine ⟨56226427499800969745265589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74968569999734626327020785 56226427499800969745265589)
            ·
              refine ⟨5271227578106340913618649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56226427499800969745265589 5271227578106340913618649)
              ·
                refine ⟨3953420683579755685213987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5271227578106340913618649 3953420683579755685213987)
                ·
                  refine ⟨5930131025369633527820981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953420683579755685213987 5930131025369633527820981)
                  ·
                    refine ⟨555949783628403143233217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5930131025369633527820981 555949783628403143233217)
                    ·
                      rfl

theorem cell23_3248125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_3248125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248125 prefixEnd_3248125 := by exact prefixLift 3248125
  have htrace : WordTrace (prefixWord ++ tailWord_3248125) baseStart_3248125 baseEnd_3248125 := by
    simpa [prefixWord, tailWord_3248125, baseEnd_3248125] using wordTrace_append hprefix tailTrace_3248125
  have hstable : (prefixWord ++ tailWord_3248125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248125).length < 2 ^ (prefixWord ++ tailWord_3248125).sum := by decide
  have hdescent : baseEnd_3248125 < baseStart_3248125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248142 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 1, 5]
def baseStart_3248142 : Nat := 118140960795 + 3248142 * 2 ^ 59
def prefixEnd_3248142 : Nat := 4983230072969 + 3 ^ 40 * 3248142 * 2
def baseEnd_3248142 : Nat := 555952693352111954395691

theorem tailTrace_3248142 : CollatzResearch.WordTrace tailWord_3248142 prefixEnd_3248142 555952693352111954395691 := by
  unfold tailWord_3248142
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808683924817968416715335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78979647599029164889148453 14808683924817968416715335)
  ·
    refine ⟨22213025887226952625073003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14808683924817968416715335 22213025887226952625073003)
    ·
      refine ⟨33319538830840428937609505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22213025887226952625073003 33319538830840428937609505)
      ·
        refine ⟨24989654123130321703207129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33319538830840428937609505 24989654123130321703207129)
        ·
          refine ⟨18742240592347741277405347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24989654123130321703207129 18742240592347741277405347)
          ·
            refine ⟨28113360888521611916108021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18742240592347741277405347 28113360888521611916108021)
            ·
              refine ⟨2635627583298901117135127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28113360888521611916108021 2635627583298901117135127)
              ·
                refine ⟨3953441374948351675702691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635627583298901117135127 3953441374948351675702691)
                ·
                  refine ⟨5930162062422527513554037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953441374948351675702691 5930162062422527513554037)
                  ·
                    refine ⟨555952693352111954395691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5930162062422527513554037 555952693352111954395691)
                    ·
                      rfl

theorem cell23_3248142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 5].length) (baseStart_3248142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248142 prefixEnd_3248142 := by exact prefixLift 3248142
  have htrace : WordTrace (prefixWord ++ tailWord_3248142) baseStart_3248142 baseEnd_3248142 := by
    simpa [prefixWord, tailWord_3248142, baseEnd_3248142] using wordTrace_append hprefix tailTrace_3248142
  have hstable : (prefixWord ++ tailWord_3248142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248142).length < 2 ^ (prefixWord ++ tailWord_3248142).sum := by decide
  have hdescent : baseEnd_3248142 < baseStart_3248142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248156 : List Nat := [2, 2, 3, 1, 3, 1, 4, 2, 1, 1, 3]
def baseStart_3248156 : Nat := 118140960795 + 3248156 * 2 ^ 59
def prefixEnd_3248156 : Nat := 4983230072969 + 3 ^ 40 * 3248156 * 2
def baseEnd_3248156 : Nat := 1667865268785498808412009

theorem tailTrace_3248156 : CollatzResearch.WordTrace tailWord_3248156 prefixEnd_3248156 1667865268785498808412009 := by
  unfold tailWord_3248156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59234991010246513862366161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78979988013662018483154881 59234991010246513862366161)
  ·
    refine ⟨44426243257684885396774621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59234991010246513862366161 44426243257684885396774621)
    ·
      refine ⟨16659841221631832023790483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44426243257684885396774621 16659841221631832023790483)
      ·
        refine ⟨24989761832447748035685725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16659841221631832023790483 24989761832447748035685725)
        ·
          refine ⟨9371160687167905513382147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24989761832447748035685725 9371160687167905513382147)
          ·
            refine ⟨14056741030751858270073221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371160687167905513382147 14056741030751858270073221)
            ·
              refine ⟨2635638943265973425638729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14056741030751858270073221 2635638943265973425638729)
              ·
                refine ⟨1976729207449480069229047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635638943265973425638729 1976729207449480069229047)
                ·
                  refine ⟨2965093811174220103843571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976729207449480069229047 2965093811174220103843571)
                  ·
                    refine ⟨4447640716761330155765357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2965093811174220103843571 4447640716761330155765357)
                    ·
                      refine ⟨1667865268785498808412009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447640716761330155765357 1667865268785498808412009)
                      ·
                        rfl

theorem cell23_3248156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_3248156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248156 prefixEnd_3248156 := by exact prefixLift 3248156
  have htrace : WordTrace (prefixWord ++ tailWord_3248156) baseStart_3248156 baseEnd_3248156 := by
    simpa [prefixWord, tailWord_3248156, baseEnd_3248156] using wordTrace_append hprefix tailTrace_3248156
  have hstable : (prefixWord ++ tailWord_3248156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248156).length < 2 ^ (prefixWord ++ tailWord_3248156).sum := by decide
  have hdescent : baseEnd_3248156 < baseStart_3248156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248165 : List Nat := [1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 3]
def baseStart_3248165 : Nat := 118140960795 + 3248165 * 2 ^ 59
def prefixEnd_3248165 : Nat := 4983230072969 + 3 ^ 40 * 3248165 * 2
def baseEnd_3248165 : Nat := 1667869890111389273199467

theorem tailTrace_3248165 : CollatzResearch.WordTrace tailWord_3248165 prefixEnd_3248165 1667869890111389273199467 := by
  unfold tailWord_3248165
  simp only [CollatzResearch.WordTrace]
  refine ⟨118470310277460422261809949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78980206851640281507873299 118470310277460422261809949)
  ·
    refine ⟨44426366354047658348178731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118470310277460422261809949 44426366354047658348178731)
    ·
      refine ⟨66639549531071487522268097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44426366354047658348178731 66639549531071487522268097)
      ·
        refine ⟨49979662148303615641701073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66639549531071487522268097 49979662148303615641701073)
        ·
          refine ⟨37484746611227711731275805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49979662148303615641701073 37484746611227711731275805)
          ·
            refine ⟨14056779979210391899228427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37484746611227711731275805 14056779979210391899228427)
            ·
              refine ⟨21085169968815587848842641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14056779979210391899228427 21085169968815587848842641)
              ·
                refine ⟨15813877476611690886631981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21085169968815587848842641 15813877476611690886631981)
                ·
                  refine ⟨5930204053729384082486993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15813877476611690886631981 5930204053729384082486993)
                  ·
                    refine ⟨4447653040297038061865245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930204053729384082486993 4447653040297038061865245)
                    ·
                      refine ⟨1667869890111389273199467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447653040297038061865245 1667869890111389273199467)
                      ·
                        rfl

theorem cell23_3248165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_3248165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248165 prefixEnd_3248165 := by exact prefixLift 3248165
  have htrace : WordTrace (prefixWord ++ tailWord_3248165) baseStart_3248165 baseEnd_3248165 := by
    simpa [prefixWord, tailWord_3248165, baseEnd_3248165] using wordTrace_append hprefix tailTrace_3248165
  have hstable : (prefixWord ++ tailWord_3248165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248165).length < 2 ^ (prefixWord ++ tailWord_3248165).sum := by decide
  have hdescent : baseEnd_3248165 < baseStart_3248165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248182 : List Nat := [5, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_3248182 : Nat := 118140960795 + 3248182 * 2 ^ 59
def prefixEnd_3248182 : Nat := 4983230072969 + 3 ^ 40 * 3248182 * 2
def baseEnd_3248182 : Nat := 1667878619282515706686889

theorem tailTrace_3248182 : CollatzResearch.WordTrace tailWord_3248182 prefixEnd_3248182 1667878619282515706686889 := by
  unfold tailWord_3248182
  simp only [CollatzResearch.WordTrace]
  refine ⟨7404433144899927135323675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78980620212265889443452533 7404433144899927135323675)
  ·
    refine ⟨11106649717349890702985513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7404433144899927135323675 11106649717349890702985513)
    ·
      refine ⟨8329987288012418027239135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11106649717349890702985513 8329987288012418027239135)
      ·
        refine ⟨12494980932018627040858703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8329987288012418027239135 12494980932018627040858703)
        ·
          refine ⟨18742471398027940561288055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494980932018627040858703 18742471398027940561288055)
          ·
            refine ⟨28113707097041910841932083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18742471398027940561288055 28113707097041910841932083)
            ·
              refine ⟨42170560645562866262898125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28113707097041910841932083 42170560645562866262898125)
              ·
                refine ⟨15813960242086074848586797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42170560645562866262898125 15813960242086074848586797)
                ·
                  refine ⟨5930235090782278068220049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15813960242086074848586797 5930235090782278068220049)
                  ·
                    refine ⟨4447676318086708551165037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5930235090782278068220049 4447676318086708551165037)
                    ·
                      refine ⟨1667878619282515706686889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447676318086708551165037 1667878619282515706686889)
                      ·
                        rfl

theorem cell23_3248182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_3248182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248182 prefixEnd_3248182 := by exact prefixLift 3248182
  have htrace : WordTrace (prefixWord ++ tailWord_3248182) baseStart_3248182 baseEnd_3248182 := by
    simpa [prefixWord, tailWord_3248182, baseEnd_3248182] using wordTrace_append hprefix tailTrace_3248182
  have hstable : (prefixWord ++ tailWord_3248182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248182).length < 2 ^ (prefixWord ++ tailWord_3248182).sum := by decide
  have hdescent : baseEnd_3248182 < baseStart_3248182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248226 : List Nat := [3, 3, 2, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3248226 : Nat := 118140960795 + 3248226 * 2 ^ 59
def prefixEnd_3248226 : Nat := 4983230072969 + 3 ^ 40 * 3248226 * 2
def baseEnd_3248226 : Nat := 1667901212431313534536687

theorem tailTrace_3248226 : CollatzResearch.WordTrace tailWord_3248226 prefixEnd_3248226 1667901212431313534536687 := by
  unfold tailWord_3248226
  simp only [CollatzResearch.WordTrace]
  refine ⟨29618133782559857419945133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78981690086826286453187021 29618133782559857419945133)
  ·
    refine ⟨11106800168459946532479425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29618133782559857419945133 11106800168459946532479425)
    ·
      refine ⟨8330100126344959899359569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11106800168459946532479425 8330100126344959899359569)
      ·
        refine ⟨6247575094758719924519677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8330100126344959899359569 6247575094758719924519677)
        ·
          refine ⟨2342840660534519971694879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6247575094758719924519677 2342840660534519971694879)
          ·
            refine ⟨3514260990801779957542319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342840660534519971694879 3514260990801779957542319)
            ·
              refine ⟨5271391486202669936313479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514260990801779957542319 5271391486202669936313479)
              ·
                refine ⟨7907087229304004904470219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271391486202669936313479 7907087229304004904470219)
                ·
                  refine ⟨11860630843956007356705329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907087229304004904470219 11860630843956007356705329)
                  ·
                    refine ⟨8895473132967005517528997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11860630843956007356705329 8895473132967005517528997)
                    ·
                      refine ⟨1667901212431313534536687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8895473132967005517528997 1667901212431313534536687)
                      ·
                        rfl

theorem cell23_3248226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3248226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248226 prefixEnd_3248226 := by exact prefixLift 3248226
  have htrace : WordTrace (prefixWord ++ tailWord_3248226) baseStart_3248226 baseEnd_3248226 := by
    simpa [prefixWord, tailWord_3248226, baseEnd_3248226] using wordTrace_append hprefix tailTrace_3248226
  have hstable : (prefixWord ++ tailWord_3248226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248226).length < 2 ^ (prefixWord ++ tailWord_3248226).sum := by decide
  have hdescent : baseEnd_3248226 < baseStart_3248226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248239 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 1, 3, 2]
def baseStart_3248239 : Nat := 118140960795 + 3248239 * 2 ^ 59
def prefixEnd_3248239 : Nat := 4983230072969 + 3 ^ 40 * 3248239 * 2
def baseEnd_3248239 : Nat := 1667907887679821983674127

theorem tailTrace_3248239 : CollatzResearch.WordTrace tailWord_3248239 prefixEnd_3248239 1667907887679821983674127 := by
  unfold tailWord_3248239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118473009279192332900003771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78982006186128221933335847 118473009279192332900003771)
  ·
    refine ⟨177709513918788499350005657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118473009279192332900003771 177709513918788499350005657)
    ·
      refine ⟨133282135439091374512504243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177709513918788499350005657 133282135439091374512504243)
      ·
        refine ⟨199923203158637061768756365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133282135439091374512504243 199923203158637061768756365)
        ·
          refine ⟨74971201184488898163283637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199923203158637061768756365 74971201184488898163283637)
          ·
            refine ⟨7028550111045834202807841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74971201184488898163283637 7028550111045834202807841)
            ·
              refine ⟨5271412583284375652105881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028550111045834202807841 5271412583284375652105881)
              ·
                refine ⟨3953559437463281739079411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5271412583284375652105881 3953559437463281739079411)
                ·
                  refine ⟨5930339156194922608619117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953559437463281739079411 5930339156194922608619117)
                  ·
                    refine ⟨2223877183573095978232169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5930339156194922608619117 2223877183573095978232169)
                    ·
                      refine ⟨1667907887679821983674127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2223877183573095978232169 1667907887679821983674127)
                      ·
                        rfl

theorem cell23_3248239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 3, 2].length) (baseStart_3248239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248239 prefixEnd_3248239 := by exact prefixLift 3248239
  have htrace : WordTrace (prefixWord ++ tailWord_3248239) baseStart_3248239 baseEnd_3248239 := by
    simpa [prefixWord, tailWord_3248239, baseEnd_3248239] using wordTrace_append hprefix tailTrace_3248239
  have hstable : (prefixWord ++ tailWord_3248239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248239).length < 2 ^ (prefixWord ++ tailWord_3248239).sum := by decide
  have hdescent : baseEnd_3248239 < baseStart_3248239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248352 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 3, 4]
def baseStart_3248352 : Nat := 118140960795 + 3248352 * 2 ^ 59
def prefixEnd_3248352 : Nat := 4983230072969 + 3 ^ 40 * 3248352 * 2
def baseEnd_3248352 : Nat := 555988636997926680520369

theorem tailTrace_3248352 : CollatzResearch.WordTrace tailWord_3248352 prefixEnd_3248352 555988636997926680520369 := by
  unfold tailWord_3248352
  simp only [CollatzResearch.WordTrace]
  refine ⟨59238565363891476599433655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78984753818521968799244873 59238565363891476599433655)
  ·
    refine ⟨88857848045837214899150483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59238565363891476599433655 88857848045837214899150483)
    ·
      refine ⟨133286772068755822348725725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88857848045837214899150483 133286772068755822348725725)
      ·
        refine ⟨49982539525783433380772147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133286772068755822348725725 49982539525783433380772147)
        ·
          refine ⟨74973809288675150071158221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49982539525783433380772147 74973809288675150071158221)
          ·
            refine ⟨28115178483253181276684333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74973809288675150071158221 28115178483253181276684333)
            ·
              refine ⟨10543191931219942978756625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28115178483253181276684333 10543191931219942978756625)
              ·
                refine ⟨7907393948414957234067469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10543191931219942978756625 7907393948414957234067469)
                ·
                  refine ⟨2965272730655608962775301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7907393948414957234067469 2965272730655608962775301)
                  ·
                    refine ⟨555988636997926680520369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965272730655608962775301 555988636997926680520369)
                    ·
                      rfl

theorem cell23_3248352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 4].length) (baseStart_3248352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248352 prefixEnd_3248352 := by exact prefixLift 3248352
  have htrace : WordTrace (prefixWord ++ tailWord_3248352) baseStart_3248352 baseEnd_3248352 := by
    simpa [prefixWord, tailWord_3248352, baseEnd_3248352] using wordTrace_append hprefix tailTrace_3248352
  have hstable : (prefixWord ++ tailWord_3248352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248352).length < 2 ^ (prefixWord ++ tailWord_3248352).sum := by decide
  have hdescent : baseEnd_3248352 < baseStart_3248352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248359 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3248359 : Nat := 118140960795 + 3248359 * 2 ^ 59
def prefixEnd_3248359 : Nat := 4983230072969 + 3 ^ 40 * 3248359 * 2
def baseEnd_3248359 : Nat := 1667969505358361514173575

theorem tailTrace_3248359 : CollatzResearch.WordTrace tailWord_3248359 prefixEnd_3248359 1667969505358361514173575 := by
  unfold tailWord_3248359
  simp only [CollatzResearch.WordTrace]
  refine ⟨118477386038757593394372131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78984924025838395596248087 118477386038757593394372131)
  ·
    refine ⟨177716079058136390091558197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118477386038757593394372131 177716079058136390091558197)
    ·
      refine ⟨16660882411700286571083581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177716079058136390091558197 16660882411700286571083581)
      ·
        refine ⟨6247830904387607464156343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16660882411700286571083581 6247830904387607464156343)
        ·
          refine ⟨9371746356581411196234515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6247830904387607464156343 9371746356581411196234515)
          ·
            refine ⟨14057619534872116794351773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9371746356581411196234515 14057619534872116794351773)
            ·
              refine ⟨5271607325577043797881915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14057619534872116794351773 5271607325577043797881915)
              ·
                refine ⟨7907410988365565696822873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271607325577043797881915 7907410988365565696822873)
                ·
                  refine ⟨5930558241274174272617155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907410988365565696822873 5930558241274174272617155)
                  ·
                    refine ⟨8895837361911261408925733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930558241274174272617155 8895837361911261408925733)
                    ·
                      refine ⟨1667969505358361514173575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8895837361911261408925733 1667969505358361514173575)
                      ·
                        rfl

theorem cell23_3248359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3248359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248359 prefixEnd_3248359 := by exact prefixLift 3248359
  have htrace : WordTrace (prefixWord ++ tailWord_3248359) baseStart_3248359 baseEnd_3248359 := by
    simpa [prefixWord, tailWord_3248359, baseEnd_3248359] using wordTrace_append hprefix tailTrace_3248359
  have hstable : (prefixWord ++ tailWord_3248359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248359).length < 2 ^ (prefixWord ++ tailWord_3248359).sum := by decide
  have hdescent : baseEnd_3248359 < baseStart_3248359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248362 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3248362 : Nat := 118140960795 + 3248362 * 2 ^ 59
def prefixEnd_3248362 : Nat := 4983230072969 + 3 ^ 40 * 3248362 * 2
def baseEnd_3248362 : Nat := 1667971045800325002436061

theorem tailTrace_3248362 : CollatzResearch.WordTrace tailWord_3248362 prefixEnd_3248362 1667971045800325002436061 := by
  unfold tailWord_3248362
  simp only [CollatzResearch.WordTrace]
  refine ⟨29619373864436681226682835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78984996971831149937820893 29619373864436681226682835)
  ·
    refine ⟨44429060796655021840024253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29619373864436681226682835 44429060796655021840024253)
    ·
      refine ⟨16660897798745633190009095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44429060796655021840024253 16660897798745633190009095)
      ·
        refine ⟨24991346698118449785013643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16660897798745633190009095 24991346698118449785013643)
        ·
          refine ⟨37487020047177674677520465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24991346698118449785013643 37487020047177674677520465)
          ·
            refine ⟨28115265035383256008140349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37487020047177674677520465 28115265035383256008140349)
            ·
              refine ⟨10543224388268721003052631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28115265035383256008140349 10543224388268721003052631)
              ·
                refine ⟨15814836582403081504578947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543224388268721003052631 15814836582403081504578947)
                ·
                  refine ⟨23722254873604622256868421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15814836582403081504578947 23722254873604622256868421)
                  ·
                    refine ⟨4447922788800866673162829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23722254873604622256868421 4447922788800866673162829)
                    ·
                      refine ⟨1667971045800325002436061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4447922788800866673162829 1667971045800325002436061)
                      ·
                        rfl

theorem cell23_3248362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3248362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248362 prefixEnd_3248362 := by exact prefixLift 3248362
  have htrace : WordTrace (prefixWord ++ tailWord_3248362) baseStart_3248362 baseEnd_3248362 := by
    simpa [prefixWord, tailWord_3248362, baseEnd_3248362] using wordTrace_append hprefix tailTrace_3248362
  have hstable : (prefixWord ++ tailWord_3248362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248362).length < 2 ^ (prefixWord ++ tailWord_3248362).sum := by decide
  have hdescent : baseEnd_3248362 < baseStart_3248362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248369 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 1, 4]
def baseStart_3248369 : Nat := 118140960795 + 3248369 * 2 ^ 59
def prefixEnd_3248369 : Nat := 4983230072969 + 3 ^ 40 * 3248369 * 2
def baseEnd_3248369 : Nat := 555991546721635491682843

theorem tailTrace_3248369 : CollatzResearch.WordTrace tailWord_3248369 prefixEnd_3248369 555991546721635491682843 := by
  unfold tailWord_3248369
  simp only [CollatzResearch.WordTrace]
  refine ⟨118477750768721365102236161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78985167179147576734824107 118477750768721365102236161)
  ·
    refine ⟨88858313076541023826677121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118477750768721365102236161 88858313076541023826677121)
    ·
      refine ⟨66643734807405767870007841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88858313076541023826677121 66643734807405767870007841)
      ·
        refine ⟨49982801105554325902505881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66643734807405767870007841 49982801105554325902505881)
        ·
          refine ⟨37487100829165744426879411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49982801105554325902505881 37487100829165744426879411)
          ·
            refine ⟨56230651243748616640319117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37487100829165744426879411 56230651243748616640319117)
            ·
              refine ⟨21086494216405731240119669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56230651243748616640319117 21086494216405731240119669)
              ·
                refine ⟨1976858832788037303761219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21086494216405731240119669 1976858832788037303761219)
                ·
                  refine ⟨2965288249182055955641829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976858832788037303761219 2965288249182055955641829)
                  ·
                    refine ⟨555991546721635491682843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965288249182055955641829 555991546721635491682843)
                    ·
                      rfl

theorem cell23_3248369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_3248369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248369 prefixEnd_3248369 := by exact prefixLift 3248369
  have htrace : WordTrace (prefixWord ++ tailWord_3248369) baseStart_3248369 baseEnd_3248369 := by
    simpa [prefixWord, tailWord_3248369, baseEnd_3248369] using wordTrace_append hprefix tailTrace_3248369
  have hstable : (prefixWord ++ tailWord_3248369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248369).length < 2 ^ (prefixWord ++ tailWord_3248369).sum := by decide
  have hdescent : baseEnd_3248369 < baseStart_3248369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248382 : List Nat := [4, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_3248382 : Nat := 118140960795 + 3248382 * 2 ^ 59
def prefixEnd_3248382 : Nat := 4983230072969 + 3 ^ 40 * 3248382 * 2
def baseEnd_3248382 : Nat := 185331257268157213798441

theorem tailTrace_3248382 : CollatzResearch.WordTrace tailWord_3248382 prefixEnd_3248382 185331257268157213798441 := by
  unfold tailWord_3248382
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809778114709283540307425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78985483278449512214972933 14809778114709283540307425)
  ·
    refine ⟨11107333586031962655230569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14809778114709283540307425 11107333586031962655230569)
    ·
      refine ⟨8330500189523971991422927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11107333586031962655230569 8330500189523971991422927)
      ·
        refine ⟨12495750284285957987134391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8330500189523971991422927 12495750284285957987134391)
        ·
          refine ⟨18743625426428936980701587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12495750284285957987134391 18743625426428936980701587)
          ·
            refine ⟨28115438139643405471052381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18743625426428936980701587 28115438139643405471052381)
            ·
              refine ⟨10543289302366277051644643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28115438139643405471052381 10543289302366277051644643)
              ·
                refine ⟨15814933953549415577466965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543289302366277051644643 15814933953549415577466965)
                ·
                  refine ⟨185331257268157213798441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15814933953549415577466965 185331257268157213798441)
                  ·
                    rfl

theorem cell23_3248382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_3248382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248382 prefixEnd_3248382 := by exact prefixLift 3248382
  have htrace : WordTrace (prefixWord ++ tailWord_3248382) baseStart_3248382 baseEnd_3248382 := by
    simpa [prefixWord, tailWord_3248382, baseEnd_3248382] using wordTrace_append hprefix tailTrace_3248382
  have hstable : (prefixWord ++ tailWord_3248382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248382).length < 2 ^ (prefixWord ++ tailWord_3248382).sum := by decide
  have hdescent : baseEnd_3248382 < baseStart_3248382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248385 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3248385 : Nat := 118140960795 + 3248385 * 2 ^ 59
def prefixEnd_3248385 : Nat := 4983230072969 + 3 ^ 40 * 3248385 * 2
def baseEnd_3248385 : Nat := 1667982855855378412448455

theorem tailTrace_3248385 : CollatzResearch.WordTrace tailWord_3248385 prefixEnd_3248385 1667982855855378412448455 := by
  unfold tailWord_3248385
  simp only [CollatzResearch.WordTrace]
  refine ⟨118478334336663399834818609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78985556224442266556545739 118478334336663399834818609)
  ·
    refine ⟨88858750752497549876113957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118478334336663399834818609 88858750752497549876113957)
    ·
      refine ⟨16661015766093290601771367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88858750752497549876113957 16661015766093290601771367)
      ·
        refine ⟨24991523649139935902657051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16661015766093290601771367 24991523649139935902657051)
        ·
          refine ⟨37487285473709903853985577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24991523649139935902657051 37487285473709903853985577)
          ·
            refine ⟨28115464105282427890489183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37487285473709903853985577 28115464105282427890489183)
            ·
              refine ⟨42173196157923641835733775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28115464105282427890489183 42173196157923641835733775)
              ·
                refine ⟨63259794236885462753600663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42173196157923641835733775 63259794236885462753600663)
                ·
                  refine ⟨94889691355328194130400995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63259794236885462753600663 94889691355328194130400995)
                  ·
                    refine ⟨142334537032992291195601493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94889691355328194130400995 142334537032992291195601493)
                    ·
                      refine ⟨1667982855855378412448455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 142334537032992291195601493 1667982855855378412448455)
                      ·
                        rfl

theorem cell23_3248385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3248385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248385 prefixEnd_3248385 := by exact prefixLift 3248385
  have htrace : WordTrace (prefixWord ++ tailWord_3248385) baseStart_3248385 baseEnd_3248385 := by
    simpa [prefixWord, tailWord_3248385, baseEnd_3248385] using wordTrace_append hprefix tailTrace_3248385
  have hstable : (prefixWord ++ tailWord_3248385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248385).length < 2 ^ (prefixWord ++ tailWord_3248385).sum := by decide
  have hdescent : baseEnd_3248385 < baseStart_3248385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248386 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_3248386 : Nat := 118140960795 + 3248386 * 2 ^ 59
def prefixEnd_3248386 : Nat := 4983230072969 + 3 ^ 40 * 3248386 * 2
def baseEnd_3248386 : Nat := 555994456445344302845317

theorem tailTrace_3248386 : CollatzResearch.WordTrace tailWord_3248386 prefixEnd_3248386 555994456445344302845317 := by
  unfold tailWord_3248386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29619592702414944251401253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78985580539773184670403341 29619592702414944251401253)
  ·
    refine ⟨5553673631702802047137735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29619592702414944251401253 5553673631702802047137735)
    ·
      refine ⟨8330510447554203070706603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5553673631702802047137735 8330510447554203070706603)
      ·
        refine ⟨12495765671331304606059905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8330510447554203070706603 12495765671331304606059905)
        ·
          refine ⟨9371824253498478454544929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12495765671331304606059905 9371824253498478454544929)
          ·
            refine ⟨7028868190123858840908697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9371824253498478454544929 7028868190123858840908697)
            ·
              refine ⟨5271651142592894130681523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7028868190123858840908697 5271651142592894130681523)
              ·
                refine ⟨7907476713889341196022285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271651142592894130681523 7907476713889341196022285)
                ·
                  refine ⟨2965303767708502948508357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7907476713889341196022285 2965303767708502948508357)
                  ·
                    refine ⟨555994456445344302845317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965303767708502948508357 555994456445344302845317)
                    ·
                      rfl

theorem cell23_3248386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_3248386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248386 prefixEnd_3248386 := by exact prefixLift 3248386
  have htrace : WordTrace (prefixWord ++ tailWord_3248386) baseStart_3248386 baseEnd_3248386 := by
    simpa [prefixWord, tailWord_3248386, baseEnd_3248386] using wordTrace_append hprefix tailTrace_3248386
  have hstable : (prefixWord ++ tailWord_3248386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248386).length < 2 ^ (prefixWord ++ tailWord_3248386).sum := by decide
  have hdescent : baseEnd_3248386 < baseStart_3248386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248405 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 7]
def baseStart_3248405 : Nat := 118140960795 + 3248405 * 2 ^ 59
def prefixEnd_3248405 : Nat := 4983230072969 + 3 ^ 40 * 3248405 * 2
def baseEnd_3248405 : Nat := 1667993125468468334198363

theorem tailTrace_3248405 : CollatzResearch.WordTrace tailWord_3248405 prefixEnd_3248405 1667993125468468334198363 := by
  unfold tailWord_3248405
  simp only [CollatzResearch.WordTrace]
  refine ⟨118479063796590943250546669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78986042531060628833697779 118479063796590943250546669)
  ·
    refine ⟨44429648923721603718955001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118479063796590943250546669 44429648923721603718955001)
    ·
      refine ⟨33322236692791202789216251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44429648923721603718955001 33322236692791202789216251)
      ·
        refine ⟨49983355039186804183824377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33322236692791202789216251 49983355039186804183824377)
        ·
          refine ⟨37487516279390103137868283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49983355039186804183824377 37487516279390103137868283)
          ·
            refine ⟨56231274419085154706802425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37487516279390103137868283 56231274419085154706802425)
            ·
              refine ⟨42173455814313866030101819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56231274419085154706802425 42173455814313866030101819)
              ·
                refine ⟨63260183721470799045152729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42173455814313866030101819 63260183721470799045152729)
                ·
                  refine ⟨47445137791103099283864547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63260183721470799045152729 47445137791103099283864547)
                  ·
                    refine ⟨71167706686654648925796821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47445137791103099283864547 71167706686654648925796821)
                    ·
                      refine ⟨1667993125468468334198363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71167706686654648925796821 1667993125468468334198363)
                      ·
                        rfl

theorem cell23_3248405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_3248405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248405 prefixEnd_3248405 := by exact prefixLift 3248405
  have htrace : WordTrace (prefixWord ++ tailWord_3248405) baseStart_3248405 baseEnd_3248405 := by
    simpa [prefixWord, tailWord_3248405, baseEnd_3248405] using wordTrace_append hprefix tailTrace_3248405
  have hstable : (prefixWord ++ tailWord_3248405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248405).length < 2 ^ (prefixWord ++ tailWord_3248405).sum := by decide
  have hdescent : baseEnd_3248405 < baseStart_3248405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248419 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 2, 3, 2]
def baseStart_3248419 : Nat := 118140960795 + 3248419 * 2 ^ 59
def prefixEnd_3248419 : Nat := 4983230072969 + 3 ^ 40 * 3248419 * 2
def baseEnd_3248419 : Nat := 1668000314197631279423299

theorem tailTrace_3248419 : CollatzResearch.WordTrace tailWord_3248419 prefixEnd_3248419 1668000314197631279423299 := by
  unfold tailWord_3248419
  simp only [CollatzResearch.WordTrace]
  refine ⟨118479574418540223641556311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78986382945693482427704207 118479574418540223641556311)
  ·
    refine ⟨177719361627810335462334467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118479574418540223641556311 177719361627810335462334467)
    ·
      refine ⟨266579042441715503193501701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177719361627810335462334467 266579042441715503193501701)
      ·
        refine ⟨49983570457821656848781569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266579042441715503193501701 49983570457821656848781569)
        ·
          refine ⟨37487677843366242636586177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49983570457821656848781569 37487677843366242636586177)
          ·
            refine ⟨28115758382524681977439633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37487677843366242636586177 28115758382524681977439633)
            ·
              refine ⟨21086818786893511483079725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28115758382524681977439633 21086818786893511483079725)
              ·
                refine ⟨7907557045085066806154897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21086818786893511483079725 7907557045085066806154897)
                ·
                  refine ⟨5930667783813800104616173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7907557045085066806154897 5930667783813800104616173)
                  ·
                    refine ⟨2224000418930175039231065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5930667783813800104616173 2224000418930175039231065)
                    ·
                      refine ⟨1668000314197631279423299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224000418930175039231065 1668000314197631279423299)
                      ·
                        rfl

theorem cell23_3248419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 3, 2].length) (baseStart_3248419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248419 prefixEnd_3248419 := by exact prefixLift 3248419
  have htrace : WordTrace (prefixWord ++ tailWord_3248419) baseStart_3248419 baseEnd_3248419 := by
    simpa [prefixWord, tailWord_3248419, baseEnd_3248419] using wordTrace_append hprefix tailTrace_3248419
  have hstable : (prefixWord ++ tailWord_3248419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248419).length < 2 ^ (prefixWord ++ tailWord_3248419).sum := by decide
  have hdescent : baseEnd_3248419 < baseStart_3248419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248436 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 4, 3, 2]
def baseStart_3248436 : Nat := 118140960795 + 3248436 * 2 ^ 59
def prefixEnd_3248436 : Nat := 4983230072969 + 3 ^ 40 * 3248436 * 2
def baseEnd_3248436 : Nat := 1668009043368757712910721

theorem tailTrace_3248436 : CollatzResearch.WordTrace tailWord_3248436 prefixEnd_3248436 1668009043368757712910721 := by
  unfold tailWord_3248436
  simp only [CollatzResearch.WordTrace]
  refine ⟨59240097229739317772462581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78986796306319090363283441 59240097229739317772462581)
  ·
    refine ⟨5553759115288061041168367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59240097229739317772462581 5553759115288061041168367)
    ·
      refine ⟨8330638672932091561752551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5553759115288061041168367 8330638672932091561752551)
      ·
        refine ⟨12495958009398137342628827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8330638672932091561752551 12495958009398137342628827)
        ·
          refine ⟨18743937014097206013943241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12495958009398137342628827 18743937014097206013943241)
          ·
            refine ⟨14057952760572904510457431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18743937014097206013943241 14057952760572904510457431)
            ·
              refine ⟨21086929140859356765686147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14057952760572904510457431 21086929140859356765686147)
              ·
                refine ⟨31630393711289035148529221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21086929140859356765686147 31630393711289035148529221)
                ·
                  refine ⟨5930698820866694090349229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31630393711289035148529221 5930698820866694090349229)
                  ·
                    refine ⟨2224012057825010283880961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5930698820866694090349229 2224012057825010283880961)
                    ·
                      refine ⟨1668009043368757712910721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224012057825010283880961 1668009043368757712910721)
                      ·
                        rfl

theorem cell23_3248436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_3248436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248436 prefixEnd_3248436 := by exact prefixLift 3248436
  have htrace : WordTrace (prefixWord ++ tailWord_3248436) baseStart_3248436 baseEnd_3248436 := by
    simpa [prefixWord, tailWord_3248436, baseEnd_3248436] using wordTrace_append hprefix tailTrace_3248436
  have hstable : (prefixWord ++ tailWord_3248436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248436).length < 2 ^ (prefixWord ++ tailWord_3248436).sum := by decide
  have hdescent : baseEnd_3248436 < baseStart_3248436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248466 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_3248466 : Nat := 118140960795 + 3248466 * 2 ^ 59
def prefixEnd_3248466 : Nat := 4983230072969 + 3 ^ 40 * 3248466 * 2
def baseEnd_3248466 : Nat := 1668024447788392595535583

theorem tailTrace_3248466 : CollatzResearch.WordTrace tailWord_3248466 prefixEnd_3248466 1668024447788392595535583 := by
  unfold tailWord_3248466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29620322162342487667129313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78987525766246633779011501 29620322162342487667129313)
  ·
    refine ⟨22215241621756865750346985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29620322162342487667129313 22215241621756865750346985)
    ·
      refine ⟨16661431216317649312760239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22215241621756865750346985 16661431216317649312760239)
      ·
        refine ⟨24992146824476473969140359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16661431216317649312760239 24992146824476473969140359)
        ·
          refine ⟨37488220236714710953710539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24992146824476473969140359 37488220236714710953710539)
          ·
            refine ⟨56232330355072066430565809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37488220236714710953710539 56232330355072066430565809)
            ·
              refine ⟨42174247766304049822924357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56232330355072066430565809 42174247766304049822924357)
              ·
                refine ⟨7907671456182009341798317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42174247766304049822924357 7907671456182009341798317)
                ·
                  refine ⟨2965376796068253503174369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7907671456182009341798317 2965376796068253503174369)
                  ·
                    refine ⟨2224032597051190127380777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965376796068253503174369 2224032597051190127380777)
                    ·
                      refine ⟨1668024447788392595535583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224032597051190127380777 1668024447788392595535583)
                      ·
                        rfl

theorem cell23_3248466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_3248466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248466 prefixEnd_3248466 := by exact prefixLift 3248466
  have htrace : WordTrace (prefixWord ++ tailWord_3248466) baseStart_3248466 baseEnd_3248466 := by
    simpa [prefixWord, tailWord_3248466, baseEnd_3248466] using wordTrace_append hprefix tailTrace_3248466
  have hstable : (prefixWord ++ tailWord_3248466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248466).length < 2 ^ (prefixWord ++ tailWord_3248466).sum := by decide
  have hdescent : baseEnd_3248466 < baseStart_3248466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248476 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3248476 : Nat := 118140960795 + 3248476 * 2 ^ 59
def prefixEnd_3248476 : Nat := 4983230072969 + 3 ^ 40 * 3248476 * 2
def baseEnd_3248476 : Nat := 556009860864979185470179

theorem tailTrace_3248476 : CollatzResearch.WordTrace tailWord_3248476 prefixEnd_3248476 556009860864979185470179 := by
  unfold tailWord_3248476
  simp only [CollatzResearch.WordTrace]
  refine ⟨59240826689666861188190641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78987768919555814917587521 59240826689666861188190641)
  ·
    refine ⟨44430620017250145891142981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59240826689666861188190641 44430620017250145891142981)
    ·
      refine ⟨8330741253234402354589309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44430620017250145891142981 8330741253234402354589309)
      ·
        refine ⟨3124027969962900882970991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8330741253234402354589309 3124027969962900882970991)
        ·
          refine ⟨4686041954944351324456487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124027969962900882970991 4686041954944351324456487)
          ·
            refine ⟨7029062932416526986684731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686041954944351324456487 7029062932416526986684731)
            ·
              refine ⟨10543594398624790480027097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029062932416526986684731 10543594398624790480027097)
              ·
                refine ⟨7907695798968592860020323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10543594398624790480027097 7907695798968592860020323)
                ·
                  refine ⟨11861543698452889290030485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907695798968592860020323 11861543698452889290030485)
                  ·
                    refine ⟨556009860864979185470179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11861543698452889290030485 556009860864979185470179)
                    ·
                      rfl

theorem cell23_3248476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3248476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248476 prefixEnd_3248476 := by exact prefixLift 3248476
  have htrace : WordTrace (prefixWord ++ tailWord_3248476) baseStart_3248476 baseEnd_3248476 := by
    simpa [prefixWord, tailWord_3248476, baseEnd_3248476] using wordTrace_append hprefix tailTrace_3248476
  have hstable : (prefixWord ++ tailWord_3248476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248476).length < 2 ^ (prefixWord ++ tailWord_3248476).sum := by decide
  have hdescent : baseEnd_3248476 < baseStart_3248476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248483 : List Nat := [1, 1, 1, 5, 2, 1, 2, 5, 1, 2, 2]
def baseStart_3248483 : Nat := 118140960795 + 3248483 * 2 ^ 59
def prefixEnd_3248483 : Nat := 4983230072969 + 3 ^ 40 * 3248483 * 2
def baseEnd_3248483 : Nat := 1668033176959519029023005

theorem tailTrace_3248483 : CollatzResearch.WordTrace tailWord_3248483 prefixEnd_3248483 1668033176959519029023005 := by
  unfold tailWord_3248483
  simp only [CollatzResearch.WordTrace]
  refine ⟨118481908690308362571886103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78987939126872241714590735 118481908690308362571886103)
  ·
    refine ⟨177722863035462543857829155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118481908690308362571886103 177722863035462543857829155)
    ·
      refine ⟨266584294553193815786743733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177722863035462543857829155 266584294553193815786743733)
      ·
        refine ⟨24992277614361920230007225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266584294553193815786743733 24992277614361920230007225)
        ·
          refine ⟨18744208210771440172505419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24992277614361920230007225 18744208210771440172505419)
          ·
            refine ⟨28116312316157160258758129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18744208210771440172505419 28116312316157160258758129)
            ·
              refine ⟨21087234237117870194068597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28116312316157160258758129 21087234237117870194068597)
              ·
                refine ⟨1976928209729800330693931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21087234237117870194068597 1976928209729800330693931)
                ·
                  refine ⟨2965392314594700496040897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1976928209729800330693931 2965392314594700496040897)
                  ·
                    refine ⟨2224044235946025372030673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965392314594700496040897 2224044235946025372030673)
                    ·
                      refine ⟨1668033176959519029023005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224044235946025372030673 1668033176959519029023005)
                      ·
                        rfl

theorem cell23_3248483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_3248483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248483 prefixEnd_3248483 := by exact prefixLift 3248483
  have htrace : WordTrace (prefixWord ++ tailWord_3248483) baseStart_3248483 baseEnd_3248483 := by
    simpa [prefixWord, tailWord_3248483, baseEnd_3248483] using wordTrace_append hprefix tailTrace_3248483
  have hstable : (prefixWord ++ tailWord_3248483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248483).length < 2 ^ (prefixWord ++ tailWord_3248483).sum := by decide
  have hdescent : baseEnd_3248483 < baseStart_3248483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248516 : List Nat := [2, 3, 2, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_3248516 : Nat := 118140960795 + 3248516 * 2 ^ 59
def prefixEnd_3248516 : Nat := 4983230072969 + 3 ^ 40 * 3248516 * 2
def baseEnd_3248516 : Nat := 1668050121821117399910353

theorem tailTrace_3248516 : CollatzResearch.WordTrace tailWord_3248516 prefixEnd_3248516 1668050121821117399910353 := by
  unfold tailWord_3248516
  simp only [CollatzResearch.WordTrace]
  refine ⟨59241556149594404603918701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78988741532792539471891601 59241556149594404603918701)
  ·
    refine ⟨22215583556097901726469513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59241556149594404603918701 22215583556097901726469513)
    ·
      refine ⟨16661687667073426294852135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22215583556097901726469513 16661687667073426294852135)
      ·
        refine ⟨24992531500610139442278203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16661687667073426294852135 24992531500610139442278203)
        ·
          refine ⟨37488797250915209163417305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24992531500610139442278203 37488797250915209163417305)
          ·
            refine ⟨28116597938186406872562979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37488797250915209163417305 28116597938186406872562979)
            ·
              refine ⟨42174896907279610308844469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28116597938186406872562979 42174896907279610308844469)
              ·
                refine ⟨3953896585057463466454169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42174896907279610308844469 3953896585057463466454169)
                ·
                  refine ⟨2965422438793097599840627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3953896585057463466454169 2965422438793097599840627)
                  ·
                    refine ⟨4448133658189646399760941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2965422438793097599840627 4448133658189646399760941)
                    ·
                      refine ⟨1668050121821117399910353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4448133658189646399760941 1668050121821117399910353)
                      ·
                        rfl

theorem cell23_3248516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_3248516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248516 prefixEnd_3248516 := by exact prefixLift 3248516
  have htrace : WordTrace (prefixWord ++ tailWord_3248516) baseStart_3248516 baseEnd_3248516 := by
    simpa [prefixWord, tailWord_3248516, baseEnd_3248516] using wordTrace_append hprefix tailTrace_3248516
  have hstable : (prefixWord ++ tailWord_3248516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248516).length < 2 ^ (prefixWord ++ tailWord_3248516).sum := by decide
  have hdescent : baseEnd_3248516 < baseStart_3248516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248534 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3248534 : Nat := 118140960795 + 3248534 * 2 ^ 59
def prefixEnd_3248534 : Nat := 4983230072969 + 3 ^ 40 * 3248534 * 2
def baseEnd_3248534 : Nat := 1668059364472898329485271

theorem tailTrace_3248534 : CollatzResearch.WordTrace tailWord_3248534 prefixEnd_3248534 1668059364472898329485271 := by
  unfold tailWord_3248534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405235550820224892624541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78989179208749065521328437 7405235550820224892624541)
  ·
    refine ⟨2776963331557584334734203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7405235550820224892624541 2776963331557584334734203)
    ·
      refine ⟨4165444997336376502101305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2776963331557584334734203 4165444997336376502101305)
      ·
        refine ⟨3124083748002282376575979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4165444997336376502101305 3124083748002282376575979)
        ·
          refine ⟨4686125622003423564863969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124083748002282376575979 4686125622003423564863969)
          ·
            refine ⟨3514594216502567673647977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4686125622003423564863969 3514594216502567673647977)
            ·
              refine ⟨2635945662376925755235983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3514594216502567673647977 2635945662376925755235983)
              ·
                refine ⟨3953918493565388632853975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2635945662376925755235983 3953918493565388632853975)
                ·
                  refine ⟨5930877740348082949280963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3953918493565388632853975 5930877740348082949280963)
                  ·
                    refine ⟨8896316610522124423921445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5930877740348082949280963 8896316610522124423921445)
                    ·
                      refine ⟨1668059364472898329485271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8896316610522124423921445 1668059364472898329485271)
                      ·
                        rfl

theorem cell23_3248534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3248534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248534 prefixEnd_3248534 := by exact prefixLift 3248534
  have htrace : WordTrace (prefixWord ++ tailWord_3248534) baseStart_3248534 baseEnd_3248534 := by
    simpa [prefixWord, tailWord_3248534, baseEnd_3248534] using wordTrace_append hprefix tailTrace_3248534
  have hstable : (prefixWord ++ tailWord_3248534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248534).length < 2 ^ (prefixWord ++ tailWord_3248534).sum := by decide
  have hdescent : baseEnd_3248534 < baseStart_3248534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248569 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3248569 : Nat := 118140960795 + 3248569 * 2 ^ 59
def prefixEnd_3248569 : Nat := 4983230072969 + 3 ^ 40 * 3248569 * 2
def baseEnd_3248569 : Nat := 1668077336295805692547609

theorem tailTrace_3248569 : CollatzResearch.WordTrace tailWord_3248569 prefixEnd_3248569 1668077336295805692547609 := by
  unfold tailWord_3248569
  simp only [CollatzResearch.WordTrace]
  refine ⟨118485045367996799259516761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78990030245331199506344507 118485045367996799259516761)
  ·
    refine ⟨88863784025997599444637571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118485045367996799259516761 88863784025997599444637571)
    ·
      refine ⟨133295676038996399166956357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88863784025997599444637571 133295676038996399166956357)
      ·
        refine ⟨24992939257311824843804317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133295676038996399166956357 24992939257311824843804317)
        ·
          refine ⟨9372352221491934316426619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24992939257311824843804317 9372352221491934316426619)
          ·
            refine ⟨14058528332237901474639929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9372352221491934316426619 14058528332237901474639929)
            ·
              refine ⟨10543896249178426105979947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14058528332237901474639929 10543896249178426105979947)
              ·
                refine ⟨15815844373767639158969921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10543896249178426105979947 15815844373767639158969921)
                ·
                  refine ⟨11861883280325729369227441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15815844373767639158969921 11861883280325729369227441)
                  ·
                    refine ⟨8896412460244297026920581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11861883280325729369227441 8896412460244297026920581)
                    ·
                      refine ⟨1668077336295805692547609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8896412460244297026920581 1668077336295805692547609)
                      ·
                        rfl

theorem cell23_3248569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3248569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248569 prefixEnd_3248569 := by exact prefixLift 3248569
  have htrace : WordTrace (prefixWord ++ tailWord_3248569) baseStart_3248569 baseEnd_3248569 := by
    simpa [prefixWord, tailWord_3248569, baseEnd_3248569] using wordTrace_append hprefix tailTrace_3248569
  have hstable : (prefixWord ++ tailWord_3248569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248569).length < 2 ^ (prefixWord ++ tailWord_3248569).sum := by decide
  have hdescent : baseEnd_3248569 < baseStart_3248569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248573 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 1, 4, 2]
def baseStart_3248573 : Nat := 118140960795 + 3248573 * 2 ^ 59
def prefixEnd_3248573 : Nat := 4983230072969 + 3 ^ 40 * 3248573 * 2
def baseEnd_3248573 : Nat := 1668079390218423676897591

theorem tailTrace_3248573 : CollatzResearch.WordTrace tailWord_3248573 prefixEnd_3248573 1668079390218423676897591 := by
  unfold tailWord_3248573
  simp only [CollatzResearch.WordTrace]
  refine ⟨118485191259982307942662373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78990127506654871961774915 118485191259982307942662373)
  ·
    refine ⟨22215973361246682739249195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118485191259982307942662373 22215973361246682739249195)
    ·
      refine ⟨33323960041870024108873793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22215973361246682739249195 33323960041870024108873793)
      ·
        refine ⟨24992970031402518081655345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33323960041870024108873793 24992970031402518081655345)
        ·
          refine ⟨18744727523551888561241509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24992970031402518081655345 18744727523551888561241509)
          ·
            refine ⟨3514636410665979105232783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18744727523551888561241509 3514636410665979105232783)
            ·
              refine ⟨5271954615998968657849175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514636410665979105232783 5271954615998968657849175)
              ·
                refine ⟨7907931923998452986773763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5271954615998968657849175 7907931923998452986773763)
                ·
                  refine ⟨11861897885997679480160645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7907931923998452986773763 11861897885997679480160645)
                  ·
                    refine ⟨2224105853624564902530121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11861897885997679480160645 2224105853624564902530121)
                    ·
                      refine ⟨1668079390218423676897591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224105853624564902530121 1668079390218423676897591)
                      ·
                        rfl

theorem cell23_3248573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_3248573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248573 prefixEnd_3248573 := by exact prefixLift 3248573
  have htrace : WordTrace (prefixWord ++ tailWord_3248573) baseStart_3248573 baseEnd_3248573 := by
    simpa [prefixWord, tailWord_3248573, baseEnd_3248573] using wordTrace_append hprefix tailTrace_3248573
  have hstable : (prefixWord ++ tailWord_3248573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248573).length < 2 ^ (prefixWord ++ tailWord_3248573).sum := by decide
  have hdescent : baseEnd_3248573 < baseStart_3248573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248599 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 7, 2]
def baseStart_3248599 : Nat := 118140960795 + 3248599 * 2 ^ 59
def prefixEnd_3248599 : Nat := 4983230072969 + 3 ^ 40 * 3248599 * 2
def baseEnd_3248599 : Nat := 1668092740715440575172471

theorem tailTrace_3248599 : CollatzResearch.WordTrace tailWord_3248599 prefixEnd_3248599 1668092740715440575172471 := by
  unfold tailWord_3248599
  simp only [CollatzResearch.WordTrace]
  refine ⟨118486139557888114383108851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78990759705258742922072567 118486139557888114383108851)
  ·
    refine ⟨177729209336832171574663277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118486139557888114383108851 177729209336832171574663277)
    ·
      refine ⟨66648453501312064340498729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177729209336832171574663277 66648453501312064340498729)
      ·
        refine ⟨49986340125984048255374047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66648453501312064340498729 49986340125984048255374047)
        ·
          refine ⟨74979510188976072383061071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49986340125984048255374047 74979510188976072383061071)
          ·
            refine ⟨112469265283464108574591607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74979510188976072383061071 112469265283464108574591607)
            ·
              refine ⟨168703897925196162861887411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112469265283464108574591607 168703897925196162861887411)
              ·
                refine ⟨253055846887794244292831117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168703897925196162861887411 253055846887794244292831117)
                ·
                  refine ⟨94895942582922841609811669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253055846887794244292831117 94895942582922841609811669)
                  ·
                    refine ⟨2224123654287254100229961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 94895942582922841609811669 2224123654287254100229961)
                    ·
                      refine ⟨1668092740715440575172471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224123654287254100229961 1668092740715440575172471)
                      ·
                        rfl

theorem cell23_3248599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_3248599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248599 prefixEnd_3248599 := by exact prefixLift 3248599
  have htrace : WordTrace (prefixWord ++ tailWord_3248599) baseStart_3248599 baseEnd_3248599 := by
    simpa [prefixWord, tailWord_3248599, baseEnd_3248599] using wordTrace_append hprefix tailTrace_3248599
  have hstable : (prefixWord ++ tailWord_3248599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248599).length < 2 ^ (prefixWord ++ tailWord_3248599).sum := by decide
  have hdescent : baseEnd_3248599 < baseStart_3248599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248609 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3248609 : Nat := 118140960795 + 3248609 * 2 ^ 59
def prefixEnd_3248609 : Nat := 4983230072969 + 3 ^ 40 * 3248609 * 2
def baseEnd_3248609 : Nat := 556032625173995178682475

theorem tailTrace_3248609 : CollatzResearch.WordTrace tailWord_3248609 prefixEnd_3248609 556032625173995178682475 := by
  unfold tailWord_3248609
  simp only [CollatzResearch.WordTrace]
  refine ⟨118486504287851886090972881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78991002858567924060648587 118486504287851886090972881)
  ·
    refine ⟨88864878215888914568229661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118486504287851886090972881 88864878215888914568229661)
    ·
      refine ⟨33324329330958342963086123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88864878215888914568229661 33324329330958342963086123)
      ·
        refine ⟨49986493996437514444629185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33324329330958342963086123 49986493996437514444629185)
        ·
          refine ⟨37489870497328135833471889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49986493996437514444629185 37489870497328135833471889)
          ·
            refine ⟨28117402872996101875103917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37489870497328135833471889 28117402872996101875103917)
            ·
              refine ⟨10544026077373538203163969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28117402872996101875103917 10544026077373538203163969)
              ·
                refine ⟨7908019558030153652372977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10544026077373538203163969 7908019558030153652372977)
                ·
                  refine ⟨5931014668522615239279733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7908019558030153652372977 5931014668522615239279733)
                  ·
                    refine ⟨556032625173995178682475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5931014668522615239279733 556032625173995178682475)
                    ·
                      rfl

theorem cell23_3248609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3248609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248609 prefixEnd_3248609 := by exact prefixLift 3248609
  have htrace : WordTrace (prefixWord ++ tailWord_3248609) baseStart_3248609 baseEnd_3248609 := by
    simpa [prefixWord, tailWord_3248609, baseEnd_3248609] using wordTrace_append hprefix tailTrace_3248609
  have hstable : (prefixWord ++ tailWord_3248609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248609).length < 2 ^ (prefixWord ++ tailWord_3248609).sum := by decide
  have hdescent : baseEnd_3248609 < baseStart_3248609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248612 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_3248612 : Nat := 118140960795 + 3248612 * 2 ^ 59
def prefixEnd_3248612 : Nat := 4983230072969 + 3 ^ 40 * 3248612 * 2
def baseEnd_3248612 : Nat := 1668099415963949024309911

theorem tailTrace_3248612 : CollatzResearch.WordTrace tailWord_3248612 prefixEnd_3248612 1668099415963949024309911 := by
  unfold tailWord_3248612
  simp only [CollatzResearch.WordTrace]
  refine ⟨59243306853420508801666045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78991075804560678402221393 59243306853420508801666045)
  ·
    refine ⟨22216240070032690800624767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59243306853420508801666045 22216240070032690800624767)
    ·
      refine ⟨33324360105049036200937151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22216240070032690800624767 33324360105049036200937151)
      ·
        refine ⟨49986540157573554301405727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33324360105049036200937151 49986540157573554301405727)
        ·
          refine ⟨74979810236360331452108591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49986540157573554301405727 74979810236360331452108591)
          ·
            refine ⟨112469715354540497178162887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74979810236360331452108591 112469715354540497178162887)
            ·
              refine ⟨168704573031810745767244331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112469715354540497178162887 168704573031810745767244331)
              ·
                refine ⟨253056859547716118650866497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168704573031810745767244331 253056859547716118650866497)
                ·
                  refine ⟨189792644660787088988149873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253056859547716118650866497 189792644660787088988149873)
                  ·
                    refine ⟨142344483495590316741112405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189792644660787088988149873 142344483495590316741112405)
                    ·
                      refine ⟨1668099415963949024309911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 142344483495590316741112405 1668099415963949024309911)
                      ·
                        rfl

theorem cell23_3248612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_3248612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248612 prefixEnd_3248612 := by exact prefixLift 3248612
  have htrace : WordTrace (prefixWord ++ tailWord_3248612) baseStart_3248612 baseEnd_3248612 := by
    simpa [prefixWord, tailWord_3248612, baseEnd_3248612] using wordTrace_append hprefix tailTrace_3248612
  have hstable : (prefixWord ++ tailWord_3248612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248612).length < 2 ^ (prefixWord ++ tailWord_3248612).sum := by decide
  have hdescent : baseEnd_3248612 < baseStart_3248612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248613 : List Nat := [1, 3, 1, 5, 3, 1, 1, 1, 7]
def baseStart_3248613 : Nat := 118140960795 + 3248613 * 2 ^ 59
def prefixEnd_3248613 : Nat := 4983230072969 + 3 ^ 40 * 3248613 * 2
def baseEnd_3248613 : Nat := 185344436604955946710823

theorem tailTrace_3248613 : CollatzResearch.WordTrace tailWord_3248613 prefixEnd_3248613 185344436604955946710823 := by
  unfold tailWord_3248613
  simp only [CollatzResearch.WordTrace]
  refine ⟨118486650179837394774118493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78991100119891596516078995 118486650179837394774118493)
  ·
    refine ⟨44432493817439023040294435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118486650179837394774118493 44432493817439023040294435)
    ·
      refine ⟨66648740726158534560441653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44432493817439023040294435 66648740726158534560441653)
      ·
        refine ⟨6248319443077362615041405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66648740726158534560441653 6248319443077362615041405)
        ·
          refine ⟨2343119791154010980640527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6248319443077362615041405 2343119791154010980640527)
          ·
            refine ⟨3514679686731016470960791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343119791154010980640527 3514679686731016470960791)
            ·
              refine ⟨5272019530096524706441187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3514679686731016470960791 5272019530096524706441187)
              ·
                refine ⟨7908029295144787059661781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5272019530096524706441187 7908029295144787059661781)
                ·
                  refine ⟨185344436604955946710823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7908029295144787059661781 185344436604955946710823)
                  ·
                    rfl

theorem cell23_3248613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 1, 7].length) (baseStart_3248613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248613 prefixEnd_3248613 := by exact prefixLift 3248613
  have htrace : WordTrace (prefixWord ++ tailWord_3248613) baseStart_3248613 baseEnd_3248613 := by
    simpa [prefixWord, tailWord_3248613, baseEnd_3248613] using wordTrace_append hprefix tailTrace_3248613
  have hstable : (prefixWord ++ tailWord_3248613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248613).length < 2 ^ (prefixWord ++ tailWord_3248613).sum := by decide
  have hdescent : baseEnd_3248613 < baseStart_3248613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248639 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 5, 4]
def baseStart_3248639 : Nat := 118140960795 + 3248639 * 2 ^ 59
def prefixEnd_3248639 : Nat := 4983230072969 + 3 ^ 40 * 3248639 * 2
def baseEnd_3248639 : Nat := 556037759980540139557429

theorem tailTrace_3248639 : CollatzResearch.WordTrace tailWord_3248639 prefixEnd_3248639 556037759980540139557429 := by
  unfold tailWord_3248639
  simp only [CollatzResearch.WordTrace]
  refine ⟨118487598477743201214564971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78991732318495467476376647 118487598477743201214564971)
  ·
    refine ⟨177731397716614801821847457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118487598477743201214564971 177731397716614801821847457)
    ·
      refine ⟨133298548287461101366385593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177731397716614801821847457 133298548287461101366385593)
      ·
        refine ⟨99973911215595826024789195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133298548287461101366385593 99973911215595826024789195)
        ·
          refine ⟨149960866823393739037183793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99973911215595826024789195 149960866823393739037183793)
          ·
            refine ⟨112470650117545304277887845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149960866823393739037183793 112470650117545304277887845)
            ·
              refine ⟨21088246897039744552103971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112470650117545304277887845 21088246897039744552103971)
              ·
                refine ⟨31632370345559616828155957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21088246897039744552103971 31632370345559616828155957)
                ·
                  refine ⟨2965534719896214077639621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31632370345559616828155957 2965534719896214077639621)
                  ·
                    refine ⟨556037759980540139557429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965534719896214077639621 556037759980540139557429)
                    ·
                      rfl

theorem cell23_3248639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_3248639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248639 prefixEnd_3248639 := by exact prefixLift 3248639
  have htrace : WordTrace (prefixWord ++ tailWord_3248639) baseStart_3248639 baseEnd_3248639 := by
    simpa [prefixWord, tailWord_3248639, baseEnd_3248639] using wordTrace_append hprefix tailTrace_3248639
  have hstable : (prefixWord ++ tailWord_3248639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248639).length < 2 ^ (prefixWord ++ tailWord_3248639).sum := by decide
  have hdescent : baseEnd_3248639 < baseStart_3248639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248653 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3248653 : Nat := 118140960795 + 3248653 * 2 ^ 59
def prefixEnd_3248653 : Nat := 4983230072969 + 3 ^ 40 * 3248653 * 2
def baseEnd_3248653 : Nat := 1668120468670783363897223

theorem tailTrace_3248653 : CollatzResearch.WordTrace tailWord_3248653 prefixEnd_3248653 1668120468670783363897223 := by
  unfold tailWord_3248653
  simp only [CollatzResearch.WordTrace]
  refine ⟨118488109099692481605574613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78992072733128321070383075 118488109099692481605574613)
  ·
    refine ⟨2777065057024042537630655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 118488109099692481605574613 2777065057024042537630655)
    ·
      refine ⟨4165597585536063806445983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2777065057024042537630655 4165597585536063806445983)
      ·
        refine ⟨6248396378304095709668975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165597585536063806445983 6248396378304095709668975)
        ·
          refine ⟨9372594567456143564503463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6248396378304095709668975 9372594567456143564503463)
          ·
            refine ⟨14058891851184215346755195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9372594567456143564503463 14058891851184215346755195)
            ·
              refine ⟨21088337776776323020132793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14058891851184215346755195 21088337776776323020132793)
              ·
                refine ⟨15816253332582242265099595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21088337776776323020132793 15816253332582242265099595)
                ·
                  refine ⟨23724379998873363397649393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15816253332582242265099595 23724379998873363397649393)
                  ·
                    refine ⟨17793284999155022548237045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23724379998873363397649393 17793284999155022548237045)
                    ·
                      refine ⟨1668120468670783363897223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17793284999155022548237045 1668120468670783363897223)
                      ·
                        rfl

theorem cell23_3248653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3248653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248653 prefixEnd_3248653 := by exact prefixLift 3248653
  have htrace : WordTrace (prefixWord ++ tailWord_3248653) baseStart_3248653 baseEnd_3248653 := by
    simpa [prefixWord, tailWord_3248653, baseEnd_3248653] using wordTrace_append hprefix tailTrace_3248653
  have hstable : (prefixWord ++ tailWord_3248653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248653).length < 2 ^ (prefixWord ++ tailWord_3248653).sum := by decide
  have hdescent : baseEnd_3248653 < baseStart_3248653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248666 : List Nat := [3, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3]
def baseStart_3248666 : Nat := 118140960795 + 3248666 * 2 ^ 59
def prefixEnd_3248666 : Nat := 4983230072969 + 3 ^ 40 * 3248666 * 2
def baseEnd_3248666 : Nat := 1668127143919291813034663

theorem tailTrace_3248666 : CollatzResearch.WordTrace tailWord_3248666 prefixEnd_3248666 1668127143919291813034663 := by
  unfold tailWord_3248666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29622145812161346206449463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78992388832430256550531901 29622145812161346206449463)
  ·
    refine ⟨44433218718242019309674195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29622145812161346206449463 44433218718242019309674195)
    ·
      refine ⟨66649828077363028964511293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44433218718242019309674195 66649828077363028964511293)
      ·
        refine ⟨24993685529011135861691735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66649828077363028964511293 24993685529011135861691735)
        ·
          refine ⟨37490528293516703792537603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24993685529011135861691735 37490528293516703792537603)
          ·
            refine ⟨56235792440275055688806405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37490528293516703792537603 56235792440275055688806405)
            ·
              refine ⟨10544211082551572941651201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56235792440275055688806405 10544211082551572941651201)
              ·
                refine ⟨7908158311913679706238401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10544211082551572941651201 7908158311913679706238401)
                ·
                  refine ⟨5931118733935259779678801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7908158311913679706238401 5931118733935259779678801)
                  ·
                    refine ⟨4448339050451444834759101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5931118733935259779678801 4448339050451444834759101)
                    ·
                      refine ⟨1668127143919291813034663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4448339050451444834759101 1668127143919291813034663)
                      ·
                        rfl

theorem cell23_3248666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3].length) (baseStart_3248666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248666 prefixEnd_3248666 := by exact prefixLift 3248666
  have htrace : WordTrace (prefixWord ++ tailWord_3248666) baseStart_3248666 baseEnd_3248666 := by
    simpa [prefixWord, tailWord_3248666, baseEnd_3248666] using wordTrace_append hprefix tailTrace_3248666
  have hstable : (prefixWord ++ tailWord_3248666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248666).length < 2 ^ (prefixWord ++ tailWord_3248666).sum := by decide
  have hdescent : baseEnd_3248666 < baseStart_3248666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248673 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3248673 : Nat := 118140960795 + 3248673 * 2 ^ 59
def prefixEnd_3248673 : Nat := 4983230072969 + 3 ^ 40 * 3248673 * 2
def baseEnd_3248673 : Nat := 556043579427957761882377

theorem tailTrace_3248673 : CollatzResearch.WordTrace tailWord_3248673 prefixEnd_3248673 556043579427957761882377 := by
  unfold tailWord_3248673
  simp only [CollatzResearch.WordTrace]
  refine ⟨118488838559620025021302673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78992559039746683347535115 118488838559620025021302673)
  ·
    refine ⟨88866628919715018765977005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118488838559620025021302673 88866628919715018765977005)
    ·
      refine ⟨33324985844893132037241377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88866628919715018765977005 33324985844893132037241377)
      ·
        refine ⟨24993739383669849027931033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33324985844893132037241377 24993739383669849027931033)
        ·
          refine ⟨18745304537752386770948275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24993739383669849027931033 18745304537752386770948275)
          ·
            refine ⟨28117956806628580156422413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18745304537752386770948275 28117956806628580156422413)
            ·
              refine ⟨10544233802485717558658405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28117956806628580156422413 10544233802485717558658405)
              ·
                refine ⟨1977043837966072042248451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10544233802485717558658405 1977043837966072042248451)
                ·
                  refine ⟨2965565756949108063372677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977043837966072042248451 2965565756949108063372677)
                  ·
                    refine ⟨556043579427957761882377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965565756949108063372677 556043579427957761882377)
                    ·
                      rfl

theorem cell23_3248673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3248673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248673 prefixEnd_3248673 := by exact prefixLift 3248673
  have htrace : WordTrace (prefixWord ++ tailWord_3248673) baseStart_3248673 baseEnd_3248673 := by
    simpa [prefixWord, tailWord_3248673, baseEnd_3248673] using wordTrace_append hprefix tailTrace_3248673
  have hstable : (prefixWord ++ tailWord_3248673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248673).length < 2 ^ (prefixWord ++ tailWord_3248673).sum := by decide
  have hdescent : baseEnd_3248673 < baseStart_3248673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248716 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 1, 5]
def baseStart_3248716 : Nat := 118140960795 + 3248716 * 2 ^ 59
def prefixEnd_3248716 : Nat := 4983230072969 + 3 ^ 40 * 3248716 * 2
def baseEnd_3248716 : Nat := 556050939317338872469811

theorem tailTrace_3248716 : CollatzResearch.WordTrace tailWord_3248716 prefixEnd_3248716 556050939317338872469811 := by
  unfold tailWord_3248716
  simp only [CollatzResearch.WordTrace]
  refine ⟨59245203449232121682559001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78993604598976162243412001 59245203449232121682559001)
  ·
    refine ⟨44433902586924091261919251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59245203449232121682559001 44433902586924091261919251)
    ·
      refine ⟨66650853880386136892878877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44433902586924091261919251 66650853880386136892878877)
      ·
        refine ⟨24994070205144801334829579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66650853880386136892878877 24994070205144801334829579)
        ·
          refine ⟨37491105307717202002244369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24994070205144801334829579 37491105307717202002244369)
          ·
            refine ⟨28118328980787901501683277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37491105307717202002244369 28118328980787901501683277)
            ·
              refine ⟨10544373367795463063131229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28118328980787901501683277 10544373367795463063131229)
              ·
                refine ⟨3954140012923298648674211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10544373367795463063131229 3954140012923298648674211)
                ·
                  refine ⟨5931210019384947973011317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954140012923298648674211 5931210019384947973011317)
                  ·
                    refine ⟨556050939317338872469811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5931210019384947973011317 556050939317338872469811)
                    ·
                      rfl

theorem cell23_3248716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 5].length) (baseStart_3248716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248716 prefixEnd_3248716 := by exact prefixLift 3248716
  have htrace : WordTrace (prefixWord ++ tailWord_3248716) baseStart_3248716 baseEnd_3248716 := by
    simpa [prefixWord, tailWord_3248716, baseEnd_3248716] using wordTrace_append hprefix tailTrace_3248716
  have hstable : (prefixWord ++ tailWord_3248716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248716).length < 2 ^ (prefixWord ++ tailWord_3248716).sum := by decide
  have hdescent : baseEnd_3248716 < baseStart_3248716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248773 : List Nat := [1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 3]
def baseStart_3248773 : Nat := 118140960795 + 3248773 * 2 ^ 59
def prefixEnd_3248773 : Nat := 4983230072969 + 3 ^ 40 * 3248773 * 2
def baseEnd_3248773 : Nat := 1668182086349322894396671

theorem tailTrace_3248773 : CollatzResearch.WordTrace tailWord_3248773 prefixEnd_3248773 1668182086349322894396671 := by
  unfold tailWord_3248773
  simp only [CollatzResearch.WordTrace]
  refine ⟨118492485859257742099942973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78994990572838494733295315 118492485859257742099942973)
  ·
    refine ⟨44434682197221653287478615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118492485859257742099942973 44434682197221653287478615)
    ·
      refine ⟨66652023295832479931217923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44434682197221653287478615 66652023295832479931217923)
      ·
        refine ⟨99978034943748719896826885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66652023295832479931217923 99978034943748719896826885)
        ·
          refine ⟨18745881551952884980655041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99978034943748719896826885 18745881551952884980655041)
          ·
            refine ⟨14059411163964663735491281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18745881551952884980655041 14059411163964663735491281)
            ·
              refine ⟨10544558372973497801618461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14059411163964663735491281 10544558372973497801618461)
              ·
                refine ⟨3954209389865061675606923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10544558372973497801618461 3954209389865061675606923)
                ·
                  refine ⟨5931314084797592513410385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954209389865061675606923 5931314084797592513410385)
                  ·
                    refine ⟨4448485563598194385057789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5931314084797592513410385 4448485563598194385057789)
                    ·
                      refine ⟨1668182086349322894396671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4448485563598194385057789 1668182086349322894396671)
                      ·
                        rfl

theorem cell23_3248773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 2, 3].length) (baseStart_3248773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248773 prefixEnd_3248773 := by exact prefixLift 3248773
  have htrace : WordTrace (prefixWord ++ tailWord_3248773) baseStart_3248773 baseEnd_3248773 := by
    simpa [prefixWord, tailWord_3248773, baseEnd_3248773] using wordTrace_append hprefix tailTrace_3248773
  have hstable : (prefixWord ++ tailWord_3248773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248773).length < 2 ^ (prefixWord ++ tailWord_3248773).sum := by decide
  have hdescent : baseEnd_3248773 < baseStart_3248773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248838 : List Nat := [6, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_3248838 : Nat := 118140960795 + 3248838 * 2 ^ 59
def prefixEnd_3248838 : Nat := 4983230072969 + 3 ^ 40 * 3248838 * 2
def baseEnd_3248838 : Nat := 1668215462591865140083873

theorem tailTrace_3248838 : CollatzResearch.WordTrace tailWord_3248838 prefixEnd_3248838 1668215462591865140083873 := by
  unfold tailWord_3248838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702964268875695568783099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78996571069348172134039445 3702964268875695568783099)
  ·
    refine ⟨5554446403313543353174649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3702964268875695568783099 5554446403313543353174649)
    ·
      refine ⟨4165834802485157514880987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5554446403313543353174649 4165834802485157514880987)
      ·
        refine ⟨6248752203727736272321481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4165834802485157514880987 6248752203727736272321481)
        ·
          refine ⟨4686564152795802204241111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6248752203727736272321481 4686564152795802204241111)
          ·
            refine ⟨7029846229193703306361667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686564152795802204241111 7029846229193703306361667)
            ·
              refine ⟨10544769343790554959542501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7029846229193703306361667 10544769343790554959542501)
              ·
                refine ⟨1977144251960729054914219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10544769343790554959542501 1977144251960729054914219)
                ·
                  refine ⟨2965716377941093582371329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977144251960729054914219 2965716377941093582371329)
                  ·
                    refine ⟨2224287283455820186778497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965716377941093582371329 2224287283455820186778497)
                    ·
                      refine ⟨1668215462591865140083873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224287283455820186778497 1668215462591865140083873)
                      ·
                        rfl

theorem cell23_3248838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_3248838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248838 prefixEnd_3248838 := by exact prefixLift 3248838
  have htrace : WordTrace (prefixWord ++ tailWord_3248838) baseStart_3248838 baseEnd_3248838 := by
    simpa [prefixWord, tailWord_3248838, baseEnd_3248838] using wordTrace_append hprefix tailTrace_3248838
  have hstable : (prefixWord ++ tailWord_3248838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248838).length < 2 ^ (prefixWord ++ tailWord_3248838).sum := by decide
  have hdescent : baseEnd_3248838 < baseStart_3248838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248856 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3248856 : Nat := 118140960795 + 3248856 * 2 ^ 59
def prefixEnd_3248856 : Nat := 4983230072969 + 3 ^ 40 * 3248856 * 2
def baseEnd_3248856 : Nat := 1668224705243646069658789

theorem tailTrace_3248856 : CollatzResearch.WordTrace tailWord_3248856 prefixEnd_3248856 1668224705243646069658789 := by
  unfold tailWord_3248856
  simp only [CollatzResearch.WordTrace]
  refine ⟨59247756558978523637607211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78997008745304698183476281 59247756558978523637607211)
  ·
    refine ⟨88871634838467785456410817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59247756558978523637607211 88871634838467785456410817)
    ·
      refine ⟨66653726128850839092308113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88871634838467785456410817 66653726128850839092308113)
      ·
        refine ⟨49990294596638129319231085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66653726128850839092308113 49990294596638129319231085)
        ·
          refine ⟨18746360473739298494711657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49990294596638129319231085 18746360473739298494711657)
          ·
            refine ⟨14059770355304473871033743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18746360473739298494711657 14059770355304473871033743)
            ·
              refine ⟨21089655532956710806550615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14059770355304473871033743 21089655532956710806550615)
              ·
                refine ⟨31634483299435066209825923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21089655532956710806550615 31634483299435066209825923)
                ·
                  refine ⟨47451724949152599314738885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31634483299435066209825923 47451724949152599314738885)
                  ·
                    refine ⟨8897198427966112371513541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47451724949152599314738885 8897198427966112371513541)
                    ·
                      refine ⟨1668224705243646069658789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8897198427966112371513541 1668224705243646069658789)
                      ·
                        rfl

theorem cell23_3248856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3248856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248856 prefixEnd_3248856 := by exact prefixLift 3248856
  have htrace : WordTrace (prefixWord ++ tailWord_3248856) baseStart_3248856 baseEnd_3248856 := by
    simpa [prefixWord, tailWord_3248856, baseEnd_3248856] using wordTrace_append hprefix tailTrace_3248856
  have hstable : (prefixWord ++ tailWord_3248856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248856).length < 2 ^ (prefixWord ++ tailWord_3248856).sum := by decide
  have hdescent : baseEnd_3248856 < baseStart_3248856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248859 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9]
def baseStart_3248859 : Nat := 118140960795 + 3248859 * 2 ^ 59
def prefixEnd_3248859 : Nat := 4983230072969 + 3 ^ 40 * 3248859 * 2
def baseEnd_3248859 : Nat := 1668226245685609557921275

theorem tailTrace_3248859 : CollatzResearch.WordTrace tailWord_3248859 prefixEnd_3248859 1668226245685609557921275 := by
  unfold tailWord_3248859
  simp only [CollatzResearch.WordTrace]
  refine ⟨118495622536946178787573631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78997081691297452525049087 118495622536946178787573631)
  ·
    refine ⟨177743433805419268181360447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118495622536946178787573631 177743433805419268181360447)
    ·
      refine ⟨266615150708128902272040671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177743433805419268181360447 266615150708128902272040671)
      ·
        refine ⟨399922726062193353408061007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266615150708128902272040671 399922726062193353408061007)
        ·
          refine ⟨599884089093290030112091511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399922726062193353408061007 599884089093290030112091511)
          ·
            refine ⟨899826133639935045168137267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599884089093290030112091511 899826133639935045168137267)
            ·
              refine ⟨1349739200459902567752205901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899826133639935045168137267 1349739200459902567752205901)
              ·
                refine ⟨506152200172463462907077213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1349739200459902567752205901 506152200172463462907077213)
                ·
                  refine ⟨189807075064673798590153955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 506152200172463462907077213 189807075064673798590153955)
                  ·
                    refine ⟨284710612597010697885230933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189807075064673798590153955 284710612597010697885230933)
                    ·
                      refine ⟨1668226245685609557921275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 284710612597010697885230933 1668226245685609557921275)
                      ·
                        rfl

theorem cell23_3248859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_3248859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248859 prefixEnd_3248859 := by exact prefixLift 3248859
  have htrace : WordTrace (prefixWord ++ tailWord_3248859) baseStart_3248859 baseEnd_3248859 := by
    simpa [prefixWord, tailWord_3248859, baseEnd_3248859] using wordTrace_append hprefix tailTrace_3248859
  have hstable : (prefixWord ++ tailWord_3248859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248859).length < 2 ^ (prefixWord ++ tailWord_3248859).sum := by decide
  have hdescent : baseEnd_3248859 < baseStart_3248859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248876 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 3]
def baseStart_3248876 : Nat := 118140960795 + 3248876 * 2 ^ 59
def prefixEnd_3248876 : Nat := 4983230072969 + 3 ^ 40 * 3248876 * 2
def baseEnd_3248876 : Nat := 1668234974856735991408697

theorem tailTrace_3248876 : CollatzResearch.WordTrace tailWord_3248876 prefixEnd_3248876 1668234974856735991408697 := by
  unfold tailWord_3248876
  simp only [CollatzResearch.WordTrace]
  refine ⟨59248121288942295345471241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78997495051923060460628321 59248121288942295345471241)
  ·
    refine ⟨44436090966706721509103431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59248121288942295345471241 44436090966706721509103431)
    ·
      refine ⟨66654136450060082263655147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44436090966706721509103431 66654136450060082263655147)
      ·
        refine ⟨99981204675090123395482721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66654136450060082263655147 99981204675090123395482721)
        ·
          refine ⟨74985903506317592546612041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99981204675090123395482721 74985903506317592546612041)
          ·
            refine ⟨56239427629738194409959031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74985903506317592546612041 56239427629738194409959031)
            ·
              refine ⟨84359141444607291614938547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56239427629738194409959031 84359141444607291614938547)
              ·
                refine ⟨126538712166910937422407821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84359141444607291614938547 126538712166910937422407821)
                ·
                  refine ⟨47452017062591601533402933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126538712166910937422407821 47452017062591601533402933)
                  ·
                    refine ⟨4448626599617962643756525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47452017062591601533402933 4448626599617962643756525)
                    ·
                      refine ⟨1668234974856735991408697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4448626599617962643756525 1668234974856735991408697)
                      ·
                        rfl

theorem cell23_3248876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 3].length) (baseStart_3248876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248876 prefixEnd_3248876 := by exact prefixLift 3248876
  have htrace : WordTrace (prefixWord ++ tailWord_3248876) baseStart_3248876 baseEnd_3248876 := by
    simpa [prefixWord, tailWord_3248876, baseEnd_3248876] using wordTrace_append hprefix tailTrace_3248876
  have hstable : (prefixWord ++ tailWord_3248876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248876).length < 2 ^ (prefixWord ++ tailWord_3248876).sum := by decide
  have hdescent : baseEnd_3248876 < baseStart_3248876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248894 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2]
def baseStart_3248894 : Nat := 118140960795 + 3248894 * 2 ^ 59
def prefixEnd_3248894 : Nat := 4983230072969 + 3 ^ 40 * 3248894 * 2
def baseEnd_3248894 : Nat := 1668244217508516920983615

theorem tailTrace_3248894 : CollatzResearch.WordTrace tailWord_3248894 prefixEnd_3248894 1668244217508516920983615 := by
  unfold tailWord_3248894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14812112386477422470637217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78997932727879586510065157 14812112386477422470637217)
  ·
    refine ⟨11109084289858066852977913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14812112386477422470637217 11109084289858066852977913)
    ·
      refine ⟨8331813217393550139733435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11109084289858066852977913 8331813217393550139733435)
      ·
        refine ⟨12497719826090325209600153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8331813217393550139733435 12497719826090325209600153)
        ·
          refine ⟨9373289869567743907200115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12497719826090325209600153 9373289869567743907200115)
          ·
            refine ⟨14059934804351615860800173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9373289869567743907200115 14059934804351615860800173)
            ·
              refine ⟨5272475551631855947800065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14059934804351615860800173 5272475551631855947800065)
              ·
                refine ⟨3954356663723891960850049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5272475551631855947800065 3954356663723891960850049)
                ·
                  refine ⟨2965767497792918970637537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3954356663723891960850049 2965767497792918970637537)
                  ·
                    refine ⟨2224325623344689227978153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965767497792918970637537 2224325623344689227978153)
                    ·
                      refine ⟨1668244217508516920983615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224325623344689227978153 1668244217508516920983615)
                      ·
                        rfl

theorem cell23_3248894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_3248894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248894 prefixEnd_3248894 := by exact prefixLift 3248894
  have htrace : WordTrace (prefixWord ++ tailWord_3248894) baseStart_3248894 baseEnd_3248894 := by
    simpa [prefixWord, tailWord_3248894, baseEnd_3248894] using wordTrace_append hprefix tailTrace_3248894
  have hstable : (prefixWord ++ tailWord_3248894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248894).length < 2 ^ (prefixWord ++ tailWord_3248894).sum := by decide
  have hdescent : baseEnd_3248894 < baseStart_3248894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248906 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3248906 : Nat := 118140960795 + 3248906 * 2 ^ 59
def prefixEnd_3248906 : Nat := 4983230072969 + 3 ^ 40 * 3248906 * 2
def baseEnd_3248906 : Nat := 1668250379276370874033559

theorem tailTrace_3248906 : CollatzResearch.WordTrace tailWord_3248906 prefixEnd_3248906 1668250379276370874033559 := by
  unfold tailWord_3248906
  simp only [CollatzResearch.WordTrace]
  refine ⟨29624334191943976453633643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78998224511850603876356381 29624334191943976453633643)
  ·
    refine ⟨44436501287915964680450465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29624334191943976453633643 44436501287915964680450465)
    ·
      refine ⟨33327375965936973510337849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44436501287915964680450465 33327375965936973510337849)
      ·
        refine ⟨24995531974452730132753387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33327375965936973510337849 24995531974452730132753387)
        ·
          refine ⟨37493297961679095199130081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24995531974452730132753387 37493297961679095199130081)
          ·
            refine ⟨28119973471259321399347561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37493297961679095199130081 28119973471259321399347561)
            ·
              refine ⟨21089980103444491049510671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28119973471259321399347561 21089980103444491049510671)
              ·
                refine ⟨31634970155166736574266007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21089980103444491049510671 31634970155166736574266007)
                ·
                  refine ⟨47452455232750104861399011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31634970155166736574266007 47452455232750104861399011)
                  ·
                    refine ⟨71178682849125157292098517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47452455232750104861399011 71178682849125157292098517)
                    ·
                      refine ⟨1668250379276370874033559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 71178682849125157292098517 1668250379276370874033559)
                      ·
                        rfl

theorem cell23_3248906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3248906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248906 prefixEnd_3248906 := by exact prefixLift 3248906
  have htrace : WordTrace (prefixWord ++ tailWord_3248906) baseStart_3248906 baseEnd_3248906 := by
    simpa [prefixWord, tailWord_3248906, baseEnd_3248906] using wordTrace_append hprefix tailTrace_3248906
  have hstable : (prefixWord ++ tailWord_3248906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248906).length < 2 ^ (prefixWord ++ tailWord_3248906).sum := by decide
  have hdescent : baseEnd_3248906 < baseStart_3248906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248933 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 4]
def baseStart_3248933 : Nat := 118140960795 + 3248933 * 2 ^ 59
def prefixEnd_3248933 : Nat := 4983230072969 + 3 ^ 40 * 3248933 * 2
def baseEnd_3248933 : Nat := 1668264243254042268395935

theorem tailTrace_3248933 : CollatzResearch.WordTrace tailWord_3248933 prefixEnd_3248933 1668264243254042268395935 := by
  unfold tailWord_3248933
  simp only [CollatzResearch.WordTrace]
  refine ⟨118498321538678089425767453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78998881025785392950511635 118498321538678089425767453)
  ·
    refine ⟨44436870577004283534662795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118498321538678089425767453 44436870577004283534662795)
    ·
      refine ⟨66655305865506425301994193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44436870577004283534662795 66655305865506425301994193)
      ·
        refine ⟨49991479399129818976495645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66655305865506425301994193 49991479399129818976495645)
        ·
          refine ⟨18746804774673682116185867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49991479399129818976495645 18746804774673682116185867)
          ·
            refine ⟨28120207162010523174278801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18746804774673682116185867 28120207162010523174278801)
            ·
              refine ⟨21090155371507892380709101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28120207162010523174278801 21090155371507892380709101)
              ·
                refine ⟨7908808264315459642765913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21090155371507892380709101 7908808264315459642765913)
                ·
                  refine ⟨5931606198236594732074435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7908808264315459642765913 5931606198236594732074435)
                  ·
                    refine ⟨8897409297354892098111653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5931606198236594732074435 8897409297354892098111653)
                    ·
                      refine ⟨1668264243254042268395935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8897409297354892098111653 1668264243254042268395935)
                      ·
                        rfl

theorem cell23_3248933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_3248933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248933 prefixEnd_3248933 := by exact prefixLift 3248933
  have htrace : WordTrace (prefixWord ++ tailWord_3248933) baseStart_3248933 baseEnd_3248933 := by
    simpa [prefixWord, tailWord_3248933, baseEnd_3248933] using wordTrace_append hprefix tailTrace_3248933
  have hstable : (prefixWord ++ tailWord_3248933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248933).length < 2 ^ (prefixWord ++ tailWord_3248933).sum := by decide
  have hdescent : baseEnd_3248933 < baseStart_3248933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248960 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 1, 4]
def baseStart_3248960 : Nat := 118140960795 + 3248960 * 2 ^ 59
def prefixEnd_3248960 : Nat := 4983230072969 + 3 ^ 40 * 3248960 * 2
def baseEnd_3248960 : Nat := 556092702410571220919437

theorem tailTrace_3248960 : CollatzResearch.WordTrace tailWord_3248960 prefixEnd_3248960 556092702410571220919437 := by
  unfold tailWord_3248960
  simp only [CollatzResearch.WordTrace]
  refine ⟨59249653154790136518500167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78999537539720182024666889 59249653154790136518500167)
  ·
    refine ⟨88874479732185204777750251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59249653154790136518500167 88874479732185204777750251)
    ·
      refine ⟨133311719598277807166625377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88874479732185204777750251 133311719598277807166625377)
      ·
        refine ⟨99983789698708355374969033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133311719598277807166625377 99983789698708355374969033)
        ·
          refine ⟨74987842274031266531226775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99983789698708355374969033 74987842274031266531226775)
          ·
            refine ⟨112481763411046899796840163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74987842274031266531226775 112481763411046899796840163)
            ·
              refine ⟨168722645116570349695260245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112481763411046899796840163 168722645116570349695260245)
              ·
                refine ⟨1977218497459808785491331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168722645116570349695260245 1977218497459808785491331)
                ·
                  refine ⟨2965827746189713178236997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977218497459808785491331 2965827746189713178236997)
                  ·
                    refine ⟨556092702410571220919437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2965827746189713178236997 556092702410571220919437)
                    ·
                      rfl

theorem cell23_3248960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 4].length) (baseStart_3248960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248960 prefixEnd_3248960 := by exact prefixLift 3248960
  have htrace : WordTrace (prefixWord ++ tailWord_3248960) baseStart_3248960 baseEnd_3248960 := by
    simpa [prefixWord, tailWord_3248960, baseEnd_3248960] using wordTrace_append hprefix tailTrace_3248960
  have hstable : (prefixWord ++ tailWord_3248960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248960).length < 2 ^ (prefixWord ++ tailWord_3248960).sum := by decide
  have hdescent : baseEnd_3248960 < baseStart_3248960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3248976 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6]
def baseStart_3248976 : Nat := 118140960795 + 3248976 * 2 ^ 59
def prefixEnd_3248976 : Nat := 4983230072969 + 3 ^ 40 * 3248976 * 2
def baseEnd_3248976 : Nat := 1668286322922185600158237

theorem tailTrace_3248976 : CollatzResearch.WordTrace tailWord_3248976 prefixEnd_3248976 1668286322922185600158237 := by
  unfold tailWord_3248976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59249944938761153884791391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78999926585014871846388521 59249944938761153884791391)
  ·
    refine ⟨88874917408141730827187087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59249944938761153884791391 88874917408141730827187087)
    ·
      refine ⟨133312376112212596240780631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88874917408141730827187087 133312376112212596240780631)
      ·
        refine ⟨199968564168318894361170947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133312376112212596240780631 199968564168318894361170947)
        ·
          refine ⟨299952846252478341541756421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199968564168318894361170947 299952846252478341541756421)
          ·
            refine ⟨56241158672339689039079329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299952846252478341541756421 56241158672339689039079329)
            ·
              refine ⟨42180869004254766779309497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56241158672339689039079329 42180869004254766779309497)
              ·
                refine ⟨31635651753191075084482123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42180869004254766779309497 31635651753191075084482123)
                ·
                  refine ⟨47453477629786612626723185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31635651753191075084482123 47453477629786612626723185)
                  ·
                    refine ⟨35590108222339959470042389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47453477629786612626723185 35590108222339959470042389)
                    ·
                      refine ⟨1668286322922185600158237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35590108222339959470042389 1668286322922185600158237)
                      ·
                        rfl

theorem cell23_3248976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_3248976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3248976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3248976 prefixEnd_3248976 := by exact prefixLift 3248976
  have htrace : WordTrace (prefixWord ++ tailWord_3248976) baseStart_3248976 baseEnd_3248976 := by
    simpa [prefixWord, tailWord_3248976, baseEnd_3248976] using wordTrace_append hprefix tailTrace_3248976
  have hstable : (prefixWord ++ tailWord_3248976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3248976).length < 2 ^ (prefixWord ++ tailWord_3248976).sum := by decide
  have hdescent : baseEnd_3248976 < baseStart_3248976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3248976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249003 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 1, 5]
def baseStart_3249003 : Nat := 118140960795 + 3249003 * 2 ^ 59
def prefixEnd_3249003 : Nat := 4983230072969 + 3 ^ 40 * 3249003 * 2
def baseEnd_3249003 : Nat := 556100062299952331506871

theorem tailTrace_3249003 : CollatzResearch.WordTrace tailWord_3249003 prefixEnd_3249003 556100062299952331506871 := by
  unfold tailWord_3249003
  simp only [CollatzResearch.WordTrace]
  refine ⟨118500874648424491380815663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79000583098949660920543775 118500874648424491380815663)
  ·
    refine ⟨177751311972636737071223495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118500874648424491380815663 177751311972636737071223495)
    ·
      refine ⟨266626967958955105606835243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177751311972636737071223495 266626967958955105606835243)
      ·
        refine ⟨399940451938432658410252865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266626967958955105606835243 399940451938432658410252865)
        ·
          refine ⟨299955338953824493807689649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399940451938432658410252865 299955338953824493807689649)
          ·
            refine ⟨224966504215368370355767237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299955338953824493807689649 224966504215368370355767237)
            ·
              refine ⟨42181219540381569441706357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224966504215368370355767237 42181219540381569441706357)
              ·
                refine ⟨3954489331910772135159971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42181219540381569441706357 3954489331910772135159971)
                ·
                  refine ⟨5931733997866158202739957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954489331910772135159971 5931733997866158202739957)
                  ·
                    refine ⟨556100062299952331506871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5931733997866158202739957 556100062299952331506871)
                    ·
                      rfl

theorem cell23_3249003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 5].length) (baseStart_3249003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249003 prefixEnd_3249003 := by exact prefixLift 3249003
  have htrace : WordTrace (prefixWord ++ tailWord_3249003) baseStart_3249003 baseEnd_3249003 := by
    simpa [prefixWord, tailWord_3249003, baseEnd_3249003] using wordTrace_append hprefix tailTrace_3249003
  have hstable : (prefixWord ++ tailWord_3249003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249003).length < 2 ^ (prefixWord ++ tailWord_3249003).sum := by decide
  have hdescent : baseEnd_3249003 < baseStart_3249003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249023 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4]
def baseStart_3249023 : Nat := 118140960795 + 3249023 * 2 ^ 59
def prefixEnd_3249023 : Nat := 4983230072969 + 3 ^ 40 * 3249023 * 2
def baseEnd_3249023 : Nat := 1668310456512946916270521

theorem tailTrace_3249023 : CollatzResearch.WordTrace tailWord_3249023 prefixEnd_3249023 1668310456512946916270521 := by
  unfold tailWord_3249023
  simp only [CollatzResearch.WordTrace]
  refine ⟨118501604108352034796543723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79001069405568023197695815 118501604108352034796543723)
  ·
    refine ⟨177752406162528052194815585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118501604108352034796543723 177752406162528052194815585)
    ·
      refine ⟨133314304621896039146111689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177752406162528052194815585 133314304621896039146111689)
      ·
        refine ⟨99985728466422029359583767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133314304621896039146111689 99985728466422029359583767)
        ·
          refine ⟨149978592699633044039375651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99985728466422029359583767 149978592699633044039375651)
          ·
            refine ⟨224967889049449566059063477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149978592699633044039375651 224967889049449566059063477)
            ·
              refine ⟨21090739598385896818037201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224967889049449566059063477 21090739598385896818037201)
              ·
                refine ⟨15818054698789422613527901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21090739598385896818037201 15818054698789422613527901)
                ·
                  refine ⟨5931770512046033480072963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15818054698789422613527901 5931770512046033480072963)
                  ·
                    refine ⟨8897655768069050220109445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5931770512046033480072963 8897655768069050220109445)
                    ·
                      refine ⟨1668310456512946916270521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8897655768069050220109445 1668310456512946916270521)
                      ·
                        rfl

theorem cell23_3249023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_3249023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249023 prefixEnd_3249023 := by exact prefixLift 3249023
  have htrace : WordTrace (prefixWord ++ tailWord_3249023) baseStart_3249023 baseEnd_3249023 := by
    simpa [prefixWord, tailWord_3249023, baseEnd_3249023] using wordTrace_append hprefix tailTrace_3249023
  have hstable : (prefixWord ++ tailWord_3249023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249023).length < 2 ^ (prefixWord ++ tailWord_3249023).sum := by decide
  have hdescent : baseEnd_3249023 < baseStart_3249023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249033 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 1, 6]
def baseStart_3249033 : Nat := 118140960795 + 3249033 * 2 ^ 59
def prefixEnd_3249033 : Nat := 4983230072969 + 3 ^ 40 * 3249033 * 2
def baseEnd_3249033 : Nat := 556105197106497292381825

theorem tailTrace_3249033 : CollatzResearch.WordTrace tailWord_3249033 prefixEnd_3249033 556105197106497292381825 := by
  unfold tailWord_3249033
  simp only [CollatzResearch.WordTrace]
  refine ⟨118501968838315806504407753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79001312558877204336271835 118501968838315806504407753)
  ·
    refine ⟨88876476628736854878305815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118501968838315806504407753 88876476628736854878305815)
    ·
      refine ⟨133314714943105282317458723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88876476628736854878305815 133314714943105282317458723)
      ·
        refine ⟨199972072414657923476188085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133314714943105282317458723 199972072414657923476188085)
        ·
          refine ⟨18747381788874180325892633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199972072414657923476188085 18747381788874180325892633)
          ·
            refine ⟨14060536341655635244419475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18747381788874180325892633 14060536341655635244419475)
            ·
              refine ⟨21090804512483452866629213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14060536341655635244419475 21090804512483452866629213)
              ·
                refine ⟨7909051692181294824985955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21090804512483452866629213 7909051692181294824985955)
                ·
                  refine ⟨11863577538271942237478933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909051692181294824985955 11863577538271942237478933)
                  ·
                    refine ⟨556105197106497292381825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11863577538271942237478933 556105197106497292381825)
                    ·
                      rfl

theorem cell23_3249033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_3249033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249033 prefixEnd_3249033 := by exact prefixLift 3249033
  have htrace : WordTrace (prefixWord ++ tailWord_3249033) baseStart_3249033 baseEnd_3249033 := by
    simpa [prefixWord, tailWord_3249033, baseEnd_3249033] using wordTrace_append hprefix tailTrace_3249033
  have hstable : (prefixWord ++ tailWord_3249033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249033).length < 2 ^ (prefixWord ++ tailWord_3249033).sum := by decide
  have hdescent : baseEnd_3249033 < baseStart_3249033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249057 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3249057 : Nat := 118140960795 + 3249057 * 2 ^ 59
def prefixEnd_3249057 : Nat := 4983230072969 + 3 ^ 40 * 3249057 * 2
def baseEnd_3249057 : Nat := 1668327914855199783245365

theorem tailTrace_3249057 : CollatzResearch.WordTrace tailWord_3249057 prefixEnd_3249057 1668327914855199783245365 := by
  unfold tailWord_3249057
  simp only [CollatzResearch.WordTrace]
  refine ⟨118502844190228858603281425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79001896126819239068854283 118502844190228858603281425)
  ·
    refine ⟨88877133142671643952461069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118502844190228858603281425 88877133142671643952461069)
    ·
      refine ⟨33328924928501866482172901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88877133142671643952461069 33328924928501866482172901)
      ·
        refine ⟨6249173424094099965407419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33328924928501866482172901 6249173424094099965407419)
        ·
          refine ⟨9373760136141149948111129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6249173424094099965407419 9373760136141149948111129)
          ·
            refine ⟨7030320102105862461083347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9373760136141149948111129 7030320102105862461083347)
            ·
              refine ⟨10545480153158793691625021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030320102105862461083347 10545480153158793691625021)
              ·
                refine ⟨3954555057434547634359383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10545480153158793691625021 3954555057434547634359383)
                ·
                  refine ⟨5931832586151821451539075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3954555057434547634359383 5931832586151821451539075)
                  ·
                    refine ⟨8897748879227732177308613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5931832586151821451539075 8897748879227732177308613)
                    ·
                      refine ⟨1668327914855199783245365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8897748879227732177308613 1668327914855199783245365)
                      ·
                        rfl

theorem cell23_3249057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3249057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249057 prefixEnd_3249057 := by exact prefixLift 3249057
  have htrace : WordTrace (prefixWord ++ tailWord_3249057) baseStart_3249057 baseEnd_3249057 := by
    simpa [prefixWord, tailWord_3249057, baseEnd_3249057] using wordTrace_append hprefix tailTrace_3249057
  have hstable : (prefixWord ++ tailWord_3249057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249057).length < 2 ^ (prefixWord ++ tailWord_3249057).sum := by decide
  have hdescent : baseEnd_3249057 < baseStart_3249057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249103 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5]
def baseStart_3249103 : Nat := 118140960795 + 3249103 * 2 ^ 59
def prefixEnd_3249103 : Nat := 4983230072969 + 3 ^ 40 * 3249103 * 2
def baseEnd_3249103 : Nat := 1668351534965306603270153

theorem tailTrace_3249103 : CollatzResearch.WordTrace tailWord_3249103 prefixEnd_3249103 1668351534965306603270153 := by
  unfold tailWord_3249103
  simp only [CollatzResearch.WordTrace]
  refine ⟨118504521948062208459455963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79003014632041472306303975 118504521948062208459455963)
  ·
    refine ⟨177756782922093312689183945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118504521948062208459455963 177756782922093312689183945)
    ·
      refine ⟨133317587191569984516887959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177756782922093312689183945 133317587191569984516887959)
      ·
        refine ⟨199976380787354976775331939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133317587191569984516887959 199976380787354976775331939)
        ·
          refine ⟨299964571181032465162997909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199976380787354976775331939 299964571181032465162997909)
          ·
            refine ⟨14060839274110896804515527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 299964571181032465162997909 14060839274110896804515527)
            ·
              refine ⟨21091258911166345206773291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14060839274110896804515527 21091258911166345206773291)
              ·
                refine ⟨31636888366749517810159937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21091258911166345206773291 31636888366749517810159937)
                ·
                  refine ⟨23727666275062138357619953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31636888366749517810159937 23727666275062138357619953)
                  ·
                    refine ⟨17795749706296603768214965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23727666275062138357619953 17795749706296603768214965)
                    ·
                      refine ⟨1668351534965306603270153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17795749706296603768214965 1668351534965306603270153)
                      ·
                        rfl

theorem cell23_3249103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_3249103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249103 prefixEnd_3249103 := by exact prefixLift 3249103
  have htrace : WordTrace (prefixWord ++ tailWord_3249103) baseStart_3249103 baseEnd_3249103 := by
    simpa [prefixWord, tailWord_3249103, baseEnd_3249103] using wordTrace_append hprefix tailTrace_3249103
  have hstable : (prefixWord ++ tailWord_3249103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249103).length < 2 ^ (prefixWord ++ tailWord_3249103).sum := by decide
  have hdescent : baseEnd_3249103 < baseStart_3249103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249108 : List Nat := [2, 4, 1, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_3249108 : Nat := 118140960795 + 3249108 * 2 ^ 59
def prefixEnd_3249108 : Nat := 4983230072969 + 3 ^ 40 * 3249108 * 2
def baseEnd_3249108 : Nat := 1668354102368579083707631

theorem tailTrace_3249108 : CollatzResearch.WordTrace tailWord_3249108 prefixEnd_3249108 1668354102368579083707631 := by
  unfold tailWord_3249108
  simp only [CollatzResearch.WordTrace]
  refine ⟨59252352156522047156693989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79003136208696062875591985 59252352156522047156693989)
  ·
    refine ⟨11109816029347883841880123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59252352156522047156693989 11109816029347883841880123)
    ·
      refine ⟨16664724044021825762820185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11109816029347883841880123 16664724044021825762820185)
      ·
        refine ⟨12498543033016369322115139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16664724044021825762820185 12498543033016369322115139)
        ·
          refine ⟨18747814549524553983172709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498543033016369322115139 18747814549524553983172709)
          ·
            refine ⟨3515215228035853871844883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18747814549524553983172709 3515215228035853871844883)
            ·
              refine ⟨5272822842053780807767325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515215228035853871844883 5272822842053780807767325)
              ·
                refine ⟨1977308565770167802912747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5272822842053780807767325 1977308565770167802912747)
                ·
                  refine ⟨2965962848655251704369121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977308565770167802912747 2965962848655251704369121)
                  ·
                    refine ⟨2224472136491438778276841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965962848655251704369121 2224472136491438778276841)
                    ·
                      refine ⟨1668354102368579083707631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224472136491438778276841 1668354102368579083707631)
                      ·
                        rfl

theorem cell23_3249108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_3249108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249108 prefixEnd_3249108 := by exact prefixLift 3249108
  have htrace : WordTrace (prefixWord ++ tailWord_3249108) baseStart_3249108 baseEnd_3249108 := by
    simpa [prefixWord, tailWord_3249108, baseEnd_3249108] using wordTrace_append hprefix tailTrace_3249108
  have hstable : (prefixWord ++ tailWord_3249108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249108).length < 2 ^ (prefixWord ++ tailWord_3249108).sum := by decide
  have hdescent : baseEnd_3249108 < baseStart_3249108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249125 : List Nat := [1, 3, 1, 6, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3249125 : Nat := 118140960795 + 3249125 * 2 ^ 59
def prefixEnd_3249125 : Nat := 4983230072969 + 3 ^ 40 * 3249125 * 2
def baseEnd_3249125 : Nat := 1668362831539705517195053

theorem tailTrace_3249125 : CollatzResearch.WordTrace tailWord_3249125 prefixEnd_3249125 1668362831539705517195053 := by
  unfold tailWord_3249125
  simp only [CollatzResearch.WordTrace]
  refine ⟨118505324353982506216756829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79003549569321670811171219 118505324353982506216756829)
  ·
    refine ⟨44439496632743439831283811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118505324353982506216756829 44439496632743439831283811)
    ·
      refine ⟨66659244949115159746925717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44439496632743439831283811 66659244949115159746925717)
      ·
        refine ⟨3124652106989773113137143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66659244949115159746925717 3124652106989773113137143)
        ·
          refine ⟨4686978160484659669705715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3124652106989773113137143 4686978160484659669705715)
          ·
            refine ⟨7030467240726989504558573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4686978160484659669705715 7030467240726989504558573)
            ·
              refine ⟨2636425215272621064209465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7030467240726989504558573 2636425215272621064209465)
              ·
                refine ⟨1977318911454465798157099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2636425215272621064209465 1977318911454465798157099)
                ·
                  refine ⟨2965978367181698697235649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977318911454465798157099 2965978367181698697235649)
                  ·
                    refine ⟨2224483775386274022926737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2965978367181698697235649 2224483775386274022926737)
                    ·
                      refine ⟨1668362831539705517195053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224483775386274022926737 1668362831539705517195053)
                      ·
                        rfl

theorem cell23_3249125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3249125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249125 prefixEnd_3249125 := by exact prefixLift 3249125
  have htrace : WordTrace (prefixWord ++ tailWord_3249125) baseStart_3249125 baseEnd_3249125 := by
    simpa [prefixWord, tailWord_3249125, baseEnd_3249125] using wordTrace_append hprefix tailTrace_3249125
  have hstable : (prefixWord ++ tailWord_3249125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249125).length < 2 ^ (prefixWord ++ tailWord_3249125).sum := by decide
  have hdescent : baseEnd_3249125 < baseStart_3249125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249187 : List Nat := [1, 1, 1, 4, 3, 3, 1, 4, 5]
def baseStart_3249187 : Nat := 118140960795 + 3249187 * 2 ^ 59
def prefixEnd_3249187 : Nat := 4983230072969 + 3 ^ 40 * 3249187 * 2
def baseEnd_3249187 : Nat := 185377185260031586068863

theorem tailTrace_3249187 : CollatzResearch.WordTrace tailWord_3249187 prefixEnd_3249187 185377185260031586068863 := by
  unfold tailWord_3249187
  simp only [CollatzResearch.WordTrace]
  refine ⟨118507585679757890805513815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79005057119838593870342543 118507585679757890805513815)
  ·
    refine ⟨177761378519636836208270723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118507585679757890805513815 177761378519636836208270723)
    ·
      refine ⟨266642067779455254312406085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177761378519636836208270723 266642067779455254312406085)
      ·
        refine ⟨49995387708647860183576141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266642067779455254312406085 49995387708647860183576141)
        ·
          refine ⟨18748270390742947568841053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49995387708647860183576141 18748270390742947568841053)
          ·
            refine ⟨7030601396528605338315395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18748270390742947568841053 7030601396528605338315395)
            ·
              refine ⟨10545902094792908007473093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030601396528605338315395 10545902094792908007473093)
              ·
                refine ⟨1977356642773670251401205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10545902094792908007473093 1977356642773670251401205)
                ·
                  refine ⟨185377185260031586068863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1977356642773670251401205 185377185260031586068863)
                  ·
                    rfl

theorem cell23_3249187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 4, 5].length) (baseStart_3249187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249187 prefixEnd_3249187 := by exact prefixLift 3249187
  have htrace : WordTrace (prefixWord ++ tailWord_3249187) baseStart_3249187 baseEnd_3249187 := by
    simpa [prefixWord, tailWord_3249187, baseEnd_3249187] using wordTrace_append hprefix tailTrace_3249187
  have hstable : (prefixWord ++ tailWord_3249187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249187).length < 2 ^ (prefixWord ++ tailWord_3249187).sum := by decide
  have hdescent : baseEnd_3249187 < baseStart_3249187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249217 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3249217 : Nat := 118140960795 + 3249217 * 2 ^ 59
def prefixEnd_3249217 : Nat := 4983230072969 + 3 ^ 40 * 3249217 * 2
def baseEnd_3249217 : Nat := 556136690586639719081543

theorem tailTrace_3249217 : CollatzResearch.WordTrace tailWord_3249217 prefixEnd_3249217 556136690586639719081543 := by
  unfold tailWord_3249217
  simp only [CollatzResearch.WordTrace]
  refine ⟨118508679869649205929105905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79005786579766137286070603 118508679869649205929105905)
  ·
    refine ⟨88881509902236904446829429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118508679869649205929105905 88881509902236904446829429)
    ·
      refine ⟨8332641553334709791890259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88881509902236904446829429 8332641553334709791890259)
      ·
        refine ⟨12498962330002064687835389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332641553334709791890259 12498962330002064687835389)
        ·
          refine ⟨4687110873750774257938271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12498962330002064687835389 4687110873750774257938271)
          ·
            refine ⟨7030666310626161386907407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687110873750774257938271 7030666310626161386907407)
            ·
              refine ⟨10545999465939242080361111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030666310626161386907407 10545999465939242080361111)
              ·
                refine ⟨15818999198908863120541667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10545999465939242080361111 15818999198908863120541667)
                ·
                  refine ⟨23728498798363294680812501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15818999198908863120541667 23728498798363294680812501)
                  ·
                    refine ⟨556136690586639719081543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23728498798363294680812501 556136690586639719081543)
                    ·
                      rfl

theorem cell23_3249217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3249217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249217 prefixEnd_3249217 := by exact prefixLift 3249217
  have htrace : WordTrace (prefixWord ++ tailWord_3249217) baseStart_3249217 baseEnd_3249217 := by
    simpa [prefixWord, tailWord_3249217, baseEnd_3249217] using wordTrace_append hprefix tailTrace_3249217
  have hstable : (prefixWord ++ tailWord_3249217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249217).length < 2 ^ (prefixWord ++ tailWord_3249217).sum := by decide
  have hdescent : baseEnd_3249217 < baseStart_3249217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249237 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 4, 4, 2]
def baseStart_3249237 : Nat := 118140960795 + 3249237 * 2 ^ 59
def prefixEnd_3249237 : Nat := 4983230072969 + 3 ^ 40 * 3249237 * 2
def baseEnd_3249237 : Nat := 1668420341373009078994537

theorem tailTrace_3249237 : CollatzResearch.WordTrace tailWord_3249237 prefixEnd_3249237 1668420341373009078994537 := by
  unfold tailWord_3249237
  simp only [CollatzResearch.WordTrace]
  refine ⟨118509409329576749344833965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79006272886384499563222643 118509409329576749344833965)
  ·
    refine ⟨44441028498591281004312737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118509409329576749344833965 44441028498591281004312737)
    ·
      refine ⟨33330771373943460753234553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44441028498591281004312737 33330771373943460753234553)
      ·
        refine ⟨24998078530457595564925915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33330771373943460753234553 24998078530457595564925915)
        ·
          refine ⟨37497117795686393347388873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24998078530457595564925915 37497117795686393347388873)
          ·
            refine ⟨28122838346764795010541655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37497117795686393347388873 28122838346764795010541655)
            ·
              refine ⟨42184257520147192515812483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28122838346764795010541655 42184257520147192515812483)
              ·
                refine ⟨63276386280220788773718725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42184257520147192515812483 63276386280220788773718725)
                ·
                  refine ⟨11864322427541397895072261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63276386280220788773718725 11864322427541397895072261)
                  ·
                    refine ⟨2224560455164012105326049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11864322427541397895072261 2224560455164012105326049)
                    ·
                      refine ⟨1668420341373009078994537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224560455164012105326049 1668420341373009078994537)
                      ·
                        rfl

theorem cell23_3249237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_3249237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249237 prefixEnd_3249237 := by exact prefixLift 3249237
  have htrace : WordTrace (prefixWord ++ tailWord_3249237) baseStart_3249237 baseEnd_3249237 := by
    simpa [prefixWord, tailWord_3249237, baseEnd_3249237] using wordTrace_append hprefix tailTrace_3249237
  have hstable : (prefixWord ++ tailWord_3249237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249237).length < 2 ^ (prefixWord ++ tailWord_3249237).sum := by decide
  have hdescent : baseEnd_3249237 < baseStart_3249237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249247 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 3, 4]
def baseStart_3249247 : Nat := 118140960795 + 3249247 * 2 ^ 59
def prefixEnd_3249247 : Nat := 4983230072969 + 3 ^ 40 * 3249247 * 2
def baseEnd_3249247 : Nat := 556141825393184679956497

theorem tailTrace_3249247 : CollatzResearch.WordTrace tailWord_3249247 prefixEnd_3249247 556141825393184679956497 := by
  unfold tailWord_3249247
  simp only [CollatzResearch.WordTrace]
  refine ⟨118509774059540521052697995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79006516039693680701798663 118509774059540521052697995)
  ·
    refine ⟨177764661089310781579046993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118509774059540521052697995 177764661089310781579046993)
    ·
      refine ⟨133323495816983086184285245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177764661089310781579046993 133323495816983086184285245)
      ·
        refine ⟨49996310931368657319106967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133323495816983086184285245 49996310931368657319106967)
        ·
          refine ⟨74994466397052985978660451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49996310931368657319106967 74994466397052985978660451)
          ·
            refine ⟨112491699595579478967990677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74994466397052985978660451 112491699595579478967990677)
            ·
              refine ⟨5273048418542788076624563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112491699595579478967990677 5273048418542788076624563)
              ·
                refine ⟨7909572627814182114936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273048418542788076624563 7909572627814182114936845)
                ·
                  refine ⟨2966089735430318293101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7909572627814182114936845 2966089735430318293101317)
                  ·
                    refine ⟨556141825393184679956497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966089735430318293101317 556141825393184679956497)
                    ·
                      rfl

theorem cell23_3249247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 4].length) (baseStart_3249247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249247 prefixEnd_3249247 := by exact prefixLift 3249247
  have htrace : WordTrace (prefixWord ++ tailWord_3249247) baseStart_3249247 baseEnd_3249247 := by
    simpa [prefixWord, tailWord_3249247, baseEnd_3249247] using wordTrace_append hprefix tailTrace_3249247
  have hstable : (prefixWord ++ tailWord_3249247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249247).length < 2 ^ (prefixWord ++ tailWord_3249247).sum := by decide
  have hdescent : baseEnd_3249247 < baseStart_3249247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249281 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3249281 : Nat := 118140960795 + 3249281 * 2 ^ 59
def prefixEnd_3249281 : Nat := 4983230072969 + 3 ^ 40 * 3249281 * 2
def baseEnd_3249281 : Nat := 556147644840602302281445

theorem tailTrace_3249281 : CollatzResearch.WordTrace tailWord_3249281 prefixEnd_3249281 556147644840602302281445 := by
  unfold tailWord_3249281
  simp only [CollatzResearch.WordTrace]
  refine ⟨118511014141417344859435697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79007342760944896572957131 118511014141417344859435697)
  ·
    refine ⟨88883260606063008644576773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118511014141417344859435697 88883260606063008644576773)
    ·
      refine ⟨16665611363636814120858145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88883260606063008644576773 16665611363636814120858145)
      ·
        refine ⟨12499208522727610590643609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16665611363636814120858145 12499208522727610590643609)
        ·
          refine ⟨9374406392045707942982707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12499208522727610590643609 9374406392045707942982707)
          ·
            refine ⟨14061609588068561914474061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9374406392045707942982707 14061609588068561914474061)
            ·
              refine ⟨5273103595525710717927773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14061609588068561914474061 5273103595525710717927773)
              ·
                refine ⟨1977413848322141519222915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5273103595525710717927773 1977413848322141519222915)
                ·
                  refine ⟨2966120772483212278834373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977413848322141519222915 2966120772483212278834373)
                  ·
                    refine ⟨556147644840602302281445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966120772483212278834373 556147644840602302281445)
                    ·
                      rfl

theorem cell23_3249281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3249281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249281 prefixEnd_3249281 := by exact prefixLift 3249281
  have htrace : WordTrace (prefixWord ++ tailWord_3249281) baseStart_3249281 baseEnd_3249281 := by
    simpa [prefixWord, tailWord_3249281, baseEnd_3249281] using wordTrace_append hprefix tailTrace_3249281
  have hstable : (prefixWord ++ tailWord_3249281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249281).length < 2 ^ (prefixWord ++ tailWord_3249281).sum := by decide
  have hdescent : baseEnd_3249281 < baseStart_3249281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249298 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_3249298 : Nat := 118140960795 + 3249298 * 2 ^ 59
def prefixEnd_3249298 : Nat := 4983230072969 + 3 ^ 40 * 3249298 * 2
def baseEnd_3249298 : Nat := 556150554564311113443919

theorem tailTrace_3249298 : CollatzResearch.WordTrace tailWord_3249298 prefixEnd_3249298 556150554564311113443919 := by
  unfold tailWord_3249298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29627908545588939190701137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79007756121570504508536365 29627908545588939190701137)
  ·
    refine ⟨22220931409191704393025853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29627908545588939190701137 22220931409191704393025853)
    ·
      refine ⟨8332849278446889147384695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22220931409191704393025853 8332849278446889147384695)
      ·
        refine ⟨12499273917670333721077043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332849278446889147384695 12499273917670333721077043)
        ·
          refine ⟨18748910876505500581615565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12499273917670333721077043 18748910876505500581615565)
          ·
            refine ⟨7030841578689562718105837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18748910876505500581615565 7030841578689562718105837)
            ·
              refine ⟨2636565592008586019289689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7030841578689562718105837 2636565592008586019289689)
              ·
                refine ⟨1977424194006439514467267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2636565592008586019289689 1977424194006439514467267)
                ·
                  refine ⟨2966136291009659271700901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977424194006439514467267 2966136291009659271700901)
                  ·
                    refine ⟨556150554564311113443919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966136291009659271700901 556150554564311113443919)
                    ·
                      rfl

theorem cell23_3249298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_3249298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249298 prefixEnd_3249298 := by exact prefixLift 3249298
  have htrace : WordTrace (prefixWord ++ tailWord_3249298) baseStart_3249298 baseEnd_3249298 := by
    simpa [prefixWord, tailWord_3249298, baseEnd_3249298] using wordTrace_append hprefix tailTrace_3249298
  have hstable : (prefixWord ++ tailWord_3249298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249298).length < 2 ^ (prefixWord ++ tailWord_3249298).sum := by decide
  have hdescent : baseEnd_3249298 < baseStart_3249298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249311 : List Nat := [1, 1, 2, 6, 2, 2, 2, 1, 6]
def baseStart_3249311 : Nat := 118140960795 + 3249311 * 2 ^ 59
def prefixEnd_3249311 : Nat := 4983230072969 + 3 ^ 40 * 3249311 * 2
def baseEnd_3249311 : Nat := 185384259882382421052133

theorem tailTrace_3249311 : CollatzResearch.WordTrace tailWord_3249311 prefixEnd_3249311 185384259882382421052133 := by
  unfold tailWord_3249311
  simp only [CollatzResearch.WordTrace]
  refine ⟨118512108331308659983027787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79008072220872439988685191 118512108331308659983027787)
  ·
    refine ⟨177768162496962989974541681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118512108331308659983027787 177768162496962989974541681)
    ·
      refine ⟨133326121872722242480906261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177768162496962989974541681 133326121872722242480906261)
      ·
        refine ⟨6249661962783855116292481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133326121872722242480906261 6249661962783855116292481)
        ·
          refine ⟨4687246472087891337219361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6249661962783855116292481 4687246472087891337219361)
          ·
            refine ⟨3515434854065918502914521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687246472087891337219361 3515434854065918502914521)
            ·
              refine ⟨2636576140549438877185891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515434854065918502914521 2636576140549438877185891)
              ·
                refine ⟨3954864210824158315778837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636576140549438877185891 3954864210824158315778837)
                ·
                  refine ⟨185384259882382421052133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3954864210824158315778837 185384259882382421052133)
                  ·
                    rfl

theorem cell23_3249311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 2, 1, 6].length) (baseStart_3249311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249311 prefixEnd_3249311 := by exact prefixLift 3249311
  have htrace : WordTrace (prefixWord ++ tailWord_3249311) baseStart_3249311 baseEnd_3249311 := by
    simpa [prefixWord, tailWord_3249311, baseEnd_3249311] using wordTrace_append hprefix tailTrace_3249311
  have hstable : (prefixWord ++ tailWord_3249311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249311).length < 2 ^ (prefixWord ++ tailWord_3249311).sum := by decide
  have hdescent : baseEnd_3249311 < baseStart_3249311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249327 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 2, 6, 2]
def baseStart_3249327 : Nat := 118140960795 + 3249327 * 2 ^ 59
def prefixEnd_3249327 : Nat := 4983230072969 + 3 ^ 40 * 3249327 * 2
def baseEnd_3249327 : Nat := 1668466554631913726869123

theorem tailTrace_3249327 : CollatzResearch.WordTrace tailWord_3249327 prefixEnd_3249327 1668466554631913726869123 := by
  unfold tailWord_3249327
  simp only [CollatzResearch.WordTrace]
  refine ⟨118512691899250694715610235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79008461266167129810406823 118512691899250694715610235)
  ·
    refine ⟨177769037848876042073415353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118512691899250694715610235 177769037848876042073415353)
    ·
      refine ⟨133326778386657031555061515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177769037848876042073415353 133326778386657031555061515)
      ·
        refine ⟨199990167579985547332592273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133326778386657031555061515 199990167579985547332592273)
        ·
          refine ⟨149992625684989160499444205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199990167579985547332592273 149992625684989160499444205)
          ·
            refine ⟨56247234631870935187291577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149992625684989160499444205 56247234631870935187291577)
            ·
              refine ⟨42185425973903201390468683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56247234631870935187291577 42185425973903201390468683)
              ·
                refine ⟨63278138960854802085703025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42185425973903201390468683 63278138960854802085703025)
                ·
                  refine ⟨47458604220641101564277269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63278138960854802085703025 47458604220641101564277269)
                  ·
                    refine ⟨2224622072842551635825497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47458604220641101564277269 2224622072842551635825497)
                    ·
                      refine ⟨1668466554631913726869123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224622072842551635825497 1668466554631913726869123)
                      ·
                        rfl

theorem cell23_3249327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 6, 2].length) (baseStart_3249327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249327 prefixEnd_3249327 := by exact prefixLift 3249327
  have htrace : WordTrace (prefixWord ++ tailWord_3249327) baseStart_3249327 baseEnd_3249327 := by
    simpa [prefixWord, tailWord_3249327, baseEnd_3249327] using wordTrace_append hprefix tailTrace_3249327
  have hstable : (prefixWord ++ tailWord_3249327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249327).length < 2 ^ (prefixWord ++ tailWord_3249327).sum := by decide
  have hdescent : baseEnd_3249327 < baseStart_3249327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249337 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 1, 6]
def baseStart_3249337 : Nat := 118140960795 + 3249337 * 2 ^ 59
def prefixEnd_3249337 : Nat := 4983230072969 + 3 ^ 40 * 3249337 * 2
def baseEnd_3249337 : Nat := 556157229812819562581359

theorem tailTrace_3249337 : CollatzResearch.WordTrace tailWord_3249337 prefixEnd_3249337 556157229812819562581359 := by
  unfold tailWord_3249337
  simp only [CollatzResearch.WordTrace]
  refine ⟨118513056629214466423474265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79008704419476310948982843 118513056629214466423474265)
  ·
    refine ⟨88884792471910849817605699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118513056629214466423474265 88884792471910849817605699)
    ·
      refine ⟨133327188707866274726408549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88884792471910849817605699 133327188707866274726408549)
      ·
        refine ⟨24998847882724926511201603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133327188707866274726408549 24998847882724926511201603)
        ·
          refine ⟨37498271824087389766802405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24998847882724926511201603 37498271824087389766802405)
          ·
            refine ⟨7030925967016385581275451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37498271824087389766802405 7030925967016385581275451)
            ·
              refine ⟨10546388950524578371913177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7030925967016385581275451 10546388950524578371913177)
              ·
                refine ⟨7909791712893433778934883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10546388950524578371913177 7909791712893433778934883)
                ·
                  refine ⟨11864687569340150668402325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7909791712893433778934883 11864687569340150668402325)
                  ·
                    refine ⟨556157229812819562581359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11864687569340150668402325 556157229812819562581359)
                    ·
                      rfl

theorem cell23_3249337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_3249337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249337 prefixEnd_3249337 := by exact prefixLift 3249337
  have htrace : WordTrace (prefixWord ++ tailWord_3249337) baseStart_3249337 baseEnd_3249337 := by
    simpa [prefixWord, tailWord_3249337, baseEnd_3249337] using wordTrace_append hprefix tailTrace_3249337
  have hstable : (prefixWord ++ tailWord_3249337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249337).length < 2 ^ (prefixWord ++ tailWord_3249337).sum := by decide
  have hdescent : baseEnd_3249337 < baseStart_3249337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249354 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_3249354 : Nat := 118140960795 + 3249354 * 2 ^ 59
def prefixEnd_3249354 : Nat := 4983230072969 + 3 ^ 40 * 3249354 * 2
def baseEnd_3249354 : Nat := 556160139536528373743833

theorem tailTrace_3249354 : CollatzResearch.WordTrace tailWord_3249354 prefixEnd_3249354 556160139536528373743833 := by
  unfold tailWord_3249354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29628419167538219581710779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79009117780101918884562077 29628419167538219581710779)
  ·
    refine ⟨44442628751307329372566169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29628419167538219581710779 44442628751307329372566169)
    ·
      refine ⟨33331971563480497029424627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44442628751307329372566169 33331971563480497029424627)
      ·
        refine ⟨49997957345220745544136941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33331971563480497029424627 49997957345220745544136941)
        ·
          refine ⟨18749234004457779579051353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49997957345220745544136941 18749234004457779579051353)
          ·
            refine ⟨14061925503343334684288515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18749234004457779579051353 14061925503343334684288515)
            ·
              refine ⟨21092888255015002026432773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14061925503343334684288515 21092888255015002026432773)
              ·
                refine ⟨3954916547815312879956145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21092888255015002026432773 3954916547815312879956145)
                ·
                  refine ⟨2966187410861484659967109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3954916547815312879956145 2966187410861484659967109)
                  ·
                    refine ⟨556160139536528373743833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966187410861484659967109 556160139536528373743833)
                    ·
                      rfl

theorem cell23_3249354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_3249354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249354 prefixEnd_3249354 := by exact prefixLift 3249354
  have htrace : WordTrace (prefixWord ++ tailWord_3249354) baseStart_3249354 baseEnd_3249354 := by
    simpa [prefixWord, tailWord_3249354, baseEnd_3249354] using wordTrace_append hprefix tailTrace_3249354
  have hstable : (prefixWord ++ tailWord_3249354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249354).length < 2 ^ (prefixWord ++ tailWord_3249354).sum := by decide
  have hdescent : baseEnd_3249354 < baseStart_3249354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249411 : List Nat := [1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 3]
def baseStart_3249411 : Nat := 118140960795 + 3249411 * 2 ^ 59
def prefixEnd_3249411 : Nat := 4983230072969 + 3 ^ 40 * 3249411 * 2
def baseEnd_3249411 : Nat := 1668509687006891398218737

theorem tailTrace_3249411 : CollatzResearch.WordTrace tailWord_3249411 prefixEnd_3249411 1668509687006891398218737 := by
  unfold tailWord_3249411
  simp only [CollatzResearch.WordTrace]
  refine ⟨118515755630946377061668087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79010503753964251374445391 118515755630946377061668087)
  ·
    refine ⟨177773633446419565592502131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118515755630946377061668087 177773633446419565592502131)
    ·
      refine ⟨266660450169629348388753197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177773633446419565592502131 266660450169629348388753197)
      ·
        refine ⟨99997668813611005645782449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266660450169629348388753197 99997668813611005645782449)
        ·
          refine ⟨74998251610208254234336837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99997668813611005645782449 74998251610208254234336837)
          ·
            refine ⟨14062172176914047668938157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74998251610208254234336837 14062172176914047668938157)
            ·
              refine ⟨5273314566342767875851809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14062172176914047668938157 5273314566342767875851809)
              ·
                refine ⟨3954985924757075906888857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273314566342767875851809 3954985924757075906888857)
                ·
                  refine ⟨2966239443567806930166643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3954985924757075906888857 2966239443567806930166643)
                  ·
                    refine ⟨4449359165351710395249965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2966239443567806930166643 4449359165351710395249965)
                    ·
                      refine ⟨1668509687006891398218737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449359165351710395249965 1668509687006891398218737)
                      ·
                        rfl

theorem cell23_3249411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 3].length) (baseStart_3249411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249411 prefixEnd_3249411 := by exact prefixLift 3249411
  have htrace : WordTrace (prefixWord ++ tailWord_3249411) baseStart_3249411 baseEnd_3249411 := by
    simpa [prefixWord, tailWord_3249411, baseEnd_3249411] using wordTrace_append hprefix tailTrace_3249411
  have hstable : (prefixWord ++ tailWord_3249411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249411).length < 2 ^ (prefixWord ++ tailWord_3249411).sum := by decide
  have hdescent : baseEnd_3249411 < baseStart_3249411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249504 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 2, 5]
def baseStart_3249504 : Nat := 118140960795 + 3249504 * 2 ^ 59
def prefixEnd_3249504 : Nat := 4983230072969 + 3 ^ 40 * 3249504 * 2
def baseEnd_3249504 : Nat := 556185813569253178118603

theorem tailTrace_3249504 : CollatzResearch.WordTrace tailWord_3249504 prefixEnd_3249504 556185813569253178118603 := by
  unfold tailWord_3249504
  simp only [CollatzResearch.WordTrace]
  refine ⟨59259573809804726972401783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79012765079739635963202377 59259573809804726972401783)
  ·
    refine ⟨88889360714707090458602675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59259573809804726972401783 88889360714707090458602675)
    ·
      refine ⟨133334041072060635687904013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88889360714707090458602675 133334041072060635687904013)
      ·
        refine ⟨50000265402022738382964005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133334041072060635687904013 50000265402022738382964005)
        ·
          refine ⟨9375049762879263446805751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50000265402022738382964005 9375049762879263446805751)
          ·
            refine ⟨14062574644318895170208627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375049762879263446805751 14062574644318895170208627)
            ·
              refine ⟨21093861966478342755312941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14062574644318895170208627 21093861966478342755312941)
              ·
                refine ⟨7910198237429378533242353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21093861966478342755312941 7910198237429378533242353)
                ·
                  refine ⟨5932648678072033899931765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7910198237429378533242353 5932648678072033899931765)
                  ·
                    refine ⟨556185813569253178118603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5932648678072033899931765 556185813569253178118603)
                    ·
                      rfl

theorem cell23_3249504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_3249504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249504 prefixEnd_3249504 := by exact prefixLift 3249504
  have htrace : WordTrace (prefixWord ++ tailWord_3249504) baseStart_3249504 baseEnd_3249504 := by
    simpa [prefixWord, tailWord_3249504, baseEnd_3249504] using wordTrace_append hprefix tailTrace_3249504
  have hstable : (prefixWord ++ tailWord_3249504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249504).length < 2 ^ (prefixWord ++ tailWord_3249504).sum := by decide
  have hdescent : baseEnd_3249504 < baseStart_3249504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249525 : List Nat := [1, 3, 4, 1, 3, 2, 2, 2, 5]
def baseStart_3249525 : Nat := 118140960795 + 3249525 * 2 ^ 59
def prefixEnd_3249525 : Nat := 4983230072969 + 3 ^ 40 * 3249525 * 2
def baseEnd_3249525 : Nat := 185396469311278216910357

theorem tailTrace_3249525 : CollatzResearch.WordTrace tailWord_3249525 prefixEnd_3249525 185396469311278216910357 := by
  unfold tailWord_3249525
  simp only [CollatzResearch.WordTrace]
  refine ⟨118519913552533374531318029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79013275701688916354212019 118519913552533374531318029)
  ·
    refine ⟨44444967582200015449244261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118519913552533374531318029 44444967582200015449244261)
    ·
      refine ⟨8333431421662502896733299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44444967582200015449244261 8333431421662502896733299)
      ·
        refine ⟨12500147132493754345099949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333431421662502896733299 12500147132493754345099949)
        ·
          refine ⟨4687555174685157879412481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12500147132493754345099949 4687555174685157879412481)
          ·
            refine ⟨3515666381013868409559361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687555174685157879412481 3515666381013868409559361)
            ·
              refine ⟨2636749785760401307169521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515666381013868409559361 2636749785760401307169521)
              ·
                refine ⟨1977562339320300980377141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2636749785760401307169521 1977562339320300980377141)
                ·
                  refine ⟨185396469311278216910357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1977562339320300980377141 185396469311278216910357)
                  ·
                    rfl

theorem cell23_3249525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 2, 2, 5].length) (baseStart_3249525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249525 prefixEnd_3249525 := by exact prefixLift 3249525
  have htrace : WordTrace (prefixWord ++ tailWord_3249525) baseStart_3249525 baseEnd_3249525 := by
    simpa [prefixWord, tailWord_3249525, baseEnd_3249525] using wordTrace_append hprefix tailTrace_3249525
  have hstable : (prefixWord ++ tailWord_3249525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249525).length < 2 ^ (prefixWord ++ tailWord_3249525).sum := by decide
  have hdescent : baseEnd_3249525 < baseStart_3249525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249527 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5]
def baseStart_3249527 : Nat := 118140960795 + 3249527 * 2 ^ 59
def prefixEnd_3249527 : Nat := 4983230072969 + 3 ^ 40 * 3249527 * 2
def baseEnd_3249527 : Nat := 1668569250762812944368203

theorem tailTrace_3249527 : CollatzResearch.WordTrace tailWord_3249527 prefixEnd_3249527 1668569250762812944368203 := by
  unfold tailWord_3249527
  simp only [CollatzResearch.WordTrace]
  refine ⟨118519986498526128872890835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79013324332350752581927223 118519986498526128872890835)
  ·
    refine ⟨177779979747789193309336253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118519986498526128872890835 177779979747789193309336253)
    ·
      refine ⟨66667492405420947491001095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177779979747789193309336253 66667492405420947491001095)
      ·
        refine ⟨100001238608131421236501643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66667492405420947491001095 100001238608131421236501643)
        ·
          refine ⟨150001857912197131854752465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100001238608131421236501643 150001857912197131854752465)
          ·
            refine ⟨112501393434147848891064349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150001857912197131854752465 112501393434147848891064349)
            ·
              refine ⟨42188022537805443334149131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112501393434147848891064349 42188022537805443334149131)
              ·
                refine ⟨63282033806708165001223697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42188022537805443334149131 63282033806708165001223697)
                ·
                  refine ⟨47461525355031123750917773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63282033806708165001223697 47461525355031123750917773)
                  ·
                    refine ⟨17798072008136671406594165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47461525355031123750917773 17798072008136671406594165)
                    ·
                      refine ⟨1668569250762812944368203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17798072008136671406594165 1668569250762812944368203)
                      ·
                        rfl

theorem cell23_3249527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_3249527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249527 prefixEnd_3249527 := by exact prefixLift 3249527
  have htrace : WordTrace (prefixWord ++ tailWord_3249527) baseStart_3249527 baseEnd_3249527 := by
    simpa [prefixWord, tailWord_3249527, baseEnd_3249527] using wordTrace_append hprefix tailTrace_3249527
  have hstable : (prefixWord ++ tailWord_3249527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249527).length < 2 ^ (prefixWord ++ tailWord_3249527).sum := by decide
  have hdescent : baseEnd_3249527 < baseStart_3249527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249561 : List Nat := [1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_3249561 : Nat := 118140960795 + 3249561 * 2 ^ 59
def prefixEnd_3249561 : Nat := 4983230072969 + 3 ^ 40 * 3249561 * 2
def baseEnd_3249561 : Nat := 1668586709105065811343047

theorem tailTrace_3249561 : CollatzResearch.WordTrace tailWord_3249561 prefixEnd_3249561 1668586709105065811343047 := by
  unfold tailWord_3249561
  simp only [CollatzResearch.WordTrace]
  refine ⟨118521226580402952679628537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79014151053601968453085691 118521226580402952679628537)
  ·
    refine ⟨88890919935302214509721403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118521226580402952679628537 88890919935302214509721403)
    ·
      refine ⟨133336379902953321764582105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88890919935302214509721403 133336379902953321764582105)
      ·
        refine ⟨100002284927214991323436579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133336379902953321764582105 100002284927214991323436579)
        ·
          refine ⟨150003427390822486985154869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100002284927214991323436579 150003427390822486985154869)
          ·
            refine ⟨14062821317889608154858269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150003427390822486985154869 14062821317889608154858269)
            ·
              refine ⟨5273557994208603058071851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14062821317889608154858269 5273557994208603058071851)
              ·
                refine ⟨7910336991312904587107777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273557994208603058071851 7910336991312904587107777)
                ·
                  refine ⟨5932752743484678440330833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7910336991312904587107777 5932752743484678440330833)
                  ·
                    refine ⟨4449564557613508830248125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5932752743484678440330833 4449564557613508830248125)
                    ·
                      refine ⟨1668586709105065811343047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449564557613508830248125 1668586709105065811343047)
                      ·
                        rfl

theorem cell23_3249561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_3249561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249561 prefixEnd_3249561 := by exact prefixLift 3249561
  have htrace : WordTrace (prefixWord ++ tailWord_3249561) baseStart_3249561 baseEnd_3249561 := by
    simpa [prefixWord, tailWord_3249561, baseEnd_3249561] using wordTrace_append hprefix tailTrace_3249561
  have hstable : (prefixWord ++ tailWord_3249561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249561).length < 2 ^ (prefixWord ++ tailWord_3249561).sum := by decide
  have hdescent : baseEnd_3249561 < baseStart_3249561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249568 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 1, 4]
def baseStart_3249568 : Nat := 118140960795 + 3249568 * 2 ^ 59
def prefixEnd_3249568 : Nat := 4983230072969 + 3 ^ 40 * 3249568 * 2
def baseEnd_3249568 : Nat := 556196767823215761318505

theorem tailTrace_3249568 : CollatzResearch.WordTrace tailWord_3249568 prefixEnd_3249568 556196767823215761318505 := by
  unfold tailWord_3249568
  simp only [CollatzResearch.WordTrace]
  refine ⟨59260740945688796437566679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79014321260918395250088905 59260740945688796437566679)
  ·
    refine ⟨88891111418533194656350019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59260740945688796437566679 88891111418533194656350019)
    ·
      refine ⟨133336667127799791984525029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88891111418533194656350019 133336667127799791984525029)
      ·
        refine ⟨25000625086462460997098443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133336667127799791984525029 25000625086462460997098443)
        ·
          refine ⟨37500937629693691495647665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25000625086462460997098443 37500937629693691495647665)
          ·
            refine ⟨28125703222270268621735749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37500937629693691495647665 28125703222270268621735749)
            ·
              refine ⟨5273569354175675366575453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28125703222270268621735749 5273569354175675366575453)
              ·
                refine ⟨1977588507815878262465795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5273569354175675366575453 1977588507815878262465795)
                ·
                  refine ⟨2966382761723817393698693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977588507815878262465795 2966382761723817393698693)
                  ·
                    refine ⟨556196767823215761318505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966382761723817393698693 556196767823215761318505)
                    ·
                      rfl

theorem cell23_3249568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 4].length) (baseStart_3249568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249568 prefixEnd_3249568 := by exact prefixLift 3249568
  have htrace : WordTrace (prefixWord ++ tailWord_3249568) baseStart_3249568 baseEnd_3249568 := by
    simpa [prefixWord, tailWord_3249568, baseEnd_3249568] using wordTrace_append hprefix tailTrace_3249568
  have hstable : (prefixWord ++ tailWord_3249568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249568).length < 2 ^ (prefixWord ++ tailWord_3249568).sum := by decide
  have hdescent : baseEnd_3249568 < baseStart_3249568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249581 : List Nat := [1, 5, 2, 2, 1, 2, 1, 1, 8]
def baseStart_3249581 : Nat := 118140960795 + 3249581 * 2 ^ 59
def prefixEnd_3249581 : Nat := 4983230072969 + 3 ^ 40 * 3249581 * 2
def baseEnd_3249581 : Nat := 185399664302017303676995

theorem tailTrace_3249581 : CollatzResearch.WordTrace tailWord_3249581 prefixEnd_3249581 185399664302017303676995 := by
  unfold tailWord_3249581
  simp only [CollatzResearch.WordTrace]
  refine ⟨118521956040330496095356597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79014637360220330730237731 118521956040330496095356597)
  ·
    refine ⟨11111433378780984008939681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118521956040330496095356597 11111433378780984008939681)
    ·
      refine ⟨8333575034085738006704761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11111433378780984008939681 8333575034085738006704761)
      ·
        refine ⟨6250181275564303505028571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8333575034085738006704761 6250181275564303505028571)
        ·
          refine ⟨9375271913346455257542857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250181275564303505028571 9375271913346455257542857)
          ·
            refine ⟨7031453935009841443157143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9375271913346455257542857 7031453935009841443157143)
            ·
              refine ⟨10547180902514762164735715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031453935009841443157143 10547180902514762164735715)
              ·
                refine ⟨15820771353772143247103573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547180902514762164735715 15820771353772143247103573)
                ·
                  refine ⟨185399664302017303676995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15820771353772143247103573 185399664302017303676995)
                  ·
                    rfl

theorem cell23_3249581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_3249581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249581 prefixEnd_3249581 := by exact prefixLift 3249581
  have htrace : WordTrace (prefixWord ++ tailWord_3249581) baseStart_3249581 baseEnd_3249581 := by
    simpa [prefixWord, tailWord_3249581, baseEnd_3249581] using wordTrace_append hprefix tailTrace_3249581
  have hstable : (prefixWord ++ tailWord_3249581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249581).length < 2 ^ (prefixWord ++ tailWord_3249581).sum := by decide
  have hdescent : baseEnd_3249581 < baseStart_3249581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249624 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 1, 6]
def baseStart_3249624 : Nat := 118140960795 + 3249624 * 2 ^ 59
def prefixEnd_3249624 : Nat := 4983230072969 + 3 ^ 40 * 3249624 * 2
def baseEnd_3249624 : Nat := 556206352795433021618419

theorem tailTrace_3249624 : CollatzResearch.WordTrace tailWord_3249624 prefixEnd_3249624 556206352795433021618419 := by
  unfold tailWord_3249624
  simp only [CollatzResearch.WordTrace]
  refine ⟨59261762189587357219585963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79015682919449809626114617 59261762189587357219585963)
  ·
    refine ⟨88892643284381035829378945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59261762189587357219585963 88892643284381035829378945)
    ·
      refine ⟨66669482463285776872034209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88892643284381035829378945 66669482463285776872034209)
      ·
        refine ⟨50002111847464332654025657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66669482463285776872034209 50002111847464332654025657)
        ·
          refine ⟨37501583885598249490519243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50002111847464332654025657 37501583885598249490519243)
          ·
            refine ⟨56252375828397374235778865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37501583885598249490519243 56252375828397374235778865)
            ·
              refine ⟨42189281871298030676834149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56252375828397374235778865 42189281871298030676834149)
              ·
                refine ⟨7910490350868380751906403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42189281871298030676834149 7910490350868380751906403)
                ·
                  refine ⟨11865735526302571127859605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910490350868380751906403 11865735526302571127859605)
                  ·
                    refine ⟨556206352795433021618419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11865735526302571127859605 556206352795433021618419)
                    ·
                      rfl

theorem cell23_3249624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_3249624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249624 prefixEnd_3249624 := by exact prefixLift 3249624
  have htrace : WordTrace (prefixWord ++ tailWord_3249624) baseStart_3249624 baseEnd_3249624 := by
    simpa [prefixWord, tailWord_3249624, baseEnd_3249624] using wordTrace_append hprefix tailTrace_3249624
  have hstable : (prefixWord ++ tailWord_3249624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249624).length < 2 ^ (prefixWord ++ tailWord_3249624).sum := by decide
  have hdescent : baseEnd_3249624 < baseStart_3249624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249625 : List Nat := [1, 2, 1, 2, 4, 2, 3, 3, 1, 1, 3]
def baseStart_3249625 : Nat := 118140960795 + 3249625 * 2 ^ 59
def prefixEnd_3249625 : Nat := 4983230072969 + 3 ^ 40 * 3249625 * 2
def baseEnd_3249625 : Nat := 1668619571866953560942753

theorem tailTrace_3249625 : CollatzResearch.WordTrace tailWord_3249625 prefixEnd_3249625 1668619571866953560942753 := by
  unfold tailWord_3249625
  simp only [CollatzResearch.WordTrace]
  refine ⟨118523560852171091609958329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79015707234780727739972219 118523560852171091609958329)
  ·
    refine ⟨88892670639128318707468747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118523560852171091609958329 88892670639128318707468747)
    ·
      refine ⟨133339005958692478061203121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88892670639128318707468747 133339005958692478061203121)
      ·
        refine ⟨100004254469019358545902341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133339005958692478061203121 100004254469019358545902341)
        ·
          refine ⟨18750797712941129727356689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100004254469019358545902341 18750797712941129727356689)
          ·
            refine ⟨14063098284705847295517517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18750797712941129727356689 14063098284705847295517517)
            ·
              refine ⟨5273661856764692735819069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14063098284705847295517517 5273661856764692735819069)
              ·
                refine ⟨1977623196286759775932151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5273661856764692735819069 1977623196286759775932151)
                ·
                  refine ⟨2966434794430139663898227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977623196286759775932151 2966434794430139663898227)
                  ·
                    refine ⟨4449652191645209495847341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2966434794430139663898227 4449652191645209495847341)
                    ·
                      refine ⟨1668619571866953560942753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449652191645209495847341 1668619571866953560942753)
                      ·
                        rfl

theorem cell23_3249625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_3249625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249625 prefixEnd_3249625 := by exact prefixLift 3249625
  have htrace : WordTrace (prefixWord ++ tailWord_3249625) baseStart_3249625 baseEnd_3249625 := by
    simpa [prefixWord, tailWord_3249625, baseEnd_3249625] using wordTrace_append hprefix tailTrace_3249625
  have hstable : (prefixWord ++ tailWord_3249625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249625).length < 2 ^ (prefixWord ++ tailWord_3249625).sum := by decide
  have hdescent : baseEnd_3249625 < baseStart_3249625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249631 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 4]
def baseStart_3249631 : Nat := 118140960795 + 3249631 * 2 ^ 59
def prefixEnd_3249631 : Nat := 4983230072969 + 3 ^ 40 * 3249631 * 2
def baseEnd_3249631 : Nat := 1668622652750880537467725

theorem tailTrace_3249631 : CollatzResearch.WordTrace tailWord_3249631 prefixEnd_3249631 1668622652750880537467725 := by
  unfold tailWord_3249631
  simp only [CollatzResearch.WordTrace]
  refine ⟨118523779690149354634676747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79015853126766236423117831 118523779690149354634676747)
  ·
    refine ⟨177785669535224031952015121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118523779690149354634676747 177785669535224031952015121)
    ·
      refine ⟨133339252151418023964011341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177785669535224031952015121 133339252151418023964011341)
      ·
        refine ⟨50002219556781758986504253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133339252151418023964011341 50002219556781758986504253)
        ·
          refine ⟨18750832333793159619939095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50002219556781758986504253 18750832333793159619939095)
          ·
            refine ⟨28126248500689739429908643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18750832333793159619939095 28126248500689739429908643)
            ·
              refine ⟨42189372751034609144862965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28126248500689739429908643 42189372751034609144862965)
              ·
                refine ⟨3955253695409494607330903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42189372751034609144862965 3955253695409494607330903)
                ·
                  refine ⟨5932880543114241910996355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955253695409494607330903 5932880543114241910996355)
                  ·
                    refine ⟨8899320814671362866494533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5932880543114241910996355 8899320814671362866494533)
                    ·
                      refine ⟨1668622652750880537467725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8899320814671362866494533 1668622652750880537467725)
                      ·
                        rfl

theorem cell23_3249631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_3249631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249631 prefixEnd_3249631 := by exact prefixLift 3249631
  have htrace : WordTrace (prefixWord ++ tailWord_3249631) baseStart_3249631 baseEnd_3249631 := by
    simpa [prefixWord, tailWord_3249631, baseEnd_3249631] using wordTrace_append hprefix tailTrace_3249631
  have hstable : (prefixWord ++ tailWord_3249631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249631).length < 2 ^ (prefixWord ++ tailWord_3249631).sum := by decide
  have hdescent : baseEnd_3249631 < baseStart_3249631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249642 : List Nat := [3, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3]
def baseStart_3249642 : Nat := 118140960795 + 3249642 * 2 ^ 59
def prefixEnd_3249642 : Nat := 4983230072969 + 3 ^ 40 * 3249642 * 2
def baseEnd_3249642 : Nat := 1668628301038079994430175

theorem tailTrace_3249642 : CollatzResearch.WordTrace tailWord_3249642 prefixEnd_3249642 1668628301038079994430175 := by
  unfold tailWord_3249642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631045223277375878331795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79016120595406335675551453 29631045223277375878331795)
  ·
    refine ⟨44446567834916063817497693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29631045223277375878331795 44446567834916063817497693)
    ·
      refine ⟨16667462938093523931561635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44446567834916063817497693 16667462938093523931561635)
      ·
        refine ⟨25001194407140285897342453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667462938093523931561635 25001194407140285897342453)
        ·
          refine ⟨2343861975669401802875855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25001194407140285897342453 2343861975669401802875855)
          ·
            refine ⟨3515792963504102704313783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343861975669401802875855 3515792963504102704313783)
            ·
              refine ⟨5273689445256154056470675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515792963504102704313783 5273689445256154056470675)
              ·
                refine ⟨7910534167884231084706013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273689445256154056470675 7910534167884231084706013)
                ·
                  refine ⟨2966450312956586656764755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7910534167884231084706013 2966450312956586656764755)
                  ·
                    refine ⟨4449675469434879985147133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2966450312956586656764755 4449675469434879985147133)
                    ·
                      refine ⟨1668628301038079994430175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449675469434879985147133 1668628301038079994430175)
                      ·
                        rfl

theorem cell23_3249642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_3249642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249642 prefixEnd_3249642 := by exact prefixLift 3249642
  have htrace : WordTrace (prefixWord ++ tailWord_3249642) baseStart_3249642 baseEnd_3249642 := by
    simpa [prefixWord, tailWord_3249642, baseEnd_3249642] using wordTrace_append hprefix tailTrace_3249642
  have hstable : (prefixWord ++ tailWord_3249642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249642).length < 2 ^ (prefixWord ++ tailWord_3249642).sum := by decide
  have hdescent : baseEnd_3249642 < baseStart_3249642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249644 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 4]
def baseStart_3249644 : Nat := 118140960795 + 3249644 * 2 ^ 59
def prefixEnd_3249644 : Nat := 4983230072969 + 3 ^ 40 * 3249644 * 2
def baseEnd_3249644 : Nat := 1668629327999388986605165

theorem tailTrace_3249644 : CollatzResearch.WordTrace tailWord_3249644 prefixEnd_3249644 1668629327999388986605165 := by
  unfold tailWord_3249644
  simp only [CollatzResearch.WordTrace]
  refine ⟨59262126919551128927449993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79016169226068171903266657 59262126919551128927449993)
  ·
    refine ⟨44446595189663346695587495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59262126919551128927449993 44446595189663346695587495)
    ·
      refine ⟨66669892784495020043381243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44446595189663346695587495 66669892784495020043381243)
      ·
        refine ⟨100004839176742530065071865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66669892784495020043381243 100004839176742530065071865)
        ·
          refine ⟨75003629382556897548803899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100004839176742530065071865 75003629382556897548803899)
          ·
            refine ⟨112505444073835346323205849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75003629382556897548803899 112505444073835346323205849)
            ·
              refine ⟨84379083055376509742404387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112505444073835346323205849 84379083055376509742404387)
              ·
                refine ⟨126568624583064764613606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84379083055376509742404387 126568624583064764613606581)
                ·
                  refine ⟨11865808554662321682525617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126568624583064764613606581 11865808554662321682525617)
                  ·
                    refine ⟨8899356415996741261894213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11865808554662321682525617 8899356415996741261894213)
                    ·
                      refine ⟨1668629327999388986605165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8899356415996741261894213 1668629327999388986605165)
                      ·
                        rfl

theorem cell23_3249644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 4].length) (baseStart_3249644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249644 prefixEnd_3249644 := by exact prefixLift 3249644
  have htrace : WordTrace (prefixWord ++ tailWord_3249644) baseStart_3249644 baseEnd_3249644 := by
    simpa [prefixWord, tailWord_3249644, baseEnd_3249644] using wordTrace_append hprefix tailTrace_3249644
  have hstable : (prefixWord ++ tailWord_3249644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249644).length < 2 ^ (prefixWord ++ tailWord_3249644).sum := by decide
  have hdescent : baseEnd_3249644 < baseStart_3249644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249662 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3249662 : Nat := 118140960795 + 3249662 * 2 ^ 59
def prefixEnd_3249662 : Nat := 4983230072969 + 3 ^ 40 * 3249662 * 2
def baseEnd_3249662 : Nat := 556212856883723305393361

theorem tailTrace_3249662 : CollatzResearch.WordTrace tailWord_3249662 prefixEnd_3249662 556212856883723305393361 := by
  unfold tailWord_3249662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815613794129630866131905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79016606902024697952703493 14815613794129630866131905)
  ·
    refine ⟨11111710345597223149598929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14815613794129630866131905 11111710345597223149598929)
    ·
      refine ⟨8333782759197917362199197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11111710345597223149598929 8333782759197917362199197)
      ·
        refine ⟨3125168534699219010824699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8333782759197917362199197 3125168534699219010824699)
        ·
          refine ⟨4687752802048828516237049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125168534699219010824699 4687752802048828516237049)
          ·
            refine ⟨3515814601536621387177787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687752802048828516237049 3515814601536621387177787)
            ·
              refine ⟨5273721902304932080766681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515814601536621387177787 5273721902304932080766681)
              ·
                refine ⟨3955291426728699060575011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273721902304932080766681 3955291426728699060575011)
                ·
                  refine ⟨5932937140093048590862517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955291426728699060575011 5932937140093048590862517)
                  ·
                    refine ⟨556212856883723305393361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5932937140093048590862517 556212856883723305393361)
                    ·
                      rfl

theorem cell23_3249662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3249662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249662 prefixEnd_3249662 := by exact prefixLift 3249662
  have htrace : WordTrace (prefixWord ++ tailWord_3249662) baseStart_3249662 baseEnd_3249662 := by
    simpa [prefixWord, tailWord_3249662, baseEnd_3249662] using wordTrace_append hprefix tailTrace_3249662
  have hstable : (prefixWord ++ tailWord_3249662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249662).length < 2 ^ (prefixWord ++ tailWord_3249662).sum := by decide
  have hdescent : baseEnd_3249662 < baseStart_3249662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249665 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3249665 : Nat := 118140960795 + 3249665 * 2 ^ 59
def prefixEnd_3249665 : Nat := 4983230072969 + 3 ^ 40 * 3249665 * 2
def baseEnd_3249665 : Nat := 1668640111093133404442569

theorem tailTrace_3249665 : CollatzResearch.WordTrace tailWord_3249665 prefixEnd_3249665 1668640111093133404442569 := by
  unfold tailWord_3249665
  simp only [CollatzResearch.WordTrace]
  refine ⟨118525019772026178441414449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79016679848017452294276299 118525019772026178441414449)
  ·
    refine ⟨88893764829019633831060837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118525019772026178441414449 88893764829019633831060837)
    ·
      refine ⟨16667580905441181343323907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88893764829019633831060837 16667580905441181343323907)
      ·
        refine ⟨25001371358161772014985861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667580905441181343323907 25001371358161772014985861)
        ·
          refine ⟨4687757129655332252809849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25001371358161772014985861 4687757129655332252809849)
          ·
            refine ⟨3515817847241499189607387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4687757129655332252809849 3515817847241499189607387)
            ·
              refine ⟨5273726770862248784411081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515817847241499189607387 5273726770862248784411081)
              ·
                refine ⟨3955295078146686588308311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5273726770862248784411081 3955295078146686588308311)
                ·
                  refine ⟨5932942617220029882462467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955295078146686588308311 5932942617220029882462467)
                  ·
                    refine ⟨8899413925830044823693701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5932942617220029882462467 8899413925830044823693701)
                    ·
                      refine ⟨1668640111093133404442569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8899413925830044823693701 1668640111093133404442569)
                      ·
                        rfl

theorem cell23_3249665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3249665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249665 prefixEnd_3249665 := by exact prefixLift 3249665
  have htrace : WordTrace (prefixWord ++ tailWord_3249665) baseStart_3249665 baseEnd_3249665 := by
    simpa [prefixWord, tailWord_3249665, baseEnd_3249665] using wordTrace_append hprefix tailTrace_3249665
  have hstable : (prefixWord ++ tailWord_3249665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249665).length < 2 ^ (prefixWord ++ tailWord_3249665).sum := by decide
  have hdescent : baseEnd_3249665 < baseStart_3249665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249678 : List Nat := [4, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3249678 : Nat := 118140960795 + 3249678 * 2 ^ 59
def prefixEnd_3249678 : Nat := 4983230072969 + 3 ^ 40 * 3249678 * 2
def baseEnd_3249678 : Nat := 1668646786341641853580009

theorem tailTrace_3249678 : CollatzResearch.WordTrace tailWord_3249678 prefixEnd_3249678 1668646786341641853580009 := by
  unfold tailWord_3249678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14815686740122385207704711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79016995947319387774425125 14815686740122385207704711)
  ·
    refine ⟨22223530110183577811557067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14815686740122385207704711 22223530110183577811557067)
    ·
      refine ⟨33335295165275366717335601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22223530110183577811557067 33335295165275366717335601)
      ·
        refine ⟨25001471373956525038001701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33335295165275366717335601 25001471373956525038001701)
        ·
          refine ⟨4687775882616848444625319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25001471373956525038001701 4687775882616848444625319)
          ·
            refine ⟨7031663823925272666937979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687775882616848444625319 7031663823925272666937979)
            ·
              refine ⟨10547495735887909000406969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031663823925272666937979 10547495735887909000406969)
              ·
                refine ⟨7910621801915931750305227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10547495735887909000406969 7910621801915931750305227)
                ·
                  refine ⟨11865932702873897625457841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910621801915931750305227 11865932702873897625457841)
                  ·
                    refine ⟨8899449527155423219093381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11865932702873897625457841 8899449527155423219093381)
                    ·
                      refine ⟨1668646786341641853580009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8899449527155423219093381 1668646786341641853580009)
                      ·
                        rfl

theorem cell23_3249678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3249678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249678 prefixEnd_3249678 := by exact prefixLift 3249678
  have htrace : WordTrace (prefixWord ++ tailWord_3249678) baseStart_3249678 baseEnd_3249678 := by
    simpa [prefixWord, tailWord_3249678, baseEnd_3249678] using wordTrace_append hprefix tailTrace_3249678
  have hstable : (prefixWord ++ tailWord_3249678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249678).length < 2 ^ (prefixWord ++ tailWord_3249678).sum := by decide
  have hdescent : baseEnd_3249678 < baseStart_3249678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249681 : List Nat := [1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_3249681 : Nat := 118140960795 + 3249681 * 2 ^ 59
def prefixEnd_3249681 : Nat := 4983230072969 + 3 ^ 40 * 3249681 * 2
def baseEnd_3249681 : Nat := 1668648326783605341842495

theorem tailTrace_3249681 : CollatzResearch.WordTrace tailWord_3249681 prefixEnd_3249681 1668648326783605341842495 := by
  unfold tailWord_3249681
  simp only [CollatzResearch.WordTrace]
  refine ⟨118525603339968213173996897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79017068893312142115997931 118525603339968213173996897)
  ·
    refine ⟨88894202504976159880497673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118525603339968213173996897 88894202504976159880497673)
    ·
      refine ⟨66670651878732119910373255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88894202504976159880497673 66670651878732119910373255)
      ·
        refine ⟨100005977818098179865559883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66670651878732119910373255 100005977818098179865559883)
        ·
          refine ⟨150008966727147269798339825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100005977818098179865559883 150008966727147269798339825)
          ·
            refine ⟨112506725045360452348754869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150008966727147269798339825 112506725045360452348754869)
            ·
              refine ⟨10547505473002542407695769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112506725045360452348754869 10547505473002542407695769)
              ·
                refine ⟨7910629104751906805771827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10547505473002542407695769 7910629104751906805771827)
                ·
                  refine ⟨11865943657127860208657741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910629104751906805771827 11865943657127860208657741)
                  ·
                    refine ⟨4449728871422947578246653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11865943657127860208657741 4449728871422947578246653)
                    ·
                      refine ⟨1668648326783605341842495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449728871422947578246653 1668648326783605341842495)
                      ·
                        rfl

theorem cell23_3249681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_3249681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249681 prefixEnd_3249681 := by exact prefixLift 3249681
  have htrace : WordTrace (prefixWord ++ tailWord_3249681) baseStart_3249681 baseEnd_3249681 := by
    simpa [prefixWord, tailWord_3249681, baseEnd_3249681] using wordTrace_append hprefix tailTrace_3249681
  have hstable : (prefixWord ++ tailWord_3249681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249681).length < 2 ^ (prefixWord ++ tailWord_3249681).sum := by decide
  have hdescent : baseEnd_3249681 < baseStart_3249681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249685 : List Nat := [1, 3, 2, 1, 3, 3, 3, 1, 1, 2, 3]
def baseStart_3249685 : Nat := 118140960795 + 3249685 * 2 ^ 59
def prefixEnd_3249685 : Nat := 4983230072969 + 3 ^ 40 * 3249685 * 2
def baseEnd_3249685 : Nat := 1668650380706223326192477

theorem tailTrace_3249685 : CollatzResearch.WordTrace tailWord_3249685 prefixEnd_3249685 1668650380706223326192477 := by
  unfold tailWord_3249685
  simp only [CollatzResearch.WordTrace]
  refine ⟨118525749231953721857142509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79017166154635814571428339 118525749231953721857142509)
  ·
    refine ⟨44447155961982645696428441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118525749231953721857142509 44447155961982645696428441)
    ·
      refine ⟨33335366971486984272321331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44447155961982645696428441 33335366971486984272321331)
      ·
        refine ⟨50003050457230476408481997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33335366971486984272321331 50003050457230476408481997)
        ·
          refine ⟨18751143921461428653180749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50003050457230476408481997 18751143921461428653180749)
          ·
            refine ⟨7031678970548035744942781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18751143921461428653180749 7031678970548035744942781)
            ·
              refine ⟨2636879613955513404353543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7031678970548035744942781 2636879613955513404353543)
              ·
                refine ⟨3955319420933270106530315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636879613955513404353543 3955319420933270106530315)
                ·
                  refine ⟨5932979131399905159795473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955319420933270106530315 5932979131399905159795473)
                  ·
                    refine ⟨4449734348549928869846605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5932979131399905159795473 4449734348549928869846605)
                    ·
                      refine ⟨1668650380706223326192477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449734348549928869846605 1668650380706223326192477)
                      ·
                        rfl

theorem cell23_3249685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_3249685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249685 prefixEnd_3249685 := by exact prefixLift 3249685
  have htrace : WordTrace (prefixWord ++ tailWord_3249685) baseStart_3249685 baseEnd_3249685 := by
    simpa [prefixWord, tailWord_3249685, baseEnd_3249685] using wordTrace_append hprefix tailTrace_3249685
  have hstable : (prefixWord ++ tailWord_3249685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249685).length < 2 ^ (prefixWord ++ tailWord_3249685).sum := by decide
  have hdescent : baseEnd_3249685 < baseStart_3249685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249698 : List Nat := [3, 3, 1, 1, 1, 1, 2, 3, 4, 1, 3]
def baseStart_3249698 : Nat := 118140960795 + 3249698 * 2 ^ 59
def prefixEnd_3249698 : Nat := 4983230072969 + 3 ^ 40 * 3249698 * 2
def baseEnd_3249698 : Nat := 1668657055954731775329917

theorem tailTrace_3249698 : CollatzResearch.WordTrace tailWord_3249698 prefixEnd_3249698 1668657055954731775329917 := by
  unfold tailWord_3249698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631555845226656269341437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79017482253937750051577165 29631555845226656269341437)
  ·
    refine ⟨11111833441959996101003039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29631555845226656269341437 11111833441959996101003039)
    ·
      refine ⟨16667750162939994151504559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11111833441959996101003039 16667750162939994151504559)
      ·
        refine ⟨25001625244409991227256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16667750162939994151504559 25001625244409991227256839)
        ·
          refine ⟨37502437866614986840885259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25001625244409991227256839 37502437866614986840885259)
          ·
            refine ⟨56253656799922480261327889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37502437866614986840885259 56253656799922480261327889)
            ·
              refine ⟨42190242599941860195995917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56253656799922480261327889 42190242599941860195995917)
              ·
                refine ⟨15821340974978197573498469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42190242599941860195995917 15821340974978197573498469)
                ·
                  refine ⟨2966501432808412045030963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15821340974978197573498469 2966501432808412045030963)
                  ·
                    refine ⟨4449752149212618067546445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2966501432808412045030963 4449752149212618067546445)
                    ·
                      refine ⟨1668657055954731775329917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4449752149212618067546445 1668657055954731775329917)
                      ·
                        rfl

theorem cell23_3249698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_3249698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249698 prefixEnd_3249698 := by exact prefixLift 3249698
  have htrace : WordTrace (prefixWord ++ tailWord_3249698) baseStart_3249698 baseEnd_3249698 := by
    simpa [prefixWord, tailWord_3249698, baseEnd_3249698] using wordTrace_append hprefix tailTrace_3249698
  have hstable : (prefixWord ++ tailWord_3249698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249698).length < 2 ^ (prefixWord ++ tailWord_3249698).sum := by decide
  have hdescent : baseEnd_3249698 < baseStart_3249698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249738 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2]
def baseStart_3249738 : Nat := 118140960795 + 3249738 * 2 ^ 59
def prefixEnd_3249738 : Nat := 4983230072969 + 3 ^ 40 * 3249738 * 2
def baseEnd_3249738 : Nat := 1668677595180911618829733

theorem tailTrace_3249738 : CollatzResearch.WordTrace tailWord_3249738 prefixEnd_3249738 1668677595180911618829733 := by
  unfold tailWord_3249738
  simp only [CollatzResearch.WordTrace]
  refine ⟨29631920575190427977205467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79018454867174474605881245 29631920575190427977205467)
  ·
    refine ⟨44447880862785641965808201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29631920575190427977205467 44447880862785641965808201)
    ·
      refine ⟨33335910647089231474356151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44447880862785641965808201 33335910647089231474356151)
      ·
        refine ⟨50003865970633847211534227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33335910647089231474356151 50003865970633847211534227)
        ·
          refine ⟨75005798955950770817301341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50003865970633847211534227 75005798955950770817301341)
          ·
            refine ⟨28127174608481539056488003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75005798955950770817301341 28127174608481539056488003)
            ·
              refine ⟨42190761912722308584732005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28127174608481539056488003 42190761912722308584732005)
              ·
                refine ⟨7910767858635432859637251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42190761912722308584732005 7910767858635432859637251)
                ·
                  refine ⟨11866151787953149289455877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7910767858635432859637251 11866151787953149289455877)
                  ·
                    refine ⟨2224903460241215491772977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11866151787953149289455877 2224903460241215491772977)
                    ·
                      refine ⟨1668677595180911618829733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224903460241215491772977 1668677595180911618829733)
                      ·
                        rfl

theorem cell23_3249738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_3249738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249738 prefixEnd_3249738 := by exact prefixLift 3249738
  have htrace : WordTrace (prefixWord ++ tailWord_3249738) baseStart_3249738 baseEnd_3249738 := by
    simpa [prefixWord, tailWord_3249738, baseEnd_3249738] using wordTrace_append hprefix tailTrace_3249738
  have hstable : (prefixWord ++ tailWord_3249738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249738).length < 2 ^ (prefixWord ++ tailWord_3249738).sum := by decide
  have hdescent : baseEnd_3249738 < baseStart_3249738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249744 : List Nat := [2, 1, 1, 1, 1, 3, 3, 2, 9]
def baseStart_3249744 : Nat := 118140960795 + 3249744 * 2 ^ 59
def prefixEnd_3249744 : Nat := 4983230072969 + 3 ^ 40 * 3249744 * 2
def baseEnd_3249744 : Nat := 185408964007204288372745

theorem tailTrace_3249744 : CollatzResearch.WordTrace tailWord_3249744 prefixEnd_3249744 185408964007204288372745 := by
  unfold tailWord_3249744
  simp only [CollatzResearch.WordTrace]
  refine ⟨59263950569369987466770143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79018600759159983289026857 59263950569369987466770143)
  ·
    refine ⟨88895925854054981200155215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59263950569369987466770143 88895925854054981200155215)
    ·
      refine ⟨133343888781082471800232823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88895925854054981200155215 133343888781082471800232823)
      ·
        refine ⟨200015833171623707700349235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133343888781082471800232823 200015833171623707700349235)
        ·
          refine ⟨300023749757435561550523853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200015833171623707700349235 300023749757435561550523853)
          ·
            refine ⟨112508906159038335581446445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300023749757435561550523853 112508906159038335581446445)
            ·
              refine ⟨42190839809639375843042417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112508906159038335581446445 42190839809639375843042417)
              ·
                refine ⟨31643129857229531882281813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42190839809639375843042417 31643129857229531882281813)
                ·
                  refine ⟨185408964007204288372745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31643129857229531882281813 185408964007204288372745)
                  ·
                    rfl

theorem cell23_3249744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 9].length) (baseStart_3249744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249744 prefixEnd_3249744 := by exact prefixLift 3249744
  have htrace : WordTrace (prefixWord ++ tailWord_3249744) baseStart_3249744 baseEnd_3249744 := by
    simpa [prefixWord, tailWord_3249744, baseEnd_3249744] using wordTrace_append hprefix tailTrace_3249744
  have hstable : (prefixWord ++ tailWord_3249744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249744).length < 2 ^ (prefixWord ++ tailWord_3249744).sum := by decide
  have hdescent : baseEnd_3249744 < baseStart_3249744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249751 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3249751 : Nat := 118140960795 + 3249751 * 2 ^ 59
def prefixEnd_3249751 : Nat := 4983230072969 + 3 ^ 40 * 3249751 * 2
def baseEnd_3249751 : Nat := 1668684270429420067967173

theorem tailTrace_3249751 : CollatzResearch.WordTrace tailWord_3249751 prefixEnd_3249751 1668684270429420067967173 := by
  unfold tailWord_3249751
  simp only [CollatzResearch.WordTrace]
  refine ⟨118528156449714615129045107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79018770966476410086030071 118528156449714615129045107)
  ·
    refine ⟨177792234674571922693567661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118528156449714615129045107 177792234674571922693567661)
    ·
      refine ⟨66672088002964471010087873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177792234674571922693567661 66672088002964471010087873)
      ·
        refine ⟨50004066002223353257565905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66672088002964471010087873 50004066002223353257565905)
        ·
          refine ⟨37503049501667514943174429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50004066002223353257565905 37503049501667514943174429)
          ·
            refine ⟨14063643563125318103690411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37503049501667514943174429 14063643563125318103690411)
            ·
              refine ⟨21095465344687977155535617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14063643563125318103690411 21095465344687977155535617)
              ·
                refine ⟨15821599008515982866651713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21095465344687977155535617 15821599008515982866651713)
                ·
                  refine ⟨11866199256386987149988785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821599008515982866651713 11866199256386987149988785)
                  ·
                    refine ⟨8899649442290240362491589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11866199256386987149988785 8899649442290240362491589)
                    ·
                      refine ⟨1668684270429420067967173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8899649442290240362491589 1668684270429420067967173)
                      ·
                        rfl

theorem cell23_3249751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3249751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249751 prefixEnd_3249751 := by exact prefixLift 3249751
  have htrace : WordTrace (prefixWord ++ tailWord_3249751) baseStart_3249751 baseEnd_3249751 := by
    simpa [prefixWord, tailWord_3249751, baseEnd_3249751] using wordTrace_append hprefix tailTrace_3249751
  have hstable : (prefixWord ++ tailWord_3249751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249751).length < 2 ^ (prefixWord ++ tailWord_3249751).sum := by decide
  have hdescent : baseEnd_3249751 < baseStart_3249751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249761 : List Nat := [1, 2, 3, 1, 1, 3, 4, 1, 7]
def baseStart_3249761 : Nat := 118140960795 + 3249761 * 2 ^ 59
def prefixEnd_3249761 : Nat := 4983230072969 + 3 ^ 40 * 3249761 * 2
def baseEnd_3249761 : Nat := 185409933915107225426903

theorem tailTrace_3249761 : CollatzResearch.WordTrace tailWord_3249761 prefixEnd_3249761 185409933915107225426903 := by
  unfold tailWord_3249761
  simp only [CollatzResearch.WordTrace]
  refine ⟨118528521179678386836909137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79019014119785591224606091 118528521179678386836909137)
  ·
    refine ⟨88896390884758790127681853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118528521179678386836909137 88896390884758790127681853)
    ·
      refine ⟨33336146581784546297880695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88896390884758790127681853 33336146581784546297880695)
      ·
        refine ⟨50004219872676819446821043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33336146581784546297880695 50004219872676819446821043)
        ·
          refine ⟨75006329809015229170231565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50004219872676819446821043 75006329809015229170231565)
          ·
            refine ⟨28127373678380710938836837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75006329809015229170231565 28127373678380710938836837)
            ·
              refine ⟨5273882564696383301031907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28127373678380710938836837 5273882564696383301031907)
              ·
                refine ⟨7910823847044574951547861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273882564696383301031907 7910823847044574951547861)
                ·
                  refine ⟨185409933915107225426903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7910823847044574951547861 185409933915107225426903)
                  ·
                    rfl

theorem cell23_3249761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 1, 7].length) (baseStart_3249761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249761 prefixEnd_3249761 := by exact prefixLift 3249761
  have htrace : WordTrace (prefixWord ++ tailWord_3249761) baseStart_3249761 baseEnd_3249761 := by
    simpa [prefixWord, tailWord_3249761, baseEnd_3249761] using wordTrace_append hprefix tailTrace_3249761
  have hstable : (prefixWord ++ tailWord_3249761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249761).length < 2 ^ (prefixWord ++ tailWord_3249761).sum := by decide
  have hdescent : baseEnd_3249761 < baseStart_3249761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249768 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3249768 : Nat := 118140960795 + 3249768 * 2 ^ 59
def prefixEnd_3249768 : Nat := 4983230072969 + 3 ^ 40 * 3249768 * 2
def baseEnd_3249768 : Nat := 1668692999600546501454595

theorem tailTrace_3249768 : CollatzResearch.WordTrace tailWord_3249768 prefixEnd_3249768 1668692999600546501454595 := by
  unfold tailWord_3249768
  simp only [CollatzResearch.WordTrace]
  refine ⟨59264388245326513516206979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79019184327102018021609305 59264388245326513516206979)
  ·
    refine ⟨88896582367989770274310469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59264388245326513516206979 88896582367989770274310469)
    ·
      refine ⟨16668109193998081926433213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88896582367989770274310469 16668109193998081926433213)
      ·
        refine ⟨6250540947749280722412455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16668109193998081926433213 6250540947749280722412455)
        ·
          refine ⟨9375811421623921083618683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6250540947749280722412455 9375811421623921083618683)
          ·
            refine ⟨14063717132435881625428025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9375811421623921083618683 14063717132435881625428025)
            ·
              refine ⟨10547787849326911219071019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14063717132435881625428025 10547787849326911219071019)
              ·
                refine ⟨15821681773990366828606529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10547787849326911219071019 15821681773990366828606529)
                ·
                  refine ⟨11866261330492775121454897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15821681773990366828606529 11866261330492775121454897)
                  ·
                    refine ⟨8899695997869581341091173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11866261330492775121454897 8899695997869581341091173)
                    ·
                      refine ⟨1668692999600546501454595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8899695997869581341091173 1668692999600546501454595)
                      ·
                        rfl

theorem cell23_3249768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3249768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249768 prefixEnd_3249768 := by exact prefixLift 3249768
  have htrace : WordTrace (prefixWord ++ tailWord_3249768) baseStart_3249768 baseEnd_3249768 := by
    simpa [prefixWord, tailWord_3249768, baseEnd_3249768] using wordTrace_append hprefix tailTrace_3249768
  have hstable : (prefixWord ++ tailWord_3249768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249768).length < 2 ^ (prefixWord ++ tailWord_3249768).sum := by decide
  have hdescent : baseEnd_3249768 < baseStart_3249768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249812 : List Nat := [2, 4, 2, 2, 3, 1, 1, 1, 7]
def baseStart_3249812 : Nat := 118140960795 + 3249812 * 2 ^ 59
def prefixEnd_3249812 : Nat := 4983230072969 + 3 ^ 40 * 3249812 * 2
def baseEnd_3249812 : Nat := 185412843638816036589377

theorem tailTrace_3249812 : CollatzResearch.WordTrace tailWord_3249812 prefixEnd_3249812 185412843638816036589377 := by
  unfold tailWord_3249812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59265190651246811273507845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79020254201662415031343793 59265190651246811273507845)
  ·
    refine ⟨11112223247108777113782721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59265190651246811273507845 11112223247108777113782721)
    ·
      refine ⟨8334167435331582835337041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11112223247108777113782721 8334167435331582835337041)
      ·
        refine ⟨6250625576498687126502781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8334167435331582835337041 6250625576498687126502781)
        ·
          refine ⟨2343984591187007672438543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6250625576498687126502781 2343984591187007672438543)
          ·
            refine ⟨3515976886780511508657815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343984591187007672438543 3515976886780511508657815)
            ·
              refine ⟨5273965330170767262986723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3515976886780511508657815 5273965330170767262986723)
              ·
                refine ⟨7910947995256150894480085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5273965330170767262986723 7910947995256150894480085)
                ·
                  refine ⟨185412843638816036589377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7910947995256150894480085 185412843638816036589377)
                  ·
                    rfl

theorem cell23_3249812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_3249812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249812 prefixEnd_3249812 := by exact prefixLift 3249812
  have htrace : WordTrace (prefixWord ++ tailWord_3249812) baseStart_3249812 baseEnd_3249812 := by
    simpa [prefixWord, tailWord_3249812, baseEnd_3249812] using wordTrace_append hprefix tailTrace_3249812
  have hstable : (prefixWord ++ tailWord_3249812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249812).length < 2 ^ (prefixWord ++ tailWord_3249812).sum := by decide
  have hdescent : baseEnd_3249812 < baseStart_3249812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249823 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3249823 : Nat := 118140960795 + 3249823 * 2 ^ 59
def prefixEnd_3249823 : Nat := 4983230072969 + 3 ^ 40 * 3249823 * 2
def baseEnd_3249823 : Nat := 1668721241036543786266843

theorem tailTrace_3249823 : CollatzResearch.WordTrace tailWord_3249823 prefixEnd_3249823 1668721241036543786266843 := by
  unfold tailWord_3249823
  simp only [CollatzResearch.WordTrace]
  refine ⟨118530782505453771425666123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79020521670302514283777415 118530782505453771425666123)
  ·
    refine ⟨177796173758180657138499185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118530782505453771425666123 177796173758180657138499185)
    ·
      refine ⟨133347130318635492853874389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177796173758180657138499185 133347130318635492853874389)
      ·
        refine ⟨3125323366843019363762681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 133347130318635492853874389 3125323366843019363762681)
        ·
          refine ⟨2343992525132264522822011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3125323366843019363762681 2343992525132264522822011)
          ·
            refine ⟨3515988787698396784233017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2343992525132264522822011 3515988787698396784233017)
            ·
              refine ⟨2636991590773797588174763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515988787698396784233017 2636991590773797588174763)
              ·
                refine ⟨3955487386160696382262145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636991590773797588174763 3955487386160696382262145)
                ·
                  refine ⟨2966615539620522286696609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3955487386160696382262145 2966615539620522286696609)
                  ·
                    refine ⟨2224961654715391715022457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2966615539620522286696609 2224961654715391715022457)
                    ·
                      refine ⟨1668721241036543786266843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2224961654715391715022457 1668721241036543786266843)
                      ·
                        rfl

theorem cell23_3249823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3249823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249823 prefixEnd_3249823 := by exact prefixLift 3249823
  have htrace : WordTrace (prefixWord ++ tailWord_3249823) baseStart_3249823 baseEnd_3249823 := by
    simpa [prefixWord, tailWord_3249823, baseEnd_3249823] using wordTrace_append hprefix tailTrace_3249823
  have hstable : (prefixWord ++ tailWord_3249823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249823).length < 2 ^ (prefixWord ++ tailWord_3249823).sum := by decide
  have hdescent : baseEnd_3249823 < baseStart_3249823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249855 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 1, 4]
def baseStart_3249855 : Nat := 118140960795 + 3249855 * 2 ^ 59
def prefixEnd_3249855 : Nat := 4983230072969 + 3 ^ 40 * 3249855 * 2
def baseEnd_3249855 : Nat := 556245890805829220355565

theorem tailTrace_3249855 : CollatzResearch.WordTrace tailWord_3249855 prefixEnd_3249855 556245890805829220355565 := by
  unfold tailWord_3249855
  simp only [CollatzResearch.WordTrace]
  refine ⟨118531949641337840890831019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79021299760891893927220679 118531949641337840890831019)
  ·
    refine ⟨177797924462006761336246529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118531949641337840890831019 177797924462006761336246529)
    ·
      refine ⟨133348443346505071002184897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177797924462006761336246529 133348443346505071002184897)
      ·
        refine ⟨100011332509878803251638673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133348443346505071002184897 100011332509878803251638673)
        ·
          refine ⟨75008499382409102438729005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100011332509878803251638673 75008499382409102438729005)
          ·
            refine ⟨28128187268403413414523377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75008499382409102438729005 28128187268403413414523377)
            ·
              refine ⟨21096140451302560060892533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28128187268403413414523377 21096140451302560060892533)
              ·
                refine ⟨1977763167309615005708675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21096140451302560060892533 1977763167309615005708675)
                ·
                  refine ⟨2966644750964422508563013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1977763167309615005708675 2966644750964422508563013)
                  ·
                    refine ⟨556245890805829220355565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966644750964422508563013 556245890805829220355565)
                    ·
                      rfl

theorem cell23_3249855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 4].length) (baseStart_3249855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249855 prefixEnd_3249855 := by exact prefixLift 3249855
  have htrace : WordTrace (prefixWord ++ tailWord_3249855) baseStart_3249855 baseEnd_3249855 := by
    simpa [prefixWord, tailWord_3249855, baseEnd_3249855] using wordTrace_append hprefix tailTrace_3249855
  have hstable : (prefixWord ++ tailWord_3249855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249855).length < 2 ^ (prefixWord ++ tailWord_3249855).sum := by decide
  have hdescent : baseEnd_3249855 < baseStart_3249855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249898 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_3249898 : Nat := 118140960795 + 3249898 * 2 ^ 59
def prefixEnd_3249898 : Nat := 4983230072969 + 3 ^ 40 * 3249898 * 2
def baseEnd_3249898 : Nat := 556253250695210330942999

theorem tailTrace_3249898 : CollatzResearch.WordTrace tailWord_3249898 prefixEnd_3249898 556253250695210330942999 := by
  unfold tailWord_3249898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29633379495045514808661587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79022345320121372823097565 29633379495045514808661587)
  ·
    refine ⟨44450069242568272212992381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29633379495045514808661587 44450069242568272212992381)
    ·
      refine ⟨16668775965963102079872143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44450069242568272212992381 16668775965963102079872143)
      ·
        refine ⟨25003163948944653119808215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16668775965963102079872143 25003163948944653119808215)
        ·
          refine ⟨37504745923416979679712323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25003163948944653119808215 37504745923416979679712323)
          ·
            refine ⟨56257118885125469519568485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37504745923416979679712323 56257118885125469519568485)
            ·
              refine ⟨10548209790961025534919091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56257118885125469519568485 10548209790961025534919091)
              ·
                refine ⟨15822314686441538302378637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548209790961025534919091 15822314686441538302378637)
                ·
                  refine ⟨5933368007415576863391989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15822314686441538302378637 5933368007415576863391989)
                  ·
                    refine ⟨556253250695210330942999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5933368007415576863391989 556253250695210330942999)
                    ·
                      rfl

theorem cell23_3249898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_3249898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249898 prefixEnd_3249898 := by exact prefixLift 3249898
  have htrace : WordTrace (prefixWord ++ tailWord_3249898) baseStart_3249898 baseEnd_3249898 := by
    simpa [prefixWord, tailWord_3249898, baseEnd_3249898] using wordTrace_append hprefix tailTrace_3249898
  have hstable : (prefixWord ++ tailWord_3249898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249898).length < 2 ^ (prefixWord ++ tailWord_3249898).sum := by decide
  have hdescent : baseEnd_3249898 < baseStart_3249898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249905 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_3249905 : Nat := 118140960795 + 3249905 * 2 ^ 59
def prefixEnd_3249905 : Nat := 4983230072969 + 3 ^ 40 * 3249905 * 2
def baseEnd_3249905 : Nat := 1668763346450212465441465

theorem tailTrace_3249905 : CollatzResearch.WordTrace tailWord_3249905 prefixEnd_3249905 1668763346450212465441465 := by
  unfold tailWord_3249905
  simp only [CollatzResearch.WordTrace]
  refine ⟨118533773291156699430151169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79022515527437799620100779 118533773291156699430151169)
  ·
    refine ⟨88900329968367524572613377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118533773291156699430151169 88900329968367524572613377)
    ·
      refine ⟨66675247476275643429460033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88900329968367524572613377 66675247476275643429460033)
      ·
        refine ⟨50006435607206732572095025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66675247476275643429460033 50006435607206732572095025)
        ·
          refine ⟨37504826705405049429071269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50006435607206732572095025 37504826705405049429071269)
          ·
            refine ⟨7032155007263446767950863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37504826705405049429071269 7032155007263446767950863)
            ·
              refine ⟨10548232510895170151926295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7032155007263446767950863 10548232510895170151926295)
              ·
                refine ⟨15822348766342755227889443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548232510895170151926295 15822348766342755227889443)
                ·
                  refine ⟨23733523149514132841834165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15822348766342755227889443 23733523149514132841834165)
                  ·
                    refine ⟨2225017795266949953921953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23733523149514132841834165 2225017795266949953921953)
                    ·
                      refine ⟨1668763346450212465441465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225017795266949953921953 1668763346450212465441465)
                      ·
                        rfl

theorem cell23_3249905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_3249905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249905 prefixEnd_3249905 := by exact prefixLift 3249905
  have htrace : WordTrace (prefixWord ++ tailWord_3249905) baseStart_3249905 baseEnd_3249905 := by
    simpa [prefixWord, tailWord_3249905, baseEnd_3249905] using wordTrace_append hprefix tailTrace_3249905
  have hstable : (prefixWord ++ tailWord_3249905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249905).length < 2 ^ (prefixWord ++ tailWord_3249905).sum := by decide
  have hdescent : baseEnd_3249905 < baseStart_3249905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249922 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_3249922 : Nat := 118140960795 + 3249922 * 2 ^ 59
def prefixEnd_3249922 : Nat := 4983230072969 + 3 ^ 40 * 3249922 * 2
def baseEnd_3249922 : Nat := 1668772075621338898928887

theorem tailTrace_3249922 : CollatzResearch.WordTrace tailWord_3249922 prefixEnd_3249922 1668772075621338898928887 := by
  unfold tailWord_3249922
  simp only [CollatzResearch.WordTrace]
  refine ⟨29633598333023777833380005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79022928888063407555680013 29633598333023777833380005)
  ·
    refine ⟨5556299687441958343758751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29633598333023777833380005 5556299687441958343758751)
    ·
      refine ⟨8334449531162937515638127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556299687441958343758751 8334449531162937515638127)
      ·
        refine ⟨12501674296744406273457191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334449531162937515638127 12501674296744406273457191)
        ·
          refine ⟨18752511445116609410185787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501674296744406273457191 18752511445116609410185787)
          ·
            refine ⟨28128767167674914115278681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18752511445116609410185787 28128767167674914115278681)
            ·
              refine ⟨21096575375756185586459011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28128767167674914115278681 21096575375756185586459011)
              ·
                refine ⟨31644863063634278379688517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21096575375756185586459011 31644863063634278379688517)
                ·
                  refine ⟨5933411824431427196191597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31644863063634278379688517 5933411824431427196191597)
                  ·
                    refine ⟨2225029434161785198571849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5933411824431427196191597 2225029434161785198571849)
                    ·
                      refine ⟨1668772075621338898928887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225029434161785198571849 1668772075621338898928887)
                      ·
                        rfl

theorem cell23_3249922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_3249922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249922 prefixEnd_3249922 := by exact prefixLift 3249922
  have htrace : WordTrace (prefixWord ++ tailWord_3249922) baseStart_3249922 baseEnd_3249922 := by
    simpa [prefixWord, tailWord_3249922, baseEnd_3249922] using wordTrace_append hprefix tailTrace_3249922
  have hstable : (prefixWord ++ tailWord_3249922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249922).length < 2 ^ (prefixWord ++ tailWord_3249922).sum := by decide
  have hdescent : baseEnd_3249922 < baseStart_3249922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249948 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3249948 : Nat := 118140960795 + 3249948 * 2 ^ 59
def prefixEnd_3249948 : Nat := 4983230072969 + 3 ^ 40 * 3249948 * 2
def baseEnd_3249948 : Nat := 1668785426118355797203767

theorem tailTrace_3249948 : CollatzResearch.WordTrace tailWord_3249948 prefixEnd_3249948 1668785426118355797203767 := by
  unfold tailWord_3249948
  simp only [CollatzResearch.WordTrace]
  refine ⟨59267670815000458886983249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79023561086667278515977665 59267670815000458886983249)
  ·
    refine ⟨44450753111250344165237437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59267670815000458886983249 44450753111250344165237437)
    ·
      refine ⟨16669032416718879061964039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44450753111250344165237437 16669032416718879061964039)
      ·
        refine ⟨25003548625078318592946059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16669032416718879061964039 25003548625078318592946059)
        ·
          refine ⟨37505322937617477889419089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25003548625078318592946059 37505322937617477889419089)
          ·
            refine ⟨28128992203213108417064317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37505322937617477889419089 28128992203213108417064317)
            ·
              refine ⟨10548372076204915656399119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28128992203213108417064317 10548372076204915656399119)
              ·
                refine ⟨15822558114307373484598679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10548372076204915656399119 15822558114307373484598679)
                ·
                  refine ⟨23733837171461060226898019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15822558114307373484598679 23733837171461060226898019)
                  ·
                    refine ⟨35600755757191590340347029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23733837171461060226898019 35600755757191590340347029)
                    ·
                      refine ⟨1668785426118355797203767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35600755757191590340347029 1668785426118355797203767)
                      ·
                        rfl

theorem cell23_3249948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3249948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249948 prefixEnd_3249948 := by exact prefixLift 3249948
  have htrace : WordTrace (prefixWord ++ tailWord_3249948) baseStart_3249948 baseEnd_3249948 := by
    simpa [prefixWord, tailWord_3249948, baseEnd_3249948] using wordTrace_append hprefix tailTrace_3249948
  have hstable : (prefixWord ++ tailWord_3249948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249948).length < 2 ^ (prefixWord ++ tailWord_3249948).sum := by decide
  have hdescent : baseEnd_3249948 < baseStart_3249948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249952 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3249952 : Nat := 118140960795 + 3249952 * 2 ^ 59
def prefixEnd_3249952 : Nat := 4983230072969 + 3 ^ 40 * 3249952 * 2
def baseEnd_3249952 : Nat := 1668787480040973781553749

theorem tailTrace_3249952 : CollatzResearch.WordTrace tailWord_3249952 prefixEnd_3249952 1668787480040973781553749 := by
  unfold tailWord_3249952
  simp only [CollatzResearch.WordTrace]
  refine ⟨59267743760993213228556055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79023658347990950971408073 59267743760993213228556055)
  ·
    refine ⟨88901615641489819842834083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59267743760993213228556055 88901615641489819842834083)
    ·
      refine ⟨133352423462234729764251125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88901615641489819842834083 133352423462234729764251125)
      ·
        refine ⟨12501789699584505915398543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133352423462234729764251125 12501789699584505915398543)
        ·
          refine ⟨18752684549376758873097815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12501789699584505915398543 18752684549376758873097815)
          ·
            refine ⟨28129026824065138309646723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18752684549376758873097815 28129026824065138309646723)
            ·
              refine ⟨42193540236097707464470085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28129026824065138309646723 42193540236097707464470085)
              ·
                refine ⟨7911288794268320149588141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42193540236097707464470085 7911288794268320149588141)
                ·
                  refine ⟨2966733297850620056095553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7911288794268320149588141 2966733297850620056095553)
                  ·
                    refine ⟨2225049973387965042071665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2966733297850620056095553 2225049973387965042071665)
                    ·
                      refine ⟨1668787480040973781553749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225049973387965042071665 1668787480040973781553749)
                      ·
                        rfl

theorem cell23_3249952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3249952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249952 prefixEnd_3249952 := by exact prefixLift 3249952
  have htrace : WordTrace (prefixWord ++ tailWord_3249952) baseStart_3249952 baseEnd_3249952 := by
    simpa [prefixWord, tailWord_3249952, baseEnd_3249952] using wordTrace_append hprefix tailTrace_3249952
  have hstable : (prefixWord ++ tailWord_3249952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249952).length < 2 ^ (prefixWord ++ tailWord_3249952).sum := by decide
  have hdescent : baseEnd_3249952 < baseStart_3249952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249955 : List Nat := [1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 3]
def baseStart_3249955 : Nat := 118140960795 + 3249955 * 2 ^ 59
def prefixEnd_3249955 : Nat := 4983230072969 + 3 ^ 40 * 3249955 * 2
def baseEnd_3249955 : Nat := 1668789020482937269816235

theorem tailTrace_3249955 : CollatzResearch.WordTrace tailWord_3249955 prefixEnd_3249955 1668789020482937269816235 := by
  unfold tailWord_3249955
  simp only [CollatzResearch.WordTrace]
  refine ⟨118535596940975557969471319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79023731293983705312980879 118535596940975557969471319)
  ·
    refine ⟨177803395411463336954206979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118535596940975557969471319 177803395411463336954206979)
    ·
      refine ⟨266705093117195005431310469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177803395411463336954206979 266705093117195005431310469)
      ·
        refine ⟨50007204959474063518370713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266705093117195005431310469 50007204959474063518370713)
        ·
          refine ⟨37505403719605547638778035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50007204959474063518370713 37505403719605547638778035)
          ·
            refine ⟨56258105579408321458167053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37505403719605547638778035 56258105579408321458167053)
            ·
              refine ⟨21096789592278120546812645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56258105579408321458167053 21096789592278120546812645)
              ·
                refine ⟨3955648048552147602527371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21096789592278120546812645 3955648048552147602527371)
                ·
                  refine ⟨5933472072828221403791057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3955648048552147602527371 5933472072828221403791057)
                  ·
                    refine ⟨4450104054621166052843293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5933472072828221403791057 4450104054621166052843293)
                    ·
                      refine ⟨1668789020482937269816235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4450104054621166052843293 1668789020482937269816235)
                      ·
                        rfl

theorem cell23_3249955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 2, 3].length) (baseStart_3249955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249955 prefixEnd_3249955 := by exact prefixLift 3249955
  have htrace : WordTrace (prefixWord ++ tailWord_3249955) baseStart_3249955 baseEnd_3249955 := by
    simpa [prefixWord, tailWord_3249955, baseEnd_3249955] using wordTrace_append hprefix tailTrace_3249955
  have hstable : (prefixWord ++ tailWord_3249955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249955).length < 2 ^ (prefixWord ++ tailWord_3249955).sum := by decide
  have hdescent : baseEnd_3249955 < baseStart_3249955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249972 : List Nat := [2, 5, 1, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3249972 : Nat := 118140960795 + 3249972 * 2 ^ 59
def prefixEnd_3249972 : Nat := 4983230072969 + 3 ^ 40 * 3249972 * 2
def baseEnd_3249972 : Nat := 1668797749654063703303657

theorem tailTrace_3249972 : CollatzResearch.WordTrace tailWord_3249972 prefixEnd_3249972 1668797749654063703303657 := by
  unfold tailWord_3249972
  simp only [CollatzResearch.WordTrace]
  refine ⟨59268108490956984936420085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79024144654609313248560113 59268108490956984936420085)
  ·
    refine ⟨5556385171027217337789383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59268108490956984936420085 5556385171027217337789383)
    ·
      refine ⟨8334577756540826006684075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556385171027217337789383 8334577756540826006684075)
      ·
        refine ⟨12501866634811239010026113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334577756540826006684075 12501866634811239010026113)
        ·
          refine ⟨9376399976108429257519585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12501866634811239010026113 9376399976108429257519585)
          ·
            refine ⟨7032299982081321943139689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9376399976108429257519585 7032299982081321943139689)
            ·
              refine ⟨5274224986560991457354767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7032299982081321943139689 5274224986560991457354767)
              ·
                refine ⟨7911337479841487186032151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274224986560991457354767 7911337479841487186032151)
                ·
                  refine ⟨11867006219762230779048227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7911337479841487186032151 11867006219762230779048227)
                  ·
                    refine ⟨17800509329643346168572341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11867006219762230779048227 17800509329643346168572341)
                    ·
                      refine ⟨1668797749654063703303657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17800509329643346168572341 1668797749654063703303657)
                      ·
                        rfl

theorem cell23_3249972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3249972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249972 prefixEnd_3249972 := by exact prefixLift 3249972
  have htrace : WordTrace (prefixWord ++ tailWord_3249972) baseStart_3249972 baseEnd_3249972 := by
    simpa [prefixWord, tailWord_3249972, baseEnd_3249972] using wordTrace_append hprefix tailTrace_3249972
  have hstable : (prefixWord ++ tailWord_3249972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249972).length < 2 ^ (prefixWord ++ tailWord_3249972).sum := by decide
  have hdescent : baseEnd_3249972 < baseStart_3249972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3249996 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_3249996 : Nat := 118140960795 + 3249996 * 2 ^ 59
def prefixEnd_3249996 : Nat := 4983230072969 + 3 ^ 40 * 3249996 * 2
def baseEnd_3249996 : Nat := 556270024396590536467849

theorem tailTrace_3249996 : CollatzResearch.WordTrace tailWord_3249996 prefixEnd_3249996 556270024396590536467849 := by
  unfold tailWord_3249996
  simp only [CollatzResearch.WordTrace]
  refine ⟨59268546166913510985856921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79024728222551347981142561 59268546166913510985856921)
  ·
    refine ⟨44451409625185133239392691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59268546166913510985856921 44451409625185133239392691)
    ·
      refine ⟨66677114437777699859089037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44451409625185133239392691 66677114437777699859089037)
      ·
        refine ⟨25003917914166637447158389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66677114437777699859089037 25003917914166637447158389)
        ·
          refine ⟨2344117304453122260671099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25003917914166637447158389 2344117304453122260671099)
          ·
            refine ⟨3516175956679683391006649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344117304453122260671099 3516175956679683391006649)
            ·
              refine ⟨2637131967509762543254987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516175956679683391006649 2637131967509762543254987)
              ·
                refine ⟨3955697951264643814882481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637131967509762543254987 3955697951264643814882481)
                ·
                  refine ⟨2966773463448482861161861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3955697951264643814882481 2966773463448482861161861)
                  ·
                    refine ⟨556270024396590536467849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2966773463448482861161861 556270024396590536467849)
                    ·
                      rfl

theorem cell23_3249996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_3249996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3249996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3249996 prefixEnd_3249996 := by exact prefixLift 3249996
  have htrace : WordTrace (prefixWord ++ tailWord_3249996) baseStart_3249996 baseEnd_3249996 := by
    simpa [prefixWord, tailWord_3249996, baseEnd_3249996] using wordTrace_append hprefix tailTrace_3249996
  have hstable : (prefixWord ++ tailWord_3249996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3249996).length < 2 ^ (prefixWord ++ tailWord_3249996).sum := by decide
  have hdescent : baseEnd_3249996 < baseStart_3249996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3249996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250042 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2]
def baseStart_3250042 : Nat := 118140960795 + 3250042 * 2 ^ 59
def prefixEnd_3250042 : Nat := 4983230072969 + 3 ^ 40 * 3250042 * 2
def baseEnd_3250042 : Nat := 1668833693299878429428335

theorem tailTrace_3250042 : CollatzResearch.WordTrace tailWord_3250042 prefixEnd_3250042 1668833693299878429428335 := by
  unfold tailWord_3250042
  simp only [CollatzResearch.WordTrace]
  refine ⟨29634692522915092956972095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79025846727773581218592253 29634692522915092956972095)
  ·
    refine ⟨44452038784372639435458143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29634692522915092956972095 44452038784372639435458143)
    ·
      refine ⟨66678058176558959153187215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44452038784372639435458143 66678058176558959153187215)
      ·
        refine ⟨100017087264838438729780823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66678058176558959153187215 100017087264838438729780823)
        ·
          refine ⟨150025630897257658094671235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100017087264838438729780823 150025630897257658094671235)
          ·
            refine ⟨225038446345886487142006853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150025630897257658094671235 225038446345886487142006853)
            ·
              refine ⟨42194708689853716339126285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225038446345886487142006853 42194708689853716339126285)
              ·
                refine ⟨15823015758695143627172357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42194708689853716339126285 15823015758695143627172357)
                ·
                  refine ⟨2966815454755339430094817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15823015758695143627172357 2966815454755339430094817)
                  ·
                    refine ⟨2225111591066504572571113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2966815454755339430094817 2225111591066504572571113)
                    ·
                      refine ⟨1668833693299878429428335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225111591066504572571113 1668833693299878429428335)
                      ·
                        rfl

theorem cell23_3250042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 4, 2, 2].length) (baseStart_3250042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250042 prefixEnd_3250042 := by exact prefixLift 3250042
  have htrace : WordTrace (prefixWord ++ tailWord_3250042) baseStart_3250042 baseEnd_3250042 := by
    simpa [prefixWord, tailWord_3250042, baseEnd_3250042] using wordTrace_append hprefix tailTrace_3250042
  have hstable : (prefixWord ++ tailWord_3250042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250042).length < 2 ^ (prefixWord ++ tailWord_3250042).sum := by decide
  have hdescent : baseEnd_3250042 < baseStart_3250042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250048 : List Nat := [2, 1, 1, 2, 1, 2, 4, 3, 7]
def baseStart_3250048 : Nat := 118140960795 + 3250048 * 2 ^ 59
def prefixEnd_3250048 : Nat := 4983230072969 + 3 ^ 40 * 3250048 * 2
def baseEnd_3250048 : Nat := 185426308242645045105923

theorem tailTrace_3250048 : CollatzResearch.WordTrace tailWord_3250048 prefixEnd_3250048 185426308242645045105923 := by
  unfold tailWord_3250048
  simp only [CollatzResearch.WordTrace]
  refine ⟨59269494464819317426303399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79025992619759089901737865 59269494464819317426303399)
  ·
    refine ⟨88904241697228976139455099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59269494464819317426303399 88904241697228976139455099)
    ·
      refine ⟨133356362545843464209182649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88904241697228976139455099 133356362545843464209182649)
      ·
        refine ⟨100017271909382598156886987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133356362545843464209182649 100017271909382598156886987)
        ·
          refine ⟨150025907864073897235330481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100017271909382598156886987 150025907864073897235330481)
          ·
            refine ⟨112519430898055422926497861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150025907864073897235330481 112519430898055422926497861)
            ·
              refine ⟨21097393293385391798718349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112519430898055422926497861 21097393293385391798718349)
              ·
                refine ⟨7911522485019521924519381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21097393293385391798718349 7911522485019521924519381)
                ·
                  refine ⟨185426308242645045105923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7911522485019521924519381 185426308242645045105923)
                  ·
                    rfl

theorem cell23_3250048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_3250048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250048 prefixEnd_3250048 := by exact prefixLift 3250048
  have htrace : WordTrace (prefixWord ++ tailWord_3250048) baseStart_3250048 baseEnd_3250048 := by
    simpa [prefixWord, tailWord_3250048, baseEnd_3250048] using wordTrace_append hprefix tailTrace_3250048
  have hstable : (prefixWord ++ tailWord_3250048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250048).length < 2 ^ (prefixWord ++ tailWord_3250048).sum := by decide
  have hdescent : baseEnd_3250048 < baseStart_3250048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250132 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3250132 : Nat := 118140960795 + 3250132 * 2 ^ 59
def prefixEnd_3250132 : Nat := 4983230072969 + 3 ^ 40 * 3250132 * 2
def baseEnd_3250132 : Nat := 1668879906558783077302921

theorem tailTrace_3250132 : CollatzResearch.WordTrace tailWord_3250132 prefixEnd_3250132 1668879906558783077302921 := by
  unfold tailWord_3250132
  simp only [CollatzResearch.WordTrace]
  refine ⟨59271026330667158599332325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79028035107556211465776433 59271026330667158599332325)
  ·
    refine ⟨11113317437000092237374811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59271026330667158599332325 11113317437000092237374811)
    ·
      refine ⟨16669976155500138356062217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11113317437000092237374811 16669976155500138356062217)
      ·
        refine ⟨12502482116625103767046663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16669976155500138356062217 12502482116625103767046663)
        ·
          refine ⟨18753723174937655650569995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12502482116625103767046663 18753723174937655650569995)
          ·
            refine ⟨28130584762406483475854993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18753723174937655650569995 28130584762406483475854993)
            ·
              refine ⟨21097938571804862606891245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28130584762406483475854993 21097938571804862606891245)
              ·
                refine ⟨7911726964426823477584217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21097938571804862606891245 7911726964426823477584217)
                ·
                  refine ⟨5933795223320117608188163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7911726964426823477584217 5933795223320117608188163)
                  ·
                    refine ⟨8900692834980176412282245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5933795223320117608188163 8900692834980176412282245)
                    ·
                      refine ⟨1668879906558783077302921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8900692834980176412282245 1668879906558783077302921)
                      ·
                        rfl

theorem cell23_3250132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3250132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250132 prefixEnd_3250132 := by exact prefixLift 3250132
  have htrace : WordTrace (prefixWord ++ tailWord_3250132) baseStart_3250132 baseEnd_3250132 := by
    simpa [prefixWord, tailWord_3250132, baseEnd_3250132] using wordTrace_append hprefix tailTrace_3250132
  have hstable : (prefixWord ++ tailWord_3250132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250132).length < 2 ^ (prefixWord ++ tailWord_3250132).sum := by decide
  have hdescent : baseEnd_3250132 < baseStart_3250132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250135 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_3250135 : Nat := 118140960795 + 3250135 * 2 ^ 59
def prefixEnd_3250135 : Nat := 4983230072969 + 3 ^ 40 * 3250135 * 2
def baseEnd_3250135 : Nat := 1668881447000746565565407

theorem tailTrace_3250135 : CollatzResearch.WordTrace tailWord_3250135 prefixEnd_3250135 1668881447000746565565407 := by
  unfold tailWord_3250135
  simp only [CollatzResearch.WordTrace]
  refine ⟨118542162080323448711023859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79028108053548965807349239 118542162080323448711023859)
  ·
    refine ⟨177813243120485173066535789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118542162080323448711023859 177813243120485173066535789)
    ·
      refine ⟨66679966170181939899950921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177813243120485173066535789 66679966170181939899950921)
      ·
        refine ⟨50009974627636454924963191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66679966170181939899950921 50009974627636454924963191)
        ·
          refine ⟨75014961941454682387444787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50009974627636454924963191 75014961941454682387444787)
          ·
            refine ⟨112522442912182023581167181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75014961941454682387444787 112522442912182023581167181)
            ·
              refine ⟨42195916092068258842937693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112522442912182023581167181 42195916092068258842937693)
              ·
                refine ⟨15823468534525597066101635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42195916092068258842937693 15823468534525597066101635)
                ·
                  refine ⟨23735202801788395599152453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15823468534525597066101635 23735202801788395599152453)
                  ·
                    refine ⟨4450350525335324174841085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23735202801788395599152453 4450350525335324174841085)
                    ·
                      refine ⟨1668881447000746565565407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4450350525335324174841085 1668881447000746565565407)
                      ·
                        rfl

theorem cell23_3250135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_3250135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250135 prefixEnd_3250135 := by exact prefixLift 3250135
  have htrace : WordTrace (prefixWord ++ tailWord_3250135) baseStart_3250135 baseEnd_3250135 := by
    simpa [prefixWord, tailWord_3250135, baseEnd_3250135] using wordTrace_append hprefix tailTrace_3250135
  have hstable : (prefixWord ++ tailWord_3250135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250135).length < 2 ^ (prefixWord ++ tailWord_3250135).sum := by decide
  have hdescent : baseEnd_3250135 < baseStart_3250135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250192 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2]
def baseStart_3250192 : Nat := 118140960795 + 3250192 * 2 ^ 59
def prefixEnd_3250192 : Nat := 4983230072969 + 3 ^ 40 * 3250192 * 2
def baseEnd_3250192 : Nat := 1668910715398052842552645

theorem tailTrace_3250192 : CollatzResearch.WordTrace tailWord_3250192 prefixEnd_3250192 1668910715398052842552645 := by
  unfold tailWord_3250192
  simp only [CollatzResearch.WordTrace]
  refine ⟨59272120520558473722924415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79029494027411298297232553 59272120520558473722924415)
  ·
    refine ⟨88908180780837710584386623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59272120520558473722924415 88908180780837710584386623)
    ·
      refine ⟨133362271171256565876579935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88908180780837710584386623 133362271171256565876579935)
      ·
        refine ⟨200043406756884848814869903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133362271171256565876579935 200043406756884848814869903)
        ·
          refine ⟨300065110135327273222304855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200043406756884848814869903 300065110135327273222304855)
          ·
            refine ⟨450097665202990909833457283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300065110135327273222304855 450097665202990909833457283)
            ·
              refine ⟨675146497804486364750185925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450097665202990909833457283 675146497804486364750185925)
              ·
                refine ⟨126589968338341193390659861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675146497804486364750185925 126589968338341193390659861)
                ·
                  refine ⟨5933904765859743440187181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126589968338341193390659861 5933904765859743440187181)
                  ·
                    refine ⟨2225214287197403790070193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5933904765859743440187181 2225214287197403790070193)
                    ·
                      refine ⟨1668910715398052842552645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225214287197403790070193 1668910715398052842552645)
                      ·
                        rfl

theorem cell23_3250192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 6, 3, 2].length) (baseStart_3250192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250192 prefixEnd_3250192 := by exact prefixLift 3250192
  have htrace : WordTrace (prefixWord ++ tailWord_3250192) baseStart_3250192 baseEnd_3250192 := by
    simpa [prefixWord, tailWord_3250192, baseEnd_3250192] using wordTrace_append hprefix tailTrace_3250192
  have hstable : (prefixWord ++ tailWord_3250192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250192).length < 2 ^ (prefixWord ++ tailWord_3250192).sum := by decide
  have hdescent : baseEnd_3250192 < baseStart_3250192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250235 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_3250235 : Nat := 118140960795 + 3250235 * 2 ^ 59
def prefixEnd_3250235 : Nat := 4983230072969 + 3 ^ 40 * 3250235 * 2
def baseEnd_3250235 : Nat := 1668932795066196174314947

theorem tailTrace_3250235 : CollatzResearch.WordTrace tailWord_3250235 prefixEnd_3250235 1668932795066196174314947 := by
  unfold tailWord_3250235
  simp only [CollatzResearch.WordTrace]
  refine ⟨118545809379961165789664159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79030539586640777193109439 118545809379961165789664159)
  ·
    refine ⟨177818714069941748684496239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118545809379961165789664159 177818714069941748684496239)
    ·
      refine ⟨266728071104912623026744359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177818714069941748684496239 266728071104912623026744359)
      ·
        refine ⟨400092106657368934540116539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266728071104912623026744359 400092106657368934540116539)
        ·
          refine ⟨600138159986053401810174809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400092106657368934540116539 600138159986053401810174809)
          ·
            refine ⟨450103619989540051357631107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600138159986053401810174809 450103619989540051357631107)
            ·
              refine ⟨675155429984310077036446661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450103619989540051357631107 675155429984310077036446661)
              ·
                refine ⟨126591643122058139444333749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 675155429984310077036446661 126591643122058139444333749)
                ·
                  refine ⟨11867966542692950572906289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126591643122058139444333749 11867966542692950572906289)
                  ·
                    refine ⟨8900974907019712929679717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11867966542692950572906289 8900974907019712929679717)
                    ·
                      refine ⟨1668932795066196174314947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8900974907019712929679717 1668932795066196174314947)
                      ·
                        rfl

theorem cell23_3250235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_3250235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250235 prefixEnd_3250235 := by exact prefixLift 3250235
  have htrace : WordTrace (prefixWord ++ tailWord_3250235) baseStart_3250235 baseEnd_3250235 := by
    simpa [prefixWord, tailWord_3250235, baseEnd_3250235] using wordTrace_append hprefix tailTrace_3250235
  have hstable : (prefixWord ++ tailWord_3250235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250235).length < 2 ^ (prefixWord ++ tailWord_3250235).sum := by decide
  have hdescent : baseEnd_3250235 < baseStart_3250235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250239 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 5, 2, 2]
def baseStart_3250239 : Nat := 118140960795 + 3250239 * 2 ^ 59
def prefixEnd_3250239 : Nat := 4983230072969 + 3 ^ 40 * 3250239 * 2
def baseEnd_3250239 : Nat := 1668934848988814158664929

theorem tailTrace_3250239 : CollatzResearch.WordTrace tailWord_3250239 prefixEnd_3250239 1668934848988814158664929 := by
  unfold tailWord_3250239
  simp only [CollatzResearch.WordTrace]
  refine ⟨118545955271946674472809771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79030636847964449648539847 118545955271946674472809771)
  ·
    refine ⟨177818932907920011709214657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118545955271946674472809771 177818932907920011709214657)
    ·
      refine ⟨133364199680940008781910993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177818932907920011709214657 133364199680940008781910993)
      ·
        refine ⟨100023149760705006586433245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133364199680940008781910993 100023149760705006586433245)
        ·
          refine ⟨37508681160264377469912467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100023149760705006586433245 37508681160264377469912467)
          ·
            refine ⟨56263021740396566204868701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37508681160264377469912467 56263021740396566204868701)
            ·
              refine ⟨21098633152648712326825763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56263021740396566204868701 21098633152648712326825763)
              ·
                refine ⟨31647949728973068490238645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21098633152648712326825763 31647949728973068490238645)
                ·
                  refine ⟨2966995287091225170959873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31647949728973068490238645 2966995287091225170959873)
                  ·
                    refine ⟨2225246465318418878219905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2966995287091225170959873 2225246465318418878219905)
                    ·
                      refine ⟨1668934848988814158664929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225246465318418878219905 1668934848988814158664929)
                      ·
                        rfl

theorem cell23_3250239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_3250239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250239 prefixEnd_3250239 := by exact prefixLift 3250239
  have htrace : WordTrace (prefixWord ++ tailWord_3250239) baseStart_3250239 baseEnd_3250239 := by
    simpa [prefixWord, tailWord_3250239, baseEnd_3250239] using wordTrace_append hprefix tailTrace_3250239
  have hstable : (prefixWord ++ tailWord_3250239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250239).length < 2 ^ (prefixWord ++ tailWord_3250239).sum := by decide
  have hdescent : baseEnd_3250239 < baseStart_3250239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250252 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 1, 2, 4]
def baseStart_3250252 : Nat := 118140960795 + 3250252 * 2 ^ 59
def prefixEnd_3250252 : Nat := 4983230072969 + 3 ^ 40 * 3250252 * 2
def baseEnd_3250252 : Nat := 1668941524237322607802369

theorem tailTrace_3250252 : CollatzResearch.WordTrace tailWord_3250252 prefixEnd_3250252 1668941524237322607802369 := by
  unfold tailWord_3250252
  simp only [CollatzResearch.WordTrace]
  refine ⟨59273214710449788846516505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79030952947266385128688673 59273214710449788846516505)
  ·
    refine ⟨44454911032837341634887379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59273214710449788846516505 44454911032837341634887379)
    ·
      refine ⟨66682366549256012452331069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44454911032837341634887379 66682366549256012452331069)
      ·
        refine ⟨25005887455971004669624151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66682366549256012452331069 25005887455971004669624151)
        ·
          refine ⟨37508831183956507004436227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25005887455971004669624151 37508831183956507004436227)
          ·
            refine ⟨56263246775934760506654341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37508831183956507004436227 56263246775934760506654341)
            ·
              refine ⟨10549358770487767594997689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56263246775934760506654341 10549358770487767594997689)
              ·
                refine ⟨7912019077865825696248267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10549358770487767594997689 7912019077865825696248267)
                ·
                  refine ⟨11868028616798738544372401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912019077865825696248267 11868028616798738544372401)
                  ·
                    refine ⟨8901021462599053908279301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11868028616798738544372401 8901021462599053908279301)
                    ·
                      refine ⟨1668941524237322607802369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8901021462599053908279301 1668941524237322607802369)
                      ·
                        rfl

theorem cell23_3250252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_3250252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250252 prefixEnd_3250252 := by exact prefixLift 3250252
  have htrace : WordTrace (prefixWord ++ tailWord_3250252) baseStart_3250252 baseEnd_3250252 := by
    simpa [prefixWord, tailWord_3250252, baseEnd_3250252] using wordTrace_append hprefix tailTrace_3250252
  have hstable : (prefixWord ++ tailWord_3250252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250252).length < 2 ^ (prefixWord ++ tailWord_3250252).sum := by decide
  have hdescent : baseEnd_3250252 < baseStart_3250252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250275 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 9]
def baseStart_3250275 : Nat := 118140960795 + 3250275 * 2 ^ 59
def prefixEnd_3250275 : Nat := 4983230072969 + 3 ^ 40 * 3250275 * 2
def baseEnd_3250275 : Nat := 556317778097458672604921

theorem tailTrace_3250275 : CollatzResearch.WordTrace tailWord_3250275 prefixEnd_3250275 556317778097458672604921 := by
  unfold tailWord_3250275
  simp only [CollatzResearch.WordTrace]
  refine ⟨118547268299816252621120279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79031512199877501747413519 118547268299816252621120279)
  ·
    refine ⟨177820902449724378931680419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118547268299816252621120279 177820902449724378931680419)
    ·
      refine ⟨266731353674586568397520629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177820902449724378931680419 266731353674586568397520629)
      ·
        refine ⟨25006064406992490787267559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266731353674586568397520629 25006064406992490787267559)
        ·
          refine ⟨37509096610488736180901339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25006064406992490787267559 37509096610488736180901339)
          ·
            refine ⟨56263644915733104271352009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37509096610488736180901339 56263644915733104271352009)
            ·
              refine ⟨42197733686799828203514007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56263644915733104271352009 42197733686799828203514007)
              ·
                refine ⟨63296600530199742305271011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42197733686799828203514007 63296600530199742305271011)
                ·
                  refine ⟨94944900795299613457906517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63296600530199742305271011 94944900795299613457906517)
                  ·
                    refine ⟨556317778097458672604921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 94944900795299613457906517 556317778097458672604921)
                    ·
                      rfl

theorem cell23_3250275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_3250275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250275 prefixEnd_3250275 := by exact prefixLift 3250275
  have htrace : WordTrace (prefixWord ++ tailWord_3250275) baseStart_3250275 baseEnd_3250275 := by
    simpa [prefixWord, tailWord_3250275, baseEnd_3250275] using wordTrace_append hprefix tailTrace_3250275
  have hstable : (prefixWord ++ tailWord_3250275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250275).length < 2 ^ (prefixWord ++ tailWord_3250275).sum := by decide
  have hdescent : baseEnd_3250275 < baseStart_3250275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250324 : List Nat := [2, 4, 2, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_3250324 : Nat := 118140960795 + 3250324 * 2 ^ 59
def prefixEnd_3250324 : Nat := 4983230072969 + 3 ^ 40 * 3250324 * 2
def baseEnd_3250324 : Nat := 1668978494844446326102039

theorem tailTrace_3250324 : CollatzResearch.WordTrace tailWord_3250324 prefixEnd_3250324 1668978494844446326102039 := by
  unfold tailWord_3250324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59274527738319366994827013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79032703651092489326436017 59274527738319366994827013)
  ·
    refine ⟨11113973950934881311530065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59274527738319366994827013 11113973950934881311530065)
    ·
      refine ⟨8335480463201160983647549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11113973950934881311530065 8335480463201160983647549)
      ·
        refine ⟨3125805173700435368867831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8335480463201160983647549 3125805173700435368867831)
        ·
          refine ⟨4688707760550653053301747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125805173700435368867831 4688707760550653053301747)
          ·
            refine ⟨7033061640825979579952621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688707760550653053301747 7033061640825979579952621)
            ·
              refine ⟨2637398115309742342482233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7033061640825979579952621 2637398115309742342482233)
              ·
                refine ⟨1978048586482306756861675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637398115309742342482233 1978048586482306756861675)
                ·
                  refine ⟨2967072879723460135292513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978048586482306756861675 2967072879723460135292513)
                  ·
                    refine ⟨2225304659792595101469385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2967072879723460135292513 2225304659792595101469385)
                    ·
                      refine ⟨1668978494844446326102039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225304659792595101469385 1668978494844446326102039)
                      ·
                        rfl

theorem cell23_3250324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_3250324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250324 prefixEnd_3250324 := by exact prefixLift 3250324
  have htrace : WordTrace (prefixWord ++ tailWord_3250324) baseStart_3250324 baseEnd_3250324 := by
    simpa [prefixWord, tailWord_3250324, baseEnd_3250324] using wordTrace_append hprefix tailTrace_3250324
  have hstable : (prefixWord ++ tailWord_3250324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250324).length < 2 ^ (prefixWord ++ tailWord_3250324).sum := by decide
  have hdescent : baseEnd_3250324 < baseStart_3250324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250332 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3250332 : Nat := 118140960795 + 3250332 * 2 ^ 59
def prefixEnd_3250332 : Nat := 4983230072969 + 3 ^ 40 * 3250332 * 2
def baseEnd_3250332 : Nat := 1668982602689682294802001

theorem tailTrace_3250332 : CollatzResearch.WordTrace tailWord_3250332 prefixEnd_3250332 1668982602689682294802001 := by
  unfold tailWord_3250332
  simp only [CollatzResearch.WordTrace]
  refine ⟨59274673630304875677972625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79032898173739834237296833 59274673630304875677972625)
  ·
    refine ⟨44456005222728656758479469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59274673630304875677972625 44456005222728656758479469)
    ·
      refine ⟨16671001958523246284429801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44456005222728656758479469 16671001958523246284429801)
      ·
        refine ⟨12503251468892434713322351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16671001958523246284429801 12503251468892434713322351)
        ·
          refine ⟨18754877203338652069983527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12503251468892434713322351 18754877203338652069983527)
          ·
            refine ⟨28132315805007978104975291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18754877203338652069983527 28132315805007978104975291)
            ·
              refine ⟨42198473707511967157462937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28132315805007978104975291 42198473707511967157462937)
              ·
                refine ⟨31648855280633975368097203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42198473707511967157462937 31648855280633975368097203)
                ·
                  refine ⟨47473282920950963052145805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31648855280633975368097203 47473282920950963052145805)
                  ·
                    refine ⟨17802481095356611144554677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47473282920950963052145805 17802481095356611144554677)
                    ·
                      refine ⟨1668982602689682294802001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17802481095356611144554677 1668982602689682294802001)
                      ·
                        rfl

theorem cell23_3250332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3250332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250332 prefixEnd_3250332 := by exact prefixLift 3250332
  have htrace : WordTrace (prefixWord ++ tailWord_3250332) baseStart_3250332 baseEnd_3250332 := by
    simpa [prefixWord, tailWord_3250332, baseEnd_3250332] using wordTrace_append hprefix tailTrace_3250332
  have hstable : (prefixWord ++ tailWord_3250332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250332).length < 2 ^ (prefixWord ++ tailWord_3250332).sum := by decide
  have hdescent : baseEnd_3250332 < baseStart_3250332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250340 : List Nat := [2, 3, 1, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_3250340 : Nat := 118140960795 + 3250340 * 2 ^ 59
def prefixEnd_3250340 : Nat := 4983230072969 + 3 ^ 40 * 3250340 * 2
def baseEnd_3250340 : Nat := 1668986710534918263501965

theorem tailTrace_3250340 : CollatzResearch.WordTrace tailWord_3250340 prefixEnd_3250340 1668986710534918263501965 := by
  unfold tailWord_3250340
  simp only [CollatzResearch.WordTrace]
  refine ⟨59274819522290384361118237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79033092696387179148157649 59274819522290384361118237)
  ·
    refine ⟨22228057320858894135419339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59274819522290384361118237 22228057320858894135419339)
    ·
      refine ⟨33342085981288341203129009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22228057320858894135419339 33342085981288341203129009)
      ·
        refine ⟨25006564485966255902346757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33342085981288341203129009 25006564485966255902346757)
        ·
          refine ⟨4688730841118672981690017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25006564485966255902346757 4688730841118672981690017)
          ·
            refine ⟨3516548130839004736267513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688730841118672981690017 3516548130839004736267513)
            ·
              refine ⟨2637411098129253552200635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516548130839004736267513 2637411098129253552200635)
              ·
                refine ⟨3956116647193880328300953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637411098129253552200635 3956116647193880328300953)
                ·
                  refine ⟨2967087485395410246225715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956116647193880328300953 2967087485395410246225715)
                  ·
                    refine ⟨4450631228093115369338573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2967087485395410246225715 4450631228093115369338573)
                    ·
                      refine ⟨1668986710534918263501965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4450631228093115369338573 1668986710534918263501965)
                      ·
                        rfl

theorem cell23_3250340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_3250340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250340 prefixEnd_3250340 := by exact prefixLift 3250340
  have htrace : WordTrace (prefixWord ++ tailWord_3250340) baseStart_3250340 baseEnd_3250340 := by
    simpa [prefixWord, tailWord_3250340, baseEnd_3250340] using wordTrace_append hprefix tailTrace_3250340
  have hstable : (prefixWord ++ tailWord_3250340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250340).length < 2 ^ (prefixWord ++ tailWord_3250340).sum := by decide
  have hdescent : baseEnd_3250340 < baseStart_3250340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250349 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3250349 : Nat := 118140960795 + 3250349 * 2 ^ 59
def prefixEnd_3250349 : Nat := 4983230072969 + 3 ^ 40 * 3250349 * 2
def baseEnd_3250349 : Nat := 1668991331860808728289423

theorem tailTrace_3250349 : CollatzResearch.WordTrace tailWord_3250349 prefixEnd_3250349 1668991331860808728289423 := by
  unfold tailWord_3250349
  simp only [CollatzResearch.WordTrace]
  refine ⟨118549967301548163259314101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79033311534365442172876067 118549967301548163259314101)
  ·
    refine ⟨11114059434520140305560697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118549967301548163259314101 11114059434520140305560697)
    ·
      refine ⟨8335544575890105229170523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11114059434520140305560697 8335544575890105229170523)
      ·
        refine ⟨12503316863835157843755785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8335544575890105229170523 12503316863835157843755785)
        ·
          refine ⟨9377487647876368382816839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12503316863835157843755785 9377487647876368382816839)
          ·
            refine ⟨14066231471814552574225259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9377487647876368382816839 14066231471814552574225259)
            ·
              refine ⟨21099347207721828861337889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14066231471814552574225259 21099347207721828861337889)
              ·
                refine ⟨15824510405791371646003417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21099347207721828861337889 15824510405791371646003417)
                ·
                  refine ⟨11868382804343528734502563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15824510405791371646003417 11868382804343528734502563)
                  ·
                    refine ⟨17802574206515293101753845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11868382804343528734502563 17802574206515293101753845)
                    ·
                      refine ⟨1668991331860808728289423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17802574206515293101753845 1668991331860808728289423)
                      ·
                        rfl

theorem cell23_3250349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3250349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250349 prefixEnd_3250349 := by exact prefixLift 3250349
  have htrace : WordTrace (prefixWord ++ tailWord_3250349) baseStart_3250349 baseEnd_3250349 := by
    simpa [prefixWord, tailWord_3250349, baseEnd_3250349] using wordTrace_append hprefix tailTrace_3250349
  have hstable : (prefixWord ++ tailWord_3250349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250349).length < 2 ^ (prefixWord ++ tailWord_3250349).sum := by decide
  have hdescent : baseEnd_3250349 < baseStart_3250349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250350 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3250350 : Nat := 118140960795 + 3250350 * 2 ^ 59
def prefixEnd_3250350 : Nat := 4983230072969 + 3 ^ 40 * 3250350 * 2
def baseEnd_3250350 : Nat := 1668991845341463224376919

theorem tailTrace_3250350 : CollatzResearch.WordTrace tailWord_3250350 prefixEnd_3250350 1668991845341463224376919 := by
  unfold tailWord_3250350
  simp only [CollatzResearch.WordTrace]
  refine ⟨14818750471818067553762563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79033335849696360286733669 14818750471818067553762563)
  ·
    refine ⟨22228125707727101330643845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14818750471818067553762563 22228125707727101330643845)
    ·
      refine ⟨4167773570198831499495721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22228125707727101330643845 4167773570198831499495721)
      ·
        refine ⟨3125830177649123624621791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4167773570198831499495721 3125830177649123624621791)
        ·
          refine ⟨4688745266473685436932687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125830177649123624621791 4688745266473685436932687)
          ·
            refine ⟨7033117899710528155399031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688745266473685436932687 7033117899710528155399031)
            ·
              refine ⟨10549676849565792233098547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033117899710528155399031 10549676849565792233098547)
              ·
                refine ⟨15824515274348688349647821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10549676849565792233098547 15824515274348688349647821)
                ·
                  refine ⟨5934193227880758131117933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15824515274348688349647821 5934193227880758131117933)
                  ·
                    refine ⟨2225322460455284299169225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5934193227880758131117933 2225322460455284299169225)
                    ·
                      refine ⟨1668991845341463224376919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225322460455284299169225 1668991845341463224376919)
                      ·
                        rfl

theorem cell23_3250350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3250350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250350 prefixEnd_3250350 := by exact prefixLift 3250350
  have htrace : WordTrace (prefixWord ++ tailWord_3250350) baseStart_3250350 baseEnd_3250350 := by
    simpa [prefixWord, tailWord_3250350, baseEnd_3250350] using wordTrace_append hprefix tailTrace_3250350
  have hstable : (prefixWord ++ tailWord_3250350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250350).length < 2 ^ (prefixWord ++ tailWord_3250350).sum := by decide
  have hdescent : baseEnd_3250350 < baseStart_3250350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250386 : List Nat := [3, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_3250386 : Nat := 118140960795 + 3250386 * 2 ^ 59
def prefixEnd_3250386 : Nat := 4983230072969 + 3 ^ 40 * 3250386 * 2
def baseEnd_3250386 : Nat := 185445592293891675947417

theorem tailTrace_3250386 : CollatzResearch.WordTrace tailWord_3250386 prefixEnd_3250386 185445592293891675947417 := by
  unfold tailWord_3250386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29637829200603529644602753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79034211201609412385607341 29637829200603529644602753)
  ·
    refine ⟨22228371900452647233452065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29637829200603529644602753 22228371900452647233452065)
    ·
      refine ⟨16671278925339485425089049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22228371900452647233452065 16671278925339485425089049)
      ·
        refine ⟨12503459194004614068816787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16671278925339485425089049 12503459194004614068816787)
        ·
          refine ⟨18755188791006921103225181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12503459194004614068816787 18755188791006921103225181)
          ·
            refine ⟨7033195796627595413709443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18755188791006921103225181 7033195796627595413709443)
            ·
              refine ⟨10549793694941393120564165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033195796627595413709443 10549793694941393120564165)
              ·
                refine ⟨1978086317801511210105781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10549793694941393120564165 1978086317801511210105781)
                ·
                  refine ⟨185445592293891675947417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978086317801511210105781 185445592293891675947417)
                  ·
                    rfl

theorem cell23_3250386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_3250386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250386 prefixEnd_3250386 := by exact prefixLift 3250386
  have htrace : WordTrace (prefixWord ++ tailWord_3250386) baseStart_3250386 baseEnd_3250386 := by
    simpa [prefixWord, tailWord_3250386, baseEnd_3250386] using wordTrace_append hprefix tailTrace_3250386
  have hstable : (prefixWord ++ tailWord_3250386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250386).length < 2 ^ (prefixWord ++ tailWord_3250386).sum := by decide
  have hdescent : baseEnd_3250386 < baseStart_3250386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250419 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 1, 6, 2]
def baseStart_3250419 : Nat := 118140960795 + 3250419 * 2 ^ 59
def prefixEnd_3250419 : Nat := 4983230072969 + 3 ^ 40 * 3250419 * 2
def baseEnd_3250419 : Nat := 1669027275506623454414101

theorem tailTrace_3250419 : CollatzResearch.WordTrace tailWord_3250419 prefixEnd_3250419 1669027275506623454414101 := by
  unfold tailWord_3250419
  simp only [CollatzResearch.WordTrace]
  refine ⟨118552520411294565214362311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79035013607529710142908207 118552520411294565214362311)
  ·
    refine ⟨177828780616941847821543467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118552520411294565214362311 177828780616941847821543467)
    ·
      refine ⟨266743170925412771732315201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177828780616941847821543467 266743170925412771732315201)
      ·
        refine ⟨200057378194059578799236401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266743170925412771732315201 200057378194059578799236401)
        ·
          refine ⟨150043033645544684099427301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200057378194059578799236401 150043033645544684099427301)
          ·
            refine ⟨28133068808539628268642619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150043033645544684099427301 28133068808539628268642619)
            ·
              refine ⟨42199603212809442402963929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28133068808539628268642619 42199603212809442402963929)
              ·
                refine ⟨31649702409607081802222947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42199603212809442402963929 31649702409607081802222947)
                ·
                  refine ⟨47474553614410622703334421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31649702409607081802222947 47474553614410622703334421)
                  ·
                    refine ⟨2225369700675497939218801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 47474553614410622703334421 2225369700675497939218801)
                    ·
                      refine ⟨1669027275506623454414101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225369700675497939218801 1669027275506623454414101)
                      ·
                        rfl

theorem cell23_3250419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 6, 2].length) (baseStart_3250419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250419 prefixEnd_3250419 := by exact prefixLift 3250419
  have htrace : WordTrace (prefixWord ++ tailWord_3250419) baseStart_3250419 baseEnd_3250419 := by
    simpa [prefixWord, tailWord_3250419, baseEnd_3250419] using wordTrace_append hprefix tailTrace_3250419
  have hstable : (prefixWord ++ tailWord_3250419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250419).length < 2 ^ (prefixWord ++ tailWord_3250419).sum := by decide
  have hdescent : baseEnd_3250419 < baseStart_3250419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250432 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_3250432 : Nat := 118140960795 + 3250432 * 2 ^ 59
def prefixEnd_3250432 : Nat := 4983230072969 + 3 ^ 40 * 3250432 * 2
def baseEnd_3250432 : Nat := 1669033950755131903551541

theorem tailTrace_3250432 : CollatzResearch.WordTrace tailWord_3250432 prefixEnd_3250432 1669033950755131903551541 := by
  unfold tailWord_3250432
  simp only [CollatzResearch.WordTrace]
  refine ⟨59276497280123734217292775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79035329706831645623057033 59276497280123734217292775)
  ·
    refine ⟨88914745920185601325939163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59276497280123734217292775 88914745920185601325939163)
    ·
      refine ⟨133372118880278401988908745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88914745920185601325939163 133372118880278401988908745)
      ·
        refine ⟨100029089160208801491681559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133372118880278401988908745 100029089160208801491681559)
        ·
          refine ⟨150043633740313202237522339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100029089160208801491681559 150043633740313202237522339)
          ·
            refine ⟨225065450610469803356283509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150043633740313202237522339 225065450610469803356283509)
            ·
              refine ⟨21099885994731544064651579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225065450610469803356283509 21099885994731544064651579)
              ·
                refine ⟨31649828992097316096977369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21099885994731544064651579 31649828992097316096977369)
                ·
                  refine ⟨23737371744072987072733027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31649828992097316096977369 23737371744072987072733027)
                  ·
                    refine ⟨35606057616109480609099541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23737371744072987072733027 35606057616109480609099541)
                    ·
                      refine ⟨1669033950755131903551541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35606057616109480609099541 1669033950755131903551541)
                      ·
                        rfl

theorem cell23_3250432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_3250432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250432 prefixEnd_3250432 := by exact prefixLift 3250432
  have htrace : WordTrace (prefixWord ++ tailWord_3250432) baseStart_3250432 baseEnd_3250432 := by
    simpa [prefixWord, tailWord_3250432, baseEnd_3250432] using wordTrace_append hprefix tailTrace_3250432
  have hstable : (prefixWord ++ tailWord_3250432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250432).length < 2 ^ (prefixWord ++ tailWord_3250432).sum := by decide
  have hdescent : baseEnd_3250432 < baseStart_3250432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250446 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3250446 : Nat := 118140960795 + 3250446 * 2 ^ 59
def prefixEnd_3250446 : Nat := 4983230072969 + 3 ^ 40 * 3250446 * 2
def baseEnd_3250446 : Nat := 556347046494764949592159

theorem tailTrace_3250446 : CollatzResearch.WordTrace tailWord_3250446 prefixEnd_3250446 556347046494764949592159 := by
  unfold tailWord_3250446
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819188147774593603199399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79035670121464499217063461 14819188147774593603199399)
  ·
    refine ⟨22228782221661890404799099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14819188147774593603199399 22228782221661890404799099)
    ·
      refine ⟨33343173332492835607198649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22228782221661890404799099 33343173332492835607198649)
      ·
        refine ⟨25007379999369626705398987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33343173332492835607198649 25007379999369626705398987)
        ·
          refine ⟨37511069999054440058098481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25007379999369626705398987 37511069999054440058098481)
          ·
            refine ⟨28133302499290830043573861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37511069999054440058098481 28133302499290830043573861)
            ·
              refine ⟨5274994218617030633170099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28133302499290830043573861 5274994218617030633170099)
              ·
                refine ⟨7912491327925545949755149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5274994218617030633170099 7912491327925545949755149)
                ·
                  refine ⟨2967184247972079731158181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7912491327925545949755149 2967184247972079731158181)
                  ·
                    refine ⟨556347046494764949592159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967184247972079731158181 556347046494764949592159)
                    ·
                      rfl

theorem cell23_3250446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3250446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250446 prefixEnd_3250446 := by exact prefixLift 3250446
  have htrace : WordTrace (prefixWord ++ tailWord_3250446) baseStart_3250446 baseEnd_3250446 := by
    simpa [prefixWord, tailWord_3250446, baseEnd_3250446] using wordTrace_append hprefix tailTrace_3250446
  have hstable : (prefixWord ++ tailWord_3250446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250446).length < 2 ^ (prefixWord ++ tailWord_3250446).sum := by decide
  have hdescent : baseEnd_3250446 < baseStart_3250446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250497 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3250497 : Nat := 118140960795 + 3250497 * 2 ^ 59
def prefixEnd_3250497 : Nat := 4983230072969 + 3 ^ 40 * 3250497 * 2
def baseEnd_3250497 : Nat := 556355775665891383079581

theorem tailTrace_3250497 : CollatzResearch.WordTrace tailWord_3250497 prefixEnd_3250497 556355775665891383079581 := by
  unfold tailWord_3250497
  simp only [CollatzResearch.WordTrace]
  refine ⟨118555365305011984535701745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79036910203341323023801163 118555365305011984535701745)
  ·
    refine ⟨88916523978758988401776309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118555365305011984535701745 88916523978758988401776309)
    ·
      refine ⟨8335924123008655162666529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 88916523978758988401776309 8335924123008655162666529)
      ·
        refine ⟨6251943092256491371999897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8335924123008655162666529 6251943092256491371999897)
        ·
          refine ⟨4688957319192368528999923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6251943092256491371999897 4688957319192368528999923)
          ·
            refine ⟨7033435978788552793499885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4688957319192368528999923 7033435978788552793499885)
            ·
              refine ⟨2637538492045707297562457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7033435978788552793499885 2637538492045707297562457)
              ·
                refine ⟨1978153869034280473171843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637538492045707297562457 1978153869034280473171843)
                ·
                  refine ⟨2967230803551420709757765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978153869034280473171843 2967230803551420709757765)
                  ·
                    refine ⟨556355775665891383079581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967230803551420709757765 556355775665891383079581)
                    ·
                      rfl

theorem cell23_3250497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3250497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250497 prefixEnd_3250497 := by exact prefixLift 3250497
  have htrace : WordTrace (prefixWord ++ tailWord_3250497) baseStart_3250497 baseEnd_3250497 := by
    simpa [prefixWord, tailWord_3250497, baseEnd_3250497] using wordTrace_append hprefix tailTrace_3250497
  have hstable : (prefixWord ++ tailWord_3250497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250497).length < 2 ^ (prefixWord ++ tailWord_3250497).sum := by decide
  have hdescent : baseEnd_3250497 < baseStart_3250497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250519 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 1, 6]
def baseStart_3250519 : Nat := 118140960795 + 3250519 * 2 ^ 59
def prefixEnd_3250519 : Nat := 4983230072969 + 3 ^ 40 * 3250519 * 2
def baseEnd_3250519 : Nat := 556359541190691021054547

theorem tailTrace_3250519 : CollatzResearch.WordTrace tailWord_3250519 prefixEnd_3250519 556359541190691021054547 := by
  unfold tailWord_3250519
  simp only [CollatzResearch.WordTrace]
  refine ⟨118556167710932282293002611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79037445140621521528668407 118556167710932282293002611)
  ·
    refine ⟨177834251566398423439503917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118556167710932282293002611 177834251566398423439503917)
    ·
      refine ⟨66687844337399408789813969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177834251566398423439503917 66687844337399408789813969)
      ·
        refine ⟨50015883253049556592360477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66687844337399408789813969 50015883253049556592360477)
        ·
          refine ⟨18755956219893583722135179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50015883253049556592360477 18755956219893583722135179)
          ·
            refine ⟨28133934329840375583202769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18755956219893583722135179 28133934329840375583202769)
            ·
              refine ⟨21100450747380281687402077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28133934329840375583202769 21100450747380281687402077)
              ·
                refine ⟨7912669030267605632775779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21100450747380281687402077 7912669030267605632775779)
                ·
                  refine ⟨11869003545401408449163669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912669030267605632775779 11869003545401408449163669)
                  ·
                    refine ⟨556359541190691021054547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11869003545401408449163669 556359541190691021054547)
                    ·
                      rfl

theorem cell23_3250519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_3250519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250519 prefixEnd_3250519 := by exact prefixLift 3250519
  have htrace : WordTrace (prefixWord ++ tailWord_3250519) baseStart_3250519 baseEnd_3250519 := by
    simpa [prefixWord, tailWord_3250519, baseEnd_3250519] using wordTrace_append hprefix tailTrace_3250519
  have hstable : (prefixWord ++ tailWord_3250519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250519).length < 2 ^ (prefixWord ++ tailWord_3250519).sum := by decide
  have hdescent : baseEnd_3250519 < baseStart_3250519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250530 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3250530 : Nat := 118140960795 + 3250530 * 2 ^ 59
def prefixEnd_3250530 : Nat := 4983230072969 + 3 ^ 40 * 3250530 * 2
def baseEnd_3250530 : Nat := 1669084271859272520126091

theorem tailTrace_3250530 : CollatzResearch.WordTrace tailWord_3250530 prefixEnd_3250530 1669084271859272520126091 := by
  unfold tailWord_3250530
  simp only [CollatzResearch.WordTrace]
  refine ⟨29639142228473107792913261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79037712609261620781102029 29639142228473107792913261)
  ·
    refine ⟨11114678335677415422342473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29639142228473107792913261 11114678335677415422342473)
    ·
      refine ⟨8336008751758061566756855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11114678335677415422342473 8336008751758061566756855)
      ·
        refine ⟨12504013127637092350135283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8336008751758061566756855 12504013127637092350135283)
        ·
          refine ⟨18756019691455638525202925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12504013127637092350135283 18756019691455638525202925)
          ·
            refine ⟨7033507384295864446951097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18756019691455638525202925 7033507384295864446951097)
            ·
              refine ⟨5275130538221898335213323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7033507384295864446951097 5275130538221898335213323)
              ·
                refine ⟨7912695807332847502819985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275130538221898335213323 7912695807332847502819985)
                ·
                  refine ⟨5934521855499635627114989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7912695807332847502819985 5934521855499635627114989)
                  ·
                    refine ⟨2225445695812363360168121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5934521855499635627114989 2225445695812363360168121)
                    ·
                      refine ⟨1669084271859272520126091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225445695812363360168121 1669084271859272520126091)
                      ·
                        rfl

theorem cell23_3250530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3250530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250530 prefixEnd_3250530 := by exact prefixLift 3250530
  have htrace : WordTrace (prefixWord ++ tailWord_3250530) baseStart_3250530 baseEnd_3250530 := by
    simpa [prefixWord, tailWord_3250530, baseEnd_3250530] using wordTrace_append hprefix tailTrace_3250530
  have hstable : (prefixWord ++ tailWord_3250530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250530).length < 2 ^ (prefixWord ++ tailWord_3250530).sum := by decide
  have hdescent : baseEnd_3250530 < baseStart_3250530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250536 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_3250536 : Nat := 118140960795 + 3250536 * 2 ^ 59
def prefixEnd_3250536 : Nat := 4983230072969 + 3 ^ 40 * 3250536 * 2
def baseEnd_3250536 : Nat := 556362450914399832217021

theorem tailTrace_3250536 : CollatzResearch.WordTrace tailWord_3250536 prefixEnd_3250536 556362450914399832217021 := by
  unfold tailWord_3250536
  simp only [CollatzResearch.WordTrace]
  refine ⟨59278393875935347098185731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79037858501247129464247641 59278393875935347098185731)
  ·
    refine ⟨88917590813903020647278597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59278393875935347098185731 88917590813903020647278597)
    ·
      refine ⟨16672048277606816371364737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88917590813903020647278597 16672048277606816371364737)
      ·
        refine ⟨12504036208205112278523553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16672048277606816371364737 12504036208205112278523553)
        ·
          refine ⟨9378027156153834208892665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12504036208205112278523553 9378027156153834208892665)
          ·
            refine ⟨7033520367115375656669499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9378027156153834208892665 7033520367115375656669499)
            ·
              refine ⟨10550280550673063485004249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7033520367115375656669499 10550280550673063485004249)
              ·
                refine ⟨7912710413004797613753187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550280550673063485004249 7912710413004797613753187)
                ·
                  refine ⟨11869065619507196420629781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912710413004797613753187 11869065619507196420629781)
                  ·
                    refine ⟨556362450914399832217021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11869065619507196420629781 556362450914399832217021)
                    ·
                      rfl

theorem cell23_3250536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_3250536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250536 prefixEnd_3250536 := by exact prefixLift 3250536
  have htrace : WordTrace (prefixWord ++ tailWord_3250536) baseStart_3250536 baseEnd_3250536 := by
    simpa [prefixWord, tailWord_3250536, baseEnd_3250536] using wordTrace_append hprefix tailTrace_3250536
  have hstable : (prefixWord ++ tailWord_3250536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250536).length < 2 ^ (prefixWord ++ tailWord_3250536).sum := by decide
  have hdescent : baseEnd_3250536 < baseStart_3250536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250539 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4]
def baseStart_3250539 : Nat := 118140960795 + 3250539 * 2 ^ 59
def prefixEnd_3250539 : Nat := 4983230072969 + 3 ^ 40 * 3250539 * 2
def baseEnd_3250539 : Nat := 1669088893185162984913549

theorem tailTrace_3250539 : CollatzResearch.WordTrace tailWord_3250539 prefixEnd_3250539 1669088893185162984913549 := by
  unfold tailWord_3250539
  simp only [CollatzResearch.WordTrace]
  refine ⟨118556897170859825708730671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79037931447239883805820447 118556897170859825708730671)
  ·
    refine ⟨177835345756289738563096007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118556897170859825708730671 177835345756289738563096007)
    ·
      refine ⟨266753018634434607844644011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177835345756289738563096007 266753018634434607844644011)
      ·
        refine ⟨400129527951651911766966017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266753018634434607844644011 400129527951651911766966017)
        ·
          refine ⟨300097145963738933825224513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400129527951651911766966017 300097145963738933825224513)
          ·
            refine ⟨225072859472804200368918385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300097145963738933825224513 225072859472804200368918385)
            ·
              refine ⟨168804644604603150276688789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225072859472804200368918385 168804644604603150276688789)
              ·
                refine ⟨7912717715840772669219787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168804644604603150276688789 7912717715840772669219787)
                ·
                  refine ⟨11869076573761159003829681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912717715840772669219787 11869076573761159003829681)
                  ·
                    refine ⟨8901807430320869252872261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11869076573761159003829681 8901807430320869252872261)
                    ·
                      refine ⟨1669088893185162984913549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8901807430320869252872261 1669088893185162984913549)
                      ·
                        rfl

theorem cell23_3250539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_3250539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250539 prefixEnd_3250539 := by exact prefixLift 3250539
  have htrace : WordTrace (prefixWord ++ tailWord_3250539) baseStart_3250539 baseEnd_3250539 := by
    simpa [prefixWord, tailWord_3250539, baseEnd_3250539] using wordTrace_append hprefix tailTrace_3250539
  have hstable : (prefixWord ++ tailWord_3250539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250539).length < 2 ^ (prefixWord ++ tailWord_3250539).sum := by decide
  have hdescent : baseEnd_3250539 < baseStart_3250539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250546 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3250546 : Nat := 118140960795 + 3250546 * 2 ^ 59
def prefixEnd_3250546 : Nat := 4983230072969 + 3 ^ 40 * 3250546 * 2
def baseEnd_3250546 : Nat := 1669092487549744457526017

theorem tailTrace_3250546 : CollatzResearch.WordTrace tailWord_3250546 prefixEnd_3250546 1669092487549744457526017 := by
  unfold tailWord_3250546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29639288120458616476058873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79038101654556310602823661 29639288120458616476058873)
  ·
    refine ⟨22229466090343962357044155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29639288120458616476058873 22229466090343962357044155)
    ·
      refine ⟨33344199135515943535566233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22229466090343962357044155 33344199135515943535566233)
      ·
        refine ⟨25008149351636957651674675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33344199135515943535566233 25008149351636957651674675)
        ·
          refine ⟨37512224027455436477512013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25008149351636957651674675 37512224027455436477512013)
          ·
            refine ⟨14067084010295788679067005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37512224027455436477512013 14067084010295788679067005)
            ·
              refine ⟨5275156503860920754650127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14067084010295788679067005 5275156503860920754650127)
              ·
                refine ⟨7912734755791381131975191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275156503860920754650127 7912734755791381131975191)
                ·
                  refine ⟨11869102133687071697962787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912734755791381131975191 11869102133687071697962787)
                  ·
                    refine ⟨17803653200530607546944181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11869102133687071697962787 17803653200530607546944181)
                    ·
                      refine ⟨1669092487549744457526017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17803653200530607546944181 1669092487549744457526017)
                      ·
                        rfl

theorem cell23_3250546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3250546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250546 prefixEnd_3250546 := by exact prefixLift 3250546
  have htrace : WordTrace (prefixWord ++ tailWord_3250546) baseStart_3250546 baseEnd_3250546 := by
    simpa [prefixWord, tailWord_3250546, baseEnd_3250546] using wordTrace_append hprefix tailTrace_3250546
  have hstable : (prefixWord ++ tailWord_3250546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250546).length < 2 ^ (prefixWord ++ tailWord_3250546).sum := by decide
  have hdescent : baseEnd_3250546 < baseStart_3250546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250549 : List Nat := [1, 3, 4, 1, 2, 12]
def baseStart_3250549 : Nat := 118140960795 + 3250549 * 2 ^ 59
def prefixEnd_3250549 : Nat := 4983230072969 + 3 ^ 40 * 3250549 * 2
def baseEnd_3250549 : Nat := 6868699703669580023821

theorem tailTrace_3250549 : CollatzResearch.WordTrace tailWord_3250549 prefixEnd_3250549 6868699703669580023821 := by
  unfold tailWord_3250549
  simp only [CollatzResearch.WordTrace]
  refine ⟨118557261900823597416594701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79038174600549064944396467 118557261900823597416594701)
  ·
    refine ⟨44458973212808849031223013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118557261900823597416594701 44458973212808849031223013)
    ·
      refine ⟨8336057477401659193354315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44458973212808849031223013 8336057477401659193354315)
      ·
        refine ⟨12504086216102488790031473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8336057477401659193354315 12504086216102488790031473)
        ·
          refine ⟨9378064662076866592523605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12504086216102488790031473 9378064662076866592523605)
          ·
            refine ⟨6868699703669580023821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9378064662076866592523605 6868699703669580023821)
            ·
              rfl

theorem cell23_3250549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 12].length) (baseStart_3250549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250549 prefixEnd_3250549 := by exact prefixLift 3250549
  have htrace : WordTrace (prefixWord ++ tailWord_3250549) baseStart_3250549 baseEnd_3250549 := by
    simpa [prefixWord, tailWord_3250549, baseEnd_3250549] using wordTrace_append hprefix tailTrace_3250549
  have hstable : (prefixWord ++ tailWord_3250549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250549).length < 2 ^ (prefixWord ++ tailWord_3250549).sum := by decide
  have hdescent : baseEnd_3250549 < baseStart_3250549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250633 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 1, 4, 2]
def baseStart_3250633 : Nat := 118140960795 + 3250633 * 2 ^ 59
def prefixEnd_3250633 : Nat := 4983230072969 + 3 ^ 40 * 3250633 * 2
def baseEnd_3250633 : Nat := 1669137160366685617138117

theorem tailTrace_3250633 : CollatzResearch.WordTrace tailWord_3250633 prefixEnd_3250633 1669137160366685617138117 := by
  unfold tailWord_3250633
  simp only [CollatzResearch.WordTrace]
  refine ⟨118560325632519279762652553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79040217088346186508435035 118560325632519279762652553)
  ·
    refine ⟨88920244224389459821989415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118560325632519279762652553 88920244224389459821989415)
    ·
      refine ⟨133380366336584189732984123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88920244224389459821989415 133380366336584189732984123)
      ·
        refine ⟨200070549504876284599476185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133380366336584189732984123 200070549504876284599476185)
        ·
          refine ⟨150052912128657213449607139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200070549504876284599476185 150052912128657213449607139)
          ·
            refine ⟨225079368192985820174410709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150052912128657213449607139 225079368192985820174410709)
            ·
              refine ⟨5275297692023105160337751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 225079368192985820174410709 5275297692023105160337751)
              ·
                refine ⟨7912946538034657740506627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5275297692023105160337751 7912946538034657740506627)
                ·
                  refine ⟨11869419807051986610759941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7912946538034657740506627 11869419807051986610759941)
                  ·
                    refine ⟨2225516213822247489517489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11869419807051986610759941 2225516213822247489517489)
                    ·
                      refine ⟨1669137160366685617138117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225516213822247489517489 1669137160366685617138117)
                      ·
                        rfl

theorem cell23_3250633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 1, 4, 2].length) (baseStart_3250633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250633 prefixEnd_3250633 := by exact prefixLift 3250633
  have htrace : WordTrace (prefixWord ++ tailWord_3250633) baseStart_3250633 baseEnd_3250633 := by
    simpa [prefixWord, tailWord_3250633, baseEnd_3250633] using wordTrace_append hprefix tailTrace_3250633
  have hstable : (prefixWord ++ tailWord_3250633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250633).length < 2 ^ (prefixWord ++ tailWord_3250633).sum := by decide
  have hdescent : baseEnd_3250633 < baseStart_3250633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250723 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4]
def baseStart_3250723 : Nat := 118140960795 + 3250723 * 2 ^ 59
def prefixEnd_3250723 : Nat := 4983230072969 + 3 ^ 40 * 3250723 * 2
def baseEnd_3250723 : Nat := 1669183373625590265012703

theorem tailTrace_3250723 : CollatzResearch.WordTrace tailWord_3250723 prefixEnd_3250723 1669183373625590265012703 := by
  unfold tailWord_3250723
  simp only [CollatzResearch.WordTrace]
  refine ⟨118563608202193225133428823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79042405468128816755619215 118563608202193225133428823)
  ·
    refine ⟨177845412303289837700143235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118563608202193225133428823 177845412303289837700143235)
    ·
      refine ⟨266768118454934756550214853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177845412303289837700143235 266768118454934756550214853)
      ·
        refine ⟨50019022210300266853165285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266768118454934756550214853 50019022210300266853165285)
        ·
          refine ⟨9378566664431300034968491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50019022210300266853165285 9378566664431300034968491)
          ·
            refine ⟨14067849996646950052452737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9378566664431300034968491 14067849996646950052452737)
            ·
              refine ⟨10550887497485212539339553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14067849996646950052452737 10550887497485212539339553)
              ·
                refine ⟨7913165623113909404504665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10550887497485212539339553 7913165623113909404504665)
                ·
                  refine ⟨5934874217335432053378499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913165623113909404504665 5934874217335432053378499)
                  ·
                    refine ⟨8902311326003148080067749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5934874217335432053378499 8902311326003148080067749)
                    ·
                      refine ⟨1669183373625590265012703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8902311326003148080067749 1669183373625590265012703)
                      ·
                        rfl

theorem cell23_3250723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_3250723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250723 prefixEnd_3250723 := by exact prefixLift 3250723
  have htrace : WordTrace (prefixWord ++ tailWord_3250723) baseStart_3250723 baseEnd_3250723 := by
    simpa [prefixWord, tailWord_3250723, baseEnd_3250723] using wordTrace_append hprefix tailTrace_3250723
  have hstable : (prefixWord ++ tailWord_3250723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250723).length < 2 ^ (prefixWord ++ tailWord_3250723).sum := by decide
  have hdescent : baseEnd_3250723 < baseStart_3250723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250724 : List Nat := [2, 3, 1, 5, 1, 2, 2, 2, 5]
def baseStart_3250724 : Nat := 118140960795 + 3250724 * 2 ^ 59
def prefixEnd_3250724 : Nat := 4983230072969 + 3 ^ 40 * 3250724 * 2
def baseEnd_3250724 : Nat := 185464876345138306788911

theorem tailTrace_3250724 : CollatzResearch.WordTrace tailWord_3250724 prefixEnd_3250724 185464876345138306788911 := by
  unfold tailWord_3250724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59281822337594801152107613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79042429783459734869476817 59281822337594801152107613)
  ·
    refine ⟨22230683376598050432040355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59281822337594801152107613 22230683376598050432040355)
    ·
      refine ⟨33346025064897075648060533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22230683376598050432040355 33346025064897075648060533)
      ·
        refine ⟨3126189849834100842005675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33346025064897075648060533 3126189849834100842005675)
        ·
          refine ⟨4689284774751151263008513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126189849834100842005675 4689284774751151263008513)
          ·
            refine ⟨3516963581063363447256385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689284774751151263008513 3516963581063363447256385)
            ·
              refine ⟨2637722685797522585442289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3516963581063363447256385 2637722685797522585442289)
              ·
                refine ⟨1978292014348141939081717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2637722685797522585442289 1978292014348141939081717)
                ·
                  refine ⟨185464876345138306788911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1978292014348141939081717 185464876345138306788911)
                  ·
                    rfl

theorem cell23_3250724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_3250724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250724 prefixEnd_3250724 := by exact prefixLift 3250724
  have htrace : WordTrace (prefixWord ++ tailWord_3250724) baseStart_3250724 baseEnd_3250724 := by
    simpa [prefixWord, tailWord_3250724, baseEnd_3250724] using wordTrace_append hprefix tailTrace_3250724
  have hstable : (prefixWord ++ tailWord_3250724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250724).length < 2 ^ (prefixWord ++ tailWord_3250724).sum := by decide
  have hdescent : baseEnd_3250724 < baseStart_3250724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250823 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 6, 4]
def baseStart_3250823 : Nat := 118140960795 + 3250823 * 2 ^ 59
def prefixEnd_3250823 : Nat := 4983230072969 + 3 ^ 40 * 3250823 * 2
def baseEnd_3250823 : Nat := 556411573897013291254081

theorem tailTrace_3250823 : CollatzResearch.WordTrace tailWord_3250823 prefixEnd_3250823 556411573897013291254081 := by
  unfold tailWord_3250823
  simp only [CollatzResearch.WordTrace]
  refine ⟨118567255501830942212069123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79044837001220628141379415 118567255501830942212069123)
  ·
    refine ⟨177850883252746413318103685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118567255501830942212069123 177850883252746413318103685)
    ·
      refine ⟨33347040609889952497144441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177850883252746413318103685 33347040609889952497144441)
      ·
        refine ⟨25010280457417464372858331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33347040609889952497144441 25010280457417464372858331)
        ·
          refine ⟨37515420686126196559287497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25010280457417464372858331 37515420686126196559287497)
          ·
            refine ⟨28136565514594647419465623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37515420686126196559287497 28136565514594647419465623)
            ·
              refine ⟨42204848271891971129198435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28136565514594647419465623 42204848271891971129198435)
              ·
                refine ⟨63307272407837956693797653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42204848271891971129198435 63307272407837956693797653)
                ·
                  refine ⟨2967528394117404220021765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63307272407837956693797653 2967528394117404220021765)
                  ·
                    refine ⟨556411573897013291254081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967528394117404220021765 556411573897013291254081)
                    ·
                      rfl

theorem cell23_3250823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_3250823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250823 prefixEnd_3250823 := by exact prefixLift 3250823
  have htrace : WordTrace (prefixWord ++ tailWord_3250823) baseStart_3250823 baseEnd_3250823 := by
    simpa [prefixWord, tailWord_3250823, baseEnd_3250823] using wordTrace_append hprefix tailTrace_3250823
  have hstable : (prefixWord ++ tailWord_3250823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250823).length < 2 ^ (prefixWord ++ tailWord_3250823).sum := by decide
  have hdescent : baseEnd_3250823 < baseStart_3250823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250830 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3250830 : Nat := 118140960795 + 3250830 * 2 ^ 59
def prefixEnd_3250830 : Nat := 4983230072969 + 3 ^ 40 * 3250830 * 2
def baseEnd_3250830 : Nat := 1669238316055621346374711

theorem tailTrace_3250830 : CollatzResearch.WordTrace tailWord_3250830 prefixEnd_3250830 1669238316055621346374711 := by
  unfold tailWord_3250830
  simp only [CollatzResearch.WordTrace]
  refine ⟨14820938851600697800946743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79045007208537054938382629 14820938851600697800946743)
  ·
    refine ⟨22231408277401046701420115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14820938851600697800946743 22231408277401046701420115)
    ·
      refine ⟨33347112416101570052130173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22231408277401046701420115 33347112416101570052130173)
      ·
        refine ⟨12505167156038088769548815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33347112416101570052130173 12505167156038088769548815)
        ·
          refine ⟨18757750734057133154323223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12505167156038088769548815 18757750734057133154323223)
          ·
            refine ⟨28136626101085699731484835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18757750734057133154323223 28136626101085699731484835)
            ·
              refine ⟨42204939151628549597227253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28136626101085699731484835 42204939151628549597227253)
              ·
                refine ⟨3956713045465176524740055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42204939151628549597227253 3956713045465176524740055)
                ·
                  refine ⟨5935069568197764787110083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956713045465176524740055 5935069568197764787110083)
                  ·
                    refine ⟨8902604352296647180665125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935069568197764787110083 8902604352296647180665125)
                    ·
                      refine ⟨1669238316055621346374711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8902604352296647180665125 1669238316055621346374711)
                      ·
                        rfl

theorem cell23_3250830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3250830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250830 prefixEnd_3250830 := by exact prefixLift 3250830
  have htrace : WordTrace (prefixWord ++ tailWord_3250830) baseStart_3250830 baseEnd_3250830 := by
    simpa [prefixWord, tailWord_3250830, baseEnd_3250830] using wordTrace_append hprefix tailTrace_3250830
  have hstable : (prefixWord ++ tailWord_3250830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250830).length < 2 ^ (prefixWord ++ tailWord_3250830).sum := by decide
  have hdescent : baseEnd_3250830 < baseStart_3250830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250840 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_3250840 : Nat := 118140960795 + 3250840 * 2 ^ 59
def prefixEnd_3250840 : Nat := 4983230072969 + 3 ^ 40 * 3250840 * 2
def baseEnd_3250840 : Nat := 556414483620722102416555

theorem tailTrace_3250840 : CollatzResearch.WordTrace tailWord_3250840 prefixEnd_3250840 556414483620722102416555 := by
  unfold tailWord_3250840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59283937771384677057718987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79045250361846236076958649 59283937771384677057718987)
  ·
    refine ⟨88925906657077015586578481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59283937771384677057718987 88925906657077015586578481)
    ·
      refine ⟨66694429992807761689933861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88925906657077015586578481 66694429992807761689933861)
      ·
        refine ⟨12505205623651455316862599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66694429992807761689933861 12505205623651455316862599)
        ·
          refine ⟨18757808435477182975293899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12505205623651455316862599 18757808435477182975293899)
          ·
            refine ⟨28136712653215774462940849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18757808435477182975293899 28136712653215774462940849)
            ·
              refine ⟨21102534489911830847205637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28136712653215774462940849 21102534489911830847205637)
              ·
                refine ⟨3956725216858468283851057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21102534489911830847205637 3956725216858468283851057)
                ·
                  refine ⟨2967543912643851212888293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956725216858468283851057 2967543912643851212888293)
                  ·
                    refine ⟨556414483620722102416555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2967543912643851212888293 556414483620722102416555)
                    ·
                      rfl

theorem cell23_3250840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_3250840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250840 prefixEnd_3250840 := by exact prefixLift 3250840
  have htrace : WordTrace (prefixWord ++ tailWord_3250840) baseStart_3250840 baseEnd_3250840 := by
    simpa [prefixWord, tailWord_3250840, baseEnd_3250840] using wordTrace_append hprefix tailTrace_3250840
  have hstable : (prefixWord ++ tailWord_3250840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250840).length < 2 ^ (prefixWord ++ tailWord_3250840).sum := by decide
  have hdescent : baseEnd_3250840 < baseStart_3250840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250867 : List Nat := [1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 3]
def baseStart_3250867 : Nat := 118140960795 + 3250867 * 2 ^ 59
def prefixEnd_3250867 : Nat := 4983230072969 + 3 ^ 40 * 3250867 * 2
def baseEnd_3250867 : Nat := 1669257314839837701612041

theorem tailTrace_3250867 : CollatzResearch.WordTrace tailWord_3250867 prefixEnd_3250867 1669257314839837701612041 := by
  unfold tailWord_3250867
  simp only [CollatzResearch.WordTrace]
  refine ⟨118568860313671537726670855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79045906875781025151113903 118568860313671537726670855)
  ·
    refine ⟨177853290470507306590006283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118568860313671537726670855 177853290470507306590006283)
    ·
      refine ⟨266779935705760959885009425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177853290470507306590006283 266779935705760959885009425)
      ·
        refine ⟨200084951779320719913757069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266779935705760959885009425 200084951779320719913757069)
        ·
          refine ⟨75031856917245269967658901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200084951779320719913757069 75031856917245269967658901)
          ·
            refine ⟨3517118292995872029734011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75031856917245269967658901 3517118292995872029734011)
            ·
              refine ⟨5275677439493808044601017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517118292995872029734011 5275677439493808044601017)
              ·
                refine ⟨3956758079620356033450763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275677439493808044601017 3956758079620356033450763)
                ·
                  refine ⟨5935137119430534050176145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956758079620356033450763 5935137119430534050176145)
                  ·
                    refine ⟨4451352839572900537632109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5935137119430534050176145 4451352839572900537632109)
                    ·
                      refine ⟨1669257314839837701612041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451352839572900537632109 1669257314839837701612041)
                      ·
                        rfl

theorem cell23_3250867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_3250867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250867 prefixEnd_3250867 := by exact prefixLift 3250867
  have htrace : WordTrace (prefixWord ++ tailWord_3250867) baseStart_3250867 baseEnd_3250867 := by
    simpa [prefixWord, tailWord_3250867, baseEnd_3250867] using wordTrace_append hprefix tailTrace_3250867
  have hstable : (prefixWord ++ tailWord_3250867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250867).length < 2 ^ (prefixWord ++ tailWord_3250867).sum := by decide
  have hdescent : baseEnd_3250867 < baseStart_3250867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250880 : List Nat := [2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3]
def baseStart_3250880 : Nat := 118140960795 + 3250880 * 2 ^ 59
def prefixEnd_3250880 : Nat := 4983230072969 + 3 ^ 40 * 3250880 * 2
def baseEnd_3250880 : Nat := 1669263990088346150749481

theorem tailTrace_3250880 : CollatzResearch.WordTrace tailWord_3250880 prefixEnd_3250880 1669263990088346150749481 := by
  unfold tailWord_3250880
  simp only [CollatzResearch.WordTrace]
  refine ⟨59284667231312220473447047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79046222975082960631262729 59284667231312220473447047)
  ·
    refine ⟨88927000846968330710170571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59284667231312220473447047 88927000846968330710170571)
    ·
      refine ⟨133390501270452496065255857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88927000846968330710170571 133390501270452496065255857)
      ·
        refine ⟨100042875952839372048941893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133390501270452496065255857 100042875952839372048941893)
        ·
          refine ⟨18758039241157382259176605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100042875952839372048941893 18758039241157382259176605)
          ·
            refine ⟨7034264715434018347191227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18758039241157382259176605 7034264715434018347191227)
            ·
              refine ⟨10551397073151027520786841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034264715434018347191227 10551397073151027520786841)
              ·
                refine ⟨7913547804863270640590131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10551397073151027520786841 7913547804863270640590131)
                ·
                  refine ⟨11870321707294905960885197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7913547804863270640590131 11870321707294905960885197)
                  ·
                    refine ⟨4451370640235589735331949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11870321707294905960885197 4451370640235589735331949)
                    ·
                      refine ⟨1669263990088346150749481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451370640235589735331949 1669263990088346150749481)
                      ·
                        rfl

theorem cell23_3250880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_3250880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250880 prefixEnd_3250880 := by exact prefixLift 3250880
  have htrace : WordTrace (prefixWord ++ tailWord_3250880) baseStart_3250880 baseEnd_3250880 := by
    simpa [prefixWord, tailWord_3250880, baseEnd_3250880] using wordTrace_append hprefix tailTrace_3250880
  have hstable : (prefixWord ++ tailWord_3250880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250880).length < 2 ^ (prefixWord ++ tailWord_3250880).sum := by decide
  have hdescent : baseEnd_3250880 < baseStart_3250880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250881 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_3250881 : Nat := 118140960795 + 3250881 * 2 ^ 59
def prefixEnd_3250881 : Nat := 4983230072969 + 3 ^ 40 * 3250881 * 2
def baseEnd_3250881 : Nat := 1669264503569000646836977

theorem tailTrace_3250881 : CollatzResearch.WordTrace tailWord_3250881 prefixEnd_3250881 1669264503569000646836977 := by
  unfold tailWord_3250881
  simp only [CollatzResearch.WordTrace]
  refine ⟨118569370935620818117680497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79046247290413878745120331 118569370935620818117680497)
  ·
    refine ⟨88927028201715613588260373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118569370935620818117680497 88927028201715613588260373)
    ·
      refine ⟨4168454446955419386949705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88927028201715613588260373 4168454446955419386949705)
      ·
        refine ⟨3126340835216564540212279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4168454446955419386949705 3126340835216564540212279)
        ·
          refine ⟨4689511252824846810318419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3126340835216564540212279 4689511252824846810318419)
          ·
            refine ⟨7034266879237270215477629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689511252824846810318419 7034266879237270215477629)
            ·
              refine ⟨2637850079713976330804111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034266879237270215477629 2637850079713976330804111)
              ·
                refine ⟨3956775119570964496206167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637850079713976330804111 3956775119570964496206167)
                ·
                  refine ⟨5935162679356446744309251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956775119570964496206167 5935162679356446744309251)
                  ·
                    refine ⟨8902744019034670116463877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5935162679356446744309251 8902744019034670116463877)
                    ·
                      refine ⟨1669264503569000646836977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8902744019034670116463877 1669264503569000646836977)
                      ·
                        rfl

theorem cell23_3250881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_3250881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250881 prefixEnd_3250881 := by exact prefixLift 3250881
  have htrace : WordTrace (prefixWord ++ tailWord_3250881) baseStart_3250881 baseEnd_3250881 := by
    simpa [prefixWord, tailWord_3250881, baseEnd_3250881] using wordTrace_append hprefix tailTrace_3250881
  have hstable : (prefixWord ++ tailWord_3250881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250881).length < 2 ^ (prefixWord ++ tailWord_3250881).sum := by decide
  have hdescent : baseEnd_3250881 < baseStart_3250881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250884 : List Nat := [2, 3, 3, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_3250884 : Nat := 118140960795 + 3250884 * 2 ^ 59
def prefixEnd_3250884 : Nat := 4983230072969 + 3 ^ 40 * 3250884 * 2
def baseEnd_3250884 : Nat := 1669266044010964135099463

theorem tailTrace_3250884 : CollatzResearch.WordTrace tailWord_3250884 prefixEnd_3250884 1669266044010964135099463 := by
  unfold tailWord_3250884
  simp only [CollatzResearch.WordTrace]
  refine ⟨59284740177304974815019853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79046320236406633086693137 59284740177304974815019853)
  ·
    refine ⟨22231777566489365555632445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59284740177304974815019853 22231777566489365555632445)
    ·
      refine ⟨8336916587433512083362167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22231777566489365555632445 8336916587433512083362167)
      ·
        refine ⟨12505374881150268125043251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8336916587433512083362167 12505374881150268125043251)
        ·
          refine ⟨18758062321725402187564877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12505374881150268125043251 18758062321725402187564877)
          ·
            refine ⟨7034273370647025820336829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18758062321725402187564877 7034273370647025820336829)
            ·
              refine ⟨2637852513992634682626311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034273370647025820336829 2637852513992634682626311)
              ·
                refine ⟨3956778770988952023939467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2637852513992634682626311 3956778770988952023939467)
                ·
                  refine ⟨5935168156483428035909201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3956778770988952023939467 5935168156483428035909201)
                  ·
                    refine ⟨4451376117362571026931901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5935168156483428035909201 4451376117362571026931901)
                    ·
                      refine ⟨1669266044010964135099463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451376117362571026931901 1669266044010964135099463)
                      ·
                        rfl

theorem cell23_3250884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_3250884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250884 prefixEnd_3250884 := by exact prefixLift 3250884
  have htrace : WordTrace (prefixWord ++ tailWord_3250884) baseStart_3250884 baseEnd_3250884 := by
    simpa [prefixWord, tailWord_3250884, baseEnd_3250884] using wordTrace_append hprefix tailTrace_3250884
  have hstable : (prefixWord ++ tailWord_3250884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250884).length < 2 ^ (prefixWord ++ tailWord_3250884).sum := by decide
  have hdescent : baseEnd_3250884 < baseStart_3250884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250897 : List Nat := [1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_3250897 : Nat := 118140960795 + 3250897 * 2 ^ 59
def prefixEnd_3250897 : Nat := 4983230072969 + 3 ^ 40 * 3250897 * 2
def baseEnd_3250897 : Nat := 1669272719259472584236903

theorem tailTrace_3250897 : CollatzResearch.WordTrace tailWord_3250897 prefixEnd_3250897 1669272719259472584236903 := by
  unfold tailWord_3250897
  simp only [CollatzResearch.WordTrace]
  refine ⟨118569954503562852850262945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79046636335708568566841963 118569954503562852850262945)
  ·
    refine ⟨88927465877672139637697209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118569954503562852850262945 88927465877672139637697209)
    ·
      refine ⟨66695599408254104728272907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88927465877672139637697209 66695599408254104728272907)
      ·
        refine ⟨100043399112381157092409361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66695599408254104728272907 100043399112381157092409361)
        ·
          refine ⟨75032549334285867819307021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100043399112381157092409361 75032549334285867819307021)
          ·
            refine ⟨28137206000357200432240133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75032549334285867819307021 28137206000357200432240133)
            ·
              refine ⟨5275726125066975081045025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28137206000357200432240133 5275726125066975081045025)
              ·
                refine ⟨3956794593800231310783769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5275726125066975081045025 3956794593800231310783769)
                ·
                  refine ⟨2967595945350173483087827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3956794593800231310783769 2967595945350173483087827)
                  ·
                    refine ⟨4451393918025260224631741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2967595945350173483087827 4451393918025260224631741)
                    ·
                      refine ⟨1669272719259472584236903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451393918025260224631741 1669272719259472584236903)
                      ·
                        rfl

theorem cell23_3250897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_3250897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250897 prefixEnd_3250897 := by exact prefixLift 3250897
  have htrace : WordTrace (prefixWord ++ tailWord_3250897) baseStart_3250897 baseEnd_3250897 := by
    simpa [prefixWord, tailWord_3250897, baseEnd_3250897] using wordTrace_append hprefix tailTrace_3250897
  have hstable : (prefixWord ++ tailWord_3250897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250897).length < 2 ^ (prefixWord ++ tailWord_3250897).sum := by decide
  have hdescent : baseEnd_3250897 < baseStart_3250897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250903 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3250903 : Nat := 118140960795 + 3250903 * 2 ^ 59
def prefixEnd_3250903 : Nat := 4983230072969 + 3 ^ 40 * 3250903 * 2
def baseEnd_3250903 : Nat := 1669275800143399560761875

theorem tailTrace_3250903 : CollatzResearch.WordTrace tailWord_3250903 prefixEnd_3250903 1669275800143399560761875 := by
  unfold tailWord_3250903
  simp only [CollatzResearch.WordTrace]
  refine ⟨118570173341541115874981363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79046782227694077249987575 118570173341541115874981363)
  ·
    refine ⟨177855260012311673812472045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118570173341541115874981363 177855260012311673812472045)
    ·
      refine ⟨66695722504616877679677017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177855260012311673812472045 66695722504616877679677017)
      ·
        refine ⟨50021791878462658259757763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66695722504616877679677017 50021791878462658259757763)
        ·
          refine ⟨75032687817693987389636645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50021791878462658259757763 75032687817693987389636645)
          ·
            refine ⟨14068628965817622635556871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75032687817693987389636645 14068628965817622635556871)
            ·
              refine ⟨21102943448726433953335307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14068628965817622635556871 21102943448726433953335307)
              ·
                refine ⟨31654415173089650930002961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21102943448726433953335307 31654415173089650930002961)
                ·
                  refine ⟨23740811379817238197502221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31654415173089650930002961 23740811379817238197502221)
                  ·
                    refine ⟨8902804267431464324063333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23740811379817238197502221 8902804267431464324063333)
                    ·
                      refine ⟨1669275800143399560761875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8902804267431464324063333 1669275800143399560761875)
                      ·
                        rfl

theorem cell23_3250903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3250903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250903 prefixEnd_3250903 := by exact prefixLift 3250903
  have htrace : WordTrace (prefixWord ++ tailWord_3250903) baseStart_3250903 baseEnd_3250903 := by
    simpa [prefixWord, tailWord_3250903, baseEnd_3250903] using wordTrace_append hprefix tailTrace_3250903
  have hstable : (prefixWord ++ tailWord_3250903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250903).length < 2 ^ (prefixWord ++ tailWord_3250903).sum := by decide
  have hdescent : baseEnd_3250903 < baseStart_3250903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250913 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3250913 : Nat := 118140960795 + 3250913 * 2 ^ 59
def prefixEnd_3250913 : Nat := 4983230072969 + 3 ^ 40 * 3250913 * 2
def baseEnd_3250913 : Nat := 556426978316648173878943

theorem tailTrace_3250913 : CollatzResearch.WordTrace tailWord_3250913 prefixEnd_3250913 556426978316648173878943 := by
  unfold tailWord_3250913
  simp only [CollatzResearch.WordTrace]
  refine ⟨118570538071504887582845393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79047025381003258388563595 118570538071504887582845393)
  ·
    refine ⟨88927903553628665687134045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118570538071504887582845393 88927903553628665687134045)
    ·
      refine ⟨33347963832610749632675267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88927903553628665687134045 33347963832610749632675267)
      ·
        refine ⟨50021945748916124449012901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33347963832610749632675267 50021945748916124449012901)
        ·
          refine ⟨9379114827921773334189919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50021945748916124449012901 9379114827921773334189919)
          ·
            refine ⟨14068672241882660001284879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9379114827921773334189919 14068672241882660001284879)
            ·
              refine ⟨21103008362823990001927319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14068672241882660001284879 21103008362823990001927319)
              ·
                refine ⟨31654512544235985002890979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21103008362823990001927319 31654512544235985002890979)
                ·
                  refine ⟨47481768816353977504336469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31654512544235985002890979 47481768816353977504336469)
                  ·
                    refine ⟨556426978316648173878943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 47481768816353977504336469 556426978316648173878943)
                    ·
                      rfl

theorem cell23_3250913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3250913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250913 prefixEnd_3250913 := by exact prefixLift 3250913
  have htrace : WordTrace (prefixWord ++ tailWord_3250913) baseStart_3250913 baseEnd_3250913 := by
    simpa [prefixWord, tailWord_3250913, baseEnd_3250913] using wordTrace_append hprefix tailTrace_3250913
  have hstable : (prefixWord ++ tailWord_3250913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250913).length < 2 ^ (prefixWord ++ tailWord_3250913).sum := by decide
  have hdescent : baseEnd_3250913 < baseStart_3250913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250923 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3]
def baseStart_3250923 : Nat := 118140960795 + 3250923 * 2 ^ 59
def prefixEnd_3250923 : Nat := 4983230072969 + 3 ^ 40 * 3250923 * 2
def baseEnd_3250923 : Nat := 1669286069756489482511783

theorem tailTrace_3250923 : CollatzResearch.WordTrace tailWord_3250923 prefixEnd_3250923 1669286069756489482511783 := by
  unfold tailWord_3250923
  simp only [CollatzResearch.WordTrace]
  refine ⟨118570902801468659290709423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79047268534312439527139615 118570902801468659290709423)
  ·
    refine ⟨177856354202202988936064135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118570902801468659290709423 177856354202202988936064135)
    ·
      refine ⟨266784531303304483404096203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177856354202202988936064135 266784531303304483404096203)
      ·
        refine ⟨400176796954956725106144305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266784531303304483404096203 400176796954956725106144305)
        ·
          refine ⟨300132597716217543829608229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400176796954956725106144305 300132597716217543829608229)
          ·
            refine ⟨56274862071790789468051543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300132597716217543829608229 56274862071790789468051543)
            ·
              refine ⟨84412293107686184202077315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56274862071790789468051543 84412293107686184202077315)
              ·
                refine ⟨126618439661529276303115973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84412293107686184202077315 126618439661529276303115973)
                ·
                  refine ⟨23740957436536739306834245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126618439661529276303115973 23740957436536739306834245)
                  ·
                    refine ⟨4451429519350638620031421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23740957436536739306834245 4451429519350638620031421)
                    ·
                      refine ⟨1669286069756489482511783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451429519350638620031421 1669286069756489482511783)
                      ·
                        rfl

theorem cell23_3250923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3].length) (baseStart_3250923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250923 prefixEnd_3250923 := by exact prefixLift 3250923
  have htrace : WordTrace (prefixWord ++ tailWord_3250923) baseStart_3250923 baseEnd_3250923 := by
    simpa [prefixWord, tailWord_3250923, baseEnd_3250923] using wordTrace_append hprefix tailTrace_3250923
  have hstable : (prefixWord ++ tailWord_3250923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250923).length < 2 ^ (prefixWord ++ tailWord_3250923).sum := by decide
  have hdescent : baseEnd_3250923 < baseStart_3250923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3250970 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3]
def baseStart_3250970 : Nat := 118140960795 + 3250970 * 2 ^ 59
def prefixEnd_3250970 : Nat := 4983230072969 + 3 ^ 40 * 3250970 * 2
def baseEnd_3250970 : Nat := 1669310203347250798624067

theorem tailTrace_3250970 : CollatzResearch.WordTrace tailWord_3250970 prefixEnd_3250970 1669310203347250798624067 := by
  unfold tailWord_3250970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29643154258074596579417591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79048411354865590878446909 29643154258074596579417591)
  ·
    refine ⟨44464731387111894869126387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29643154258074596579417591 44464731387111894869126387)
    ·
      refine ⟨66697097080667842303689581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44464731387111894869126387 66697097080667842303689581)
      ·
        refine ⟨25011411405250440863883593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66697097080667842303689581 25011411405250440863883593)
        ·
          refine ⟨18758558553937830647912695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25011411405250440863883593 18758558553937830647912695)
          ·
            refine ⟨28137837830906745971869043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18758558553937830647912695 28137837830906745971869043)
            ·
              refine ⟨42206756746360118957803565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28137837830906745971869043 42206756746360118957803565)
              ·
                refine ⟨15827533779885044609176337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42206756746360118957803565 15827533779885044609176337)
                ·
                  refine ⟨11870650334913783456882253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15827533779885044609176337 11870650334913783456882253)
                  ·
                    refine ⟨4451493875592668796330845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11870650334913783456882253 4451493875592668796330845)
                    ·
                      refine ⟨1669310203347250798624067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451493875592668796330845 1669310203347250798624067)
                      ·
                        rfl

theorem cell23_3250970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_3250970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3250970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3250970 prefixEnd_3250970 := by exact prefixLift 3250970
  have htrace : WordTrace (prefixWord ++ tailWord_3250970) baseStart_3250970 baseEnd_3250970 := by
    simpa [prefixWord, tailWord_3250970, baseEnd_3250970] using wordTrace_append hprefix tailTrace_3250970
  have hstable : (prefixWord ++ tailWord_3250970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3250970).length < 2 ^ (prefixWord ++ tailWord_3250970).sum := by decide
  have hdescent : baseEnd_3250970 < baseStart_3250970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3250970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251013 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_3251013 : Nat := 118140960795 + 3251013 * 2 ^ 59
def prefixEnd_3251013 : Nat := 4983230072969 + 3 ^ 40 * 3251013 * 2
def baseEnd_3251013 : Nat := 1669332283015394130386369

theorem tailTrace_3251013 : CollatzResearch.WordTrace tailWord_3251013 prefixEnd_3251013 1669332283015394130386369 := by
  unfold tailWord_3251013
  simp only [CollatzResearch.WordTrace]
  refine ⟨118574185371142604661485693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79049456914095069774323795 118574185371142604661485693)
  ·
    refine ⟨44465319514178476748057135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118574185371142604661485693 44465319514178476748057135)
    ·
      refine ⟨66697979271267715122085703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44465319514178476748057135 66697979271267715122085703)
      ·
        refine ⟨100046968906901572683128555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66697979271267715122085703 100046968906901572683128555)
        ·
          refine ⟨150070453360352359024692833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100046968906901572683128555 150070453360352359024692833)
          ·
            refine ⟨112552840020264269268519625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150070453360352359024692833 112552840020264269268519625)
            ·
              refine ⟨84414630015198201951389719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112552840020264269268519625 84414630015198201951389719)
              ·
                refine ⟨126621945022797302927084579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84414630015198201951389719 126621945022797302927084579)
                ·
                  refine ⟨189932917534195954390626869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126621945022797302927084579 189932917534195954390626869)
                  ·
                    refine ⟨17806211018830870724121269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 189932917534195954390626869 17806211018830870724121269)
                    ·
                      refine ⟨1669332283015394130386369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17806211018830870724121269 1669332283015394130386369)
                      ·
                        rfl

theorem cell23_3251013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_3251013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251013 prefixEnd_3251013 := by exact prefixLift 3251013
  have htrace : WordTrace (prefixWord ++ tailWord_3251013) baseStart_3251013 baseEnd_3251013 := by
    simpa [prefixWord, tailWord_3251013, baseEnd_3251013] using wordTrace_append hprefix tailTrace_3251013
  have hstable : (prefixWord ++ tailWord_3251013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251013).length < 2 ^ (prefixWord ++ tailWord_3251013).sum := by decide
  have hdescent : baseEnd_3251013 < baseStart_3251013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251047 : List Nat := [1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3251047 : Nat := 118140960795 + 3251047 * 2 ^ 59
def prefixEnd_3251047 : Nat := 4983230072969 + 3 ^ 40 * 3251047 * 2
def baseEnd_3251047 : Nat := 1669349741357646997361213

theorem tailTrace_3251047 : CollatzResearch.WordTrace tailWord_3251047 prefixEnd_3251047 1669349741357646997361213 := by
  unfold tailWord_3251047
  simp only [CollatzResearch.WordTrace]
  refine ⟨118575425453019428468223395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79050283635346285645482263 118575425453019428468223395)
  ·
    refine ⟨177863138179529142702335093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118575425453019428468223395 177863138179529142702335093)
    ·
      refine ⟨16674669204330857128343915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177863138179529142702335093 16674669204330857128343915)
      ·
        refine ⟨25012003806496285692515873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16674669204330857128343915 25012003806496285692515873)
        ·
          refine ⟨18759002854872214269386905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25012003806496285692515873 18759002854872214269386905)
          ·
            refine ⟨14069252141154160702040179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18759002854872214269386905 14069252141154160702040179)
            ·
              refine ⟨21103878211731241053060269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14069252141154160702040179 21103878211731241053060269)
              ·
                refine ⟨7913954329399215394897601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21103878211731241053060269 7913954329399215394897601)
                ·
                  refine ⟨5935465747049411546173201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7913954329399215394897601 5935465747049411546173201)
                  ·
                    refine ⟨4451599310287058659629901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5935465747049411546173201 4451599310287058659629901)
                    ·
                      refine ⟨1669349741357646997361213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451599310287058659629901 1669349741357646997361213)
                      ·
                        rfl

theorem cell23_3251047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3251047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251047 prefixEnd_3251047 := by exact prefixLift 3251047
  have htrace : WordTrace (prefixWord ++ tailWord_3251047) baseStart_3251047 baseEnd_3251047 := by
    simpa [prefixWord, tailWord_3251047, baseEnd_3251047] using wordTrace_append hprefix tailTrace_3251047
  have hstable : (prefixWord ++ tailWord_3251047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251047).length < 2 ^ (prefixWord ++ tailWord_3251047).sum := by decide
  have hdescent : baseEnd_3251047 < baseStart_3251047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251104 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2]
def baseStart_3251104 : Nat := 118140960795 + 3251104 * 2 ^ 59
def prefixEnd_3251104 : Nat := 4983230072969 + 3 ^ 40 * 3251104 * 2
def baseEnd_3251104 : Nat := 1669379009754953274348451

theorem tailTrace_3251104 : CollatzResearch.WordTrace tailWord_3251104 prefixEnd_3251104 1669379009754953274348451 := by
  unfold tailWord_3251104
  simp only [CollatzResearch.WordTrace]
  refine ⟨59288752206906463601524183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79051669609208618135365577 59288752206906463601524183)
  ·
    refine ⟨88933128310359695402286275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59288752206906463601524183 88933128310359695402286275)
    ·
      refine ⟨133399692465539543103429413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88933128310359695402286275 133399692465539543103429413)
      ·
        refine ⟨25012442337288664331893015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133399692465539543103429413 25012442337288664331893015)
        ·
          refine ⟨37518663505932996497839523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25012442337288664331893015 37518663505932996497839523)
          ·
            refine ⟨56277995258899494746759285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37518663505932996497839523 56277995258899494746759285)
            ·
              refine ⟨5276062055521827632508683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56277995258899494746759285 5276062055521827632508683)
              ·
                refine ⟨7914093083282741448763025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276062055521827632508683 7914093083282741448763025)
                ·
                  refine ⟨5935569812462056086572269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7914093083282741448763025 5935569812462056086572269)
                  ·
                    refine ⟨2225838679673271032464601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5935569812462056086572269 2225838679673271032464601)
                    ·
                      refine ⟨1669379009754953274348451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225838679673271032464601 1669379009754953274348451)
                      ·
                        rfl

theorem cell23_3251104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_3251104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251104 prefixEnd_3251104 := by exact prefixLift 3251104
  have htrace : WordTrace (prefixWord ++ tailWord_3251104) baseStart_3251104 baseEnd_3251104 := by
    simpa [prefixWord, tailWord_3251104, baseEnd_3251104] using wordTrace_append hprefix tailTrace_3251104
  have hstable : (prefixWord ++ tailWord_3251104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251104).length < 2 ^ (prefixWord ++ tailWord_3251104).sum := by decide
  have hdescent : baseEnd_3251104 < baseStart_3251104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251130 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3251130 : Nat := 118140960795 + 3251130 * 2 ^ 59
def prefixEnd_3251130 : Nat := 4983230072969 + 3 ^ 40 * 3251130 * 2
def baseEnd_3251130 : Nat := 1669392360251970172623331

theorem tailTrace_3251130 : CollatzResearch.WordTrace tailWord_3251130 prefixEnd_3251130 1669392360251970172623331 := by
  unfold tailWord_3251130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29644613177929683410873711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79052301807812489095663229 29644613177929683410873711)
  ·
    refine ⟨44466919766894525116310567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29644613177929683410873711 44466919766894525116310567)
    ·
      refine ⟨66700379650341787674465851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44466919766894525116310567 66700379650341787674465851)
      ·
        refine ⟨100050569475512681511698777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66700379650341787674465851 100050569475512681511698777)
        ·
          refine ⟨75037927106634511133774083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100050569475512681511698777 75037927106634511133774083)
          ·
            refine ⟨112556890659951766700661125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75037927106634511133774083 112556890659951766700661125)
            ·
              refine ⟨21104416998740956256373961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112556890659951766700661125 21104416998740956256373961)
              ·
                refine ⟨15828312749055717192280471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21104416998740956256373961 15828312749055717192280471)
                ·
                  refine ⟨23742469123583575788420707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15828312749055717192280471 23742469123583575788420707)
                  ·
                    refine ⟨35613703685375363682631061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23742469123583575788420707 35613703685375363682631061)
                    ·
                      refine ⟨1669392360251970172623331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35613703685375363682631061 1669392360251970172623331)
                      ·
                        rfl

theorem cell23_3251130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3251130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251130 prefixEnd_3251130 := by exact prefixLift 3251130
  have htrace : WordTrace (prefixWord ++ tailWord_3251130) baseStart_3251130 baseEnd_3251130 := by
    simpa [prefixWord, tailWord_3251130, baseEnd_3251130] using wordTrace_append hprefix tailTrace_3251130
  have hstable : (prefixWord ++ tailWord_3251130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251130).length < 2 ^ (prefixWord ++ tailWord_3251130).sum := by decide
  have hdescent : baseEnd_3251130 < baseStart_3251130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251144 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_3251144 : Nat := 118140960795 + 3251144 * 2 ^ 59
def prefixEnd_3251144 : Nat := 4983230072969 + 3 ^ 40 * 3251144 * 2
def baseEnd_3251144 : Nat := 556466516327044372616089

theorem tailTrace_3251144 : CollatzResearch.WordTrace tailWord_3251144 prefixEnd_3251144 556466516327044372616089 := by
  unfold tailWord_3251144
  simp only [CollatzResearch.WordTrace]
  refine ⟨59289481666834007017252243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79052642222445342689669657 59289481666834007017252243)
  ·
    refine ⟨88934222500251010525878365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59289481666834007017252243 88934222500251010525878365)
    ·
      refine ⟨33350333437594128947204387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88934222500251010525878365 33350333437594128947204387)
      ·
        refine ⟨50025500156391193420806581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33350333437594128947204387 50025500156391193420806581)
        ·
          refine ⟨4689890639661674383200617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50025500156391193420806581 4689890639661674383200617)
          ·
            refine ⟨3517417979746255787400463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4689890639661674383200617 3517417979746255787400463)
            ·
              refine ⟨5276126969619383681100695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517417979746255787400463 5276126969619383681100695)
              ·
                refine ⟨7914190454429075521651043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276126969619383681100695 7914190454429075521651043)
                ·
                  refine ⟨11871285681643613282476565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7914190454429075521651043 11871285681643613282476565)
                  ·
                    refine ⟨556466516327044372616089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11871285681643613282476565 556466516327044372616089)
                    ·
                      rfl

theorem cell23_3251144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_3251144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251144 prefixEnd_3251144 := by exact prefixLift 3251144
  have htrace : WordTrace (prefixWord ++ tailWord_3251144) baseStart_3251144 baseEnd_3251144 := by
    simpa [prefixWord, tailWord_3251144, baseEnd_3251144] using wordTrace_append hprefix tailTrace_3251144
  have hstable : (prefixWord ++ tailWord_3251144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251144).length < 2 ^ (prefixWord ++ tailWord_3251144).sum := by decide
  have hdescent : baseEnd_3251144 < baseStart_3251144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251147 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4]
def baseStart_3251147 : Nat := 118140960795 + 3251147 * 2 ^ 59
def prefixEnd_3251147 : Nat := 4983230072969 + 3 ^ 40 * 3251147 * 2
def baseEnd_3251147 : Nat := 1669401089423096606110753

theorem tailTrace_3251147 : CollatzResearch.WordTrace tailWord_3251147 prefixEnd_3251147 1669401089423096606110753 := by
  unfold tailWord_3251147
  simp only [CollatzResearch.WordTrace]
  refine ⟨118579072752657145546863695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79052715168438097031242463 118579072752657145546863695)
  ·
    refine ⟨177868609128985718320295543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118579072752657145546863695 177868609128985718320295543)
    ·
      refine ⟨266802913693478577480443315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177868609128985718320295543 266802913693478577480443315)
      ·
        refine ⟨400204370540217866220664973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266802913693478577480443315 400204370540217866220664973)
        ·
          refine ⟨150076638952581699832749365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400204370540217866220664973 150076638952581699832749365)
          ·
            refine ⟨14069684901804534359320253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150076638952581699832749365 14069684901804534359320253)
            ·
              refine ⟨5276131838176700384745095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14069684901804534359320253 5276131838176700384745095)
              ·
                refine ⟨7914197757265050577117643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5276131838176700384745095 7914197757265050577117643)
                ·
                  refine ⟨11871296635897575865676465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7914197757265050577117643 11871296635897575865676465)
                  ·
                    refine ⟨8903472476923181899257349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11871296635897575865676465 8903472476923181899257349)
                    ·
                      refine ⟨1669401089423096606110753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8903472476923181899257349 1669401089423096606110753)
                      ·
                        rfl

theorem cell23_3251147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4].length) (baseStart_3251147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251147 prefixEnd_3251147 := by exact prefixLift 3251147
  have htrace : WordTrace (prefixWord ++ tailWord_3251147) baseStart_3251147 baseEnd_3251147 := by
    simpa [prefixWord, tailWord_3251147, baseEnd_3251147] using wordTrace_append hprefix tailTrace_3251147
  have hstable : (prefixWord ++ tailWord_3251147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251147).length < 2 ^ (prefixWord ++ tailWord_3251147).sum := by decide
  have hdescent : baseEnd_3251147 < baseStart_3251147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251157 : List Nat := [1, 3, 2, 3, 3, 1, 1, 9]
def baseStart_3251157 : Nat := 118140960795 + 3251157 * 2 ^ 59
def prefixEnd_3251157 : Nat := 4983230072969 + 3 ^ 40 * 3251157 * 2
def baseEnd_3251157 : Nat := 61829860156653391369841

theorem tailTrace_3251157 : CollatzResearch.WordTrace tailWord_3251157 prefixEnd_3251157 61829860156653391369841 := by
  unfold tailWord_3251157
  simp only [CollatzResearch.WordTrace]
  refine ⟨118579437482620917254727725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79052958321747278169818483 118579437482620917254727725)
  ·
    refine ⟨44467289055982843970522897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118579437482620917254727725 44467289055982843970522897)
    ·
      refine ⟨33350466791987132977892173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44467289055982843970522897 33350466791987132977892173)
      ·
        refine ⟨12506425046995174866709565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33350466791987132977892173 12506425046995174866709565)
        ·
          refine ⟨4689909392623190575016087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12506425046995174866709565 4689909392623190575016087)
          ·
            refine ⟨7034864088934785862524131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4689909392623190575016087 7034864088934785862524131)
            ·
              refine ⟨10552296133402178793786197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034864088934785862524131 10552296133402178793786197)
              ·
                refine ⟨61829860156653391369841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10552296133402178793786197 61829860156653391369841)
                ·
                  rfl

theorem cell23_3251157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 9].length) (baseStart_3251157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251157 prefixEnd_3251157 := by exact prefixLift 3251157
  have htrace : WordTrace (prefixWord ++ tailWord_3251157) baseStart_3251157 baseEnd_3251157 := by
    simpa [prefixWord, tailWord_3251157, baseEnd_3251157] using wordTrace_append hprefix tailTrace_3251157
  have hstable : (prefixWord ++ tailWord_3251157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251157).length < 2 ^ (prefixWord ++ tailWord_3251157).sum := by decide
  have hdescent : baseEnd_3251157 < baseStart_3251157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251184 : List Nat := [2, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3]
def baseStart_3251184 : Nat := 118140960795 + 3251184 * 2 ^ 59
def prefixEnd_3251184 : Nat := 4983230072969 + 3 ^ 40 * 3251184 * 2
def baseEnd_3251184 : Nat := 1669420088207312961348083

theorem tailTrace_3251184 : CollatzResearch.WordTrace tailWord_3251184 prefixEnd_3251184 1669420088207312961348083 := by
  unfold tailWord_3251184
  simp only [CollatzResearch.WordTrace]
  refine ⟨59290211126761550432980303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79053614835682067243973737 59290211126761550432980303)
  ·
    refine ⟨88935316690142325649470455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59290211126761550432980303 88935316690142325649470455)
    ·
      refine ⟨133402975035213488474205683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88935316690142325649470455 133402975035213488474205683)
      ·
        refine ⟨200104462552820232711308525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133402975035213488474205683 200104462552820232711308525)
        ·
          refine ⟨75039173457307587266740697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200104462552820232711308525 75039173457307587266740697)
          ·
            refine ⟨56279380092980690450055523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75039173457307587266740697 56279380092980690450055523)
            ·
              refine ⟨84419070139471035675083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56279380092980690450055523 84419070139471035675083285)
              ·
                refine ⟨3957143912787704797269529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84419070139471035675083285 3957143912787704797269529)
                ·
                  refine ⟨2967857934590778597952147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957143912787704797269529 2967857934590778597952147)
                  ·
                    refine ⟨4451786901886167896928221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2967857934590778597952147 4451786901886167896928221)
                    ·
                      refine ⟨1669420088207312961348083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451786901886167896928221 1669420088207312961348083)
                      ·
                        rfl

theorem cell23_3251184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 6, 2, 1, 3].length) (baseStart_3251184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251184 prefixEnd_3251184 := by exact prefixLift 3251184
  have htrace : WordTrace (prefixWord ++ tailWord_3251184) baseStart_3251184 baseEnd_3251184 := by
    simpa [prefixWord, tailWord_3251184, baseEnd_3251184] using wordTrace_append hprefix tailTrace_3251184
  have hstable : (prefixWord ++ tailWord_3251184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251184).length < 2 ^ (prefixWord ++ tailWord_3251184).sum := by decide
  have hdescent : baseEnd_3251184 < baseStart_3251184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251185 : List Nat := [1, 2, 2, 2, 4, 2, 3, 2, 1, 2, 2]
def baseStart_3251185 : Nat := 118140960795 + 3251185 * 2 ^ 59
def prefixEnd_3251185 : Nat := 4983230072969 + 3 ^ 40 * 3251185 * 2
def baseEnd_3251185 : Nat := 1669420601687967457435579

theorem tailTrace_3251185 : CollatzResearch.WordTrace tailWord_3251185 prefixEnd_3251185 1669420601687967457435579 := by
  unfold tailWord_3251185
  simp only [CollatzResearch.WordTrace]
  refine ⟨118580458726519478036747009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79053639151012985357831339 118580458726519478036747009)
  ·
    refine ⟨88935344044889608527560257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118580458726519478036747009 88935344044889608527560257)
    ·
      refine ⟨66701508033667206395670193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88935344044889608527560257 66701508033667206395670193)
      ·
        refine ⟨50026131025250404796752645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66701508033667206395670193 50026131025250404796752645)
        ·
          refine ⟨9379899567234450899391121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50026131025250404796752645 9379899567234450899391121)
          ·
            refine ⟨7034924675425838174543341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9379899567234450899391121 7034924675425838174543341)
            ·
              refine ⟨2638096753284689315453753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7034924675425838174543341 2638096753284689315453753)
              ·
                refine ⟨1978572564963516986590315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2638096753284689315453753 1978572564963516986590315)
                ·
                  refine ⟨2967858847445275479885473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978572564963516986590315 2967858847445275479885473)
                  ·
                    refine ⟨2225894135583956609914105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2967858847445275479885473 2225894135583956609914105)
                    ·
                      refine ⟨1669420601687967457435579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2225894135583956609914105 1669420601687967457435579)
                      ·
                        rfl

theorem cell23_3251185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_3251185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251185 prefixEnd_3251185 := by exact prefixLift 3251185
  have htrace : WordTrace (prefixWord ++ tailWord_3251185) baseStart_3251185 baseEnd_3251185 := by
    simpa [prefixWord, tailWord_3251185, baseEnd_3251185] using wordTrace_append hprefix tailTrace_3251185
  have hstable : (prefixWord ++ tailWord_3251185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251185).length < 2 ^ (prefixWord ++ tailWord_3251185).sum := by decide
  have hdescent : baseEnd_3251185 < baseStart_3251185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251200 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_3251200 : Nat := 118140960795 + 3251200 * 2 ^ 59
def prefixEnd_3251200 : Nat := 4983230072969 + 3 ^ 40 * 3251200 * 2
def baseEnd_3251200 : Nat := 556476101299261632916003

theorem tailTrace_3251200 : CollatzResearch.WordTrace tailWord_3251200 prefixEnd_3251200 556476101299261632916003 := by
  unfold tailWord_3251200
  simp only [CollatzResearch.WordTrace]
  refine ⟨59290502910732567799271527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79054003880976757065695369 59290502910732567799271527)
  ·
    refine ⟨88935754366098851698907291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59290502910732567799271527 88935754366098851698907291)
    ·
      refine ⟨133403631549148277548360937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88935754366098851698907291 133403631549148277548360937)
      ·
        refine ⟨100052723661861208161270703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133403631549148277548360937 100052723661861208161270703)
        ·
          refine ⟨150079085492791812241906055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100052723661861208161270703 150079085492791812241906055)
          ·
            refine ⟨225118628239187718362859083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150079085492791812241906055 225118628239187718362859083)
            ·
              refine ⟨337677942358781577544288625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225118628239187718362859083 337677942358781577544288625)
              ·
                refine ⟨253258456769086183158216469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337677942358781577544288625 253258456769086183158216469)
                ·
                  refine ⟨11871490161050914835541397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 253258456769086183158216469 11871490161050914835541397)
                  ·
                    refine ⟨556476101299261632916003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11871490161050914835541397 556476101299261632916003)
                    ·
                      rfl

theorem cell23_3251200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_3251200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251200 prefixEnd_3251200 := by exact prefixLift 3251200
  have htrace : WordTrace (prefixWord ++ tailWord_3251200) baseStart_3251200 baseEnd_3251200 := by
    simpa [prefixWord, tailWord_3251200, baseEnd_3251200] using wordTrace_append hprefix tailTrace_3251200
  have hstable : (prefixWord ++ tailWord_3251200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251200).length < 2 ^ (prefixWord ++ tailWord_3251200).sum := by decide
  have hdescent : baseEnd_3251200 < baseStart_3251200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3251201 : List Nat := [1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3251201 : Nat := 118140960795 + 3251201 * 2 ^ 59
def prefixEnd_3251201 : Nat := 4983230072969 + 3 ^ 40 * 3251201 * 2
def baseEnd_3251201 : Nat := 1669428817378439394835505

theorem tailTrace_3251201 : CollatzResearch.WordTrace tailWord_3251201 prefixEnd_3251201 1669428817378439394835505 := by
  unfold tailWord_3251201
  simp only [CollatzResearch.WordTrace]
  refine ⟨118581042294461512769329457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79054028196307675179552971 118581042294461512769329457)
  ·
    refine ⟨88935781720846134576997093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118581042294461512769329457 88935781720846134576997093)
    ·
      refine ⟨16675459072658650233186955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88935781720846134576997093 16675459072658650233186955)
      ·
        refine ⟨25013188608987975349780433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16675459072658650233186955 25013188608987975349780433)
        ·
          refine ⟨18759891456740981512335325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25013188608987975349780433 18759891456740981512335325)
          ·
            refine ⟨7034959296277868067125747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18759891456740981512335325 7034959296277868067125747)
            ·
              refine ⟨10552438944416802100688621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7034959296277868067125747 10552438944416802100688621)
              ·
                refine ⟨3957164604156300787758233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10552438944416802100688621 3957164604156300787758233)
                ·
                  refine ⟨2967873453117225590818675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957164604156300787758233 2967873453117225590818675)
                  ·
                    refine ⟨4451810179675838386228013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2967873453117225590818675 4451810179675838386228013)
                    ·
                      refine ⟨1669428817378439394835505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4451810179675838386228013 1669428817378439394835505)
                      ·
                        rfl

theorem cell23_3251201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3251201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3251201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3251201 prefixEnd_3251201 := by exact prefixLift 3251201
  have htrace : WordTrace (prefixWord ++ tailWord_3251201) baseStart_3251201 baseEnd_3251201 := by
    simpa [prefixWord, tailWord_3251201, baseEnd_3251201] using wordTrace_append hprefix tailTrace_3251201
  have hstable : (prefixWord ++ tailWord_3251201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3251201).length < 2 ^ (prefixWord ++ tailWord_3251201).sum := by decide
  have hdescent : baseEnd_3251201 < baseStart_3251201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3251201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
