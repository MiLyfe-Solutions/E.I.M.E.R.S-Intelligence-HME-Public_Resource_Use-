import V185TrunkScan23Chunk0247

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1467505 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1467505 : Nat := 118140960795 + 1467505 * 2 ^ 59
def prefixEnd_1467505 : Nat := 4983230072969 + 3 ^ 40 * 1467505 * 2
def baseEnd_1467505 : Nat := 753535427876386113638573

theorem tailTrace_1467505 : CollatzResearch.WordTrace tailWord_1467505 prefixEnd_1467505 753535427876386113638573 := by
  unfold tailWord_1467505
  simp only [CollatzResearch.WordTrace]
  refine ⟨53524304548487489745443969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35682869698991659830295979 53524304548487489745443969)
  ·
    refine ⟨40143228411365617309082977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53524304548487489745443969 40143228411365617309082977)
    ·
      refine ⟨30107421308524212981812233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40143228411365617309082977 30107421308524212981812233)
      ·
        refine ⟨22580565981393159736359175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30107421308524212981812233 22580565981393159736359175)
        ·
          refine ⟨33870848972089739604538763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22580565981393159736359175 33870848972089739604538763)
          ·
            refine ⟨50806273458134609406808145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33870848972089739604538763 50806273458134609406808145)
            ·
              refine ⟨38104705093600957055106109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50806273458134609406808145 38104705093600957055106109)
              ·
                refine ⟨14289264410100358895664791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38104705093600957055106109 14289264410100358895664791)
                ·
                  refine ⟨21433896615150538343497187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14289264410100358895664791 21433896615150538343497187)
                  ·
                    refine ⟨32150844922725807515245781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21433896615150538343497187 32150844922725807515245781)
                    ·
                      refine ⟨753535427876386113638573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32150844922725807515245781 753535427876386113638573)
                      ·
                        rfl

theorem cell23_1467505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1467505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467505 prefixEnd_1467505 := by exact prefixLift 1467505
  have htrace : WordTrace (prefixWord ++ tailWord_1467505) baseStart_1467505 baseEnd_1467505 := by
    simpa [prefixWord, tailWord_1467505, baseEnd_1467505] using wordTrace_append hprefix tailTrace_1467505
  have hstable : (prefixWord ++ tailWord_1467505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467505).length < 2 ^ (prefixWord ++ tailWord_1467505).sum := by decide
  have hdescent : baseEnd_1467505 < baseStart_1467505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467529 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 2, 5]
def baseStart_1467529 : Nat := 118140960795 + 1467529 * 2 ^ 59
def prefixEnd_1467529 : Nat := 4983230072969 + 3 ^ 40 * 1467529 * 2
def baseEnd_1467529 : Nat := 251182583804031339912821

theorem tailTrace_1467529 : CollatzResearch.WordTrace tailWord_1467529 prefixEnd_1467529 251182583804031339912821 := by
  unfold tailWord_1467529
  simp only [CollatzResearch.WordTrace]
  refine ⟨53525179900400541844317641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35683453266933694562878427 53525179900400541844317641)
  ·
    refine ⟨40143884925300406383238231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53525179900400541844317641 40143884925300406383238231)
    ·
      refine ⟨60215827387950609574857347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40143884925300406383238231 60215827387950609574857347)
      ·
        refine ⟨90323741081925914362286021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60215827387950609574857347 90323741081925914362286021)
        ·
          refine ⟨16935701452861108942928629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90323741081925914362286021 16935701452861108942928629)
          ·
            refine ⟨1587722011205728963399559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16935701452861108942928629 1587722011205728963399559)
            ·
              refine ⟨2381583016808593445099339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587722011205728963399559 2381583016808593445099339)
              ·
                refine ⟨3572374525212890167649009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381583016808593445099339 3572374525212890167649009)
                ·
                  refine ⟨2679280893909667625736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572374525212890167649009 2679280893909667625736757)
                  ·
                    refine ⟨251182583804031339912821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2679280893909667625736757 251182583804031339912821)
                    ·
                      rfl

theorem cell23_1467529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 5].length) (baseStart_1467529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467529 prefixEnd_1467529 := by exact prefixLift 1467529
  have htrace : WordTrace (prefixWord ++ tailWord_1467529) baseStart_1467529 baseEnd_1467529 := by
    simpa [prefixWord, tailWord_1467529, baseEnd_1467529] using wordTrace_append hprefix tailTrace_1467529
  have hstable : (prefixWord ++ tailWord_1467529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467529).length < 2 ^ (prefixWord ++ tailWord_1467529).sum := by decide
  have hdescent : baseEnd_1467529 < baseStart_1467529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467535 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5]
def baseStart_1467535 : Nat := 118140960795 + 1467535 * 2 ^ 59
def prefixEnd_1467535 : Nat := 4983230072969 + 3 ^ 40 * 1467535 * 2
def baseEnd_1467535 : Nat := 753550832296020996263435

theorem tailTrace_1467535 : CollatzResearch.WordTrace tailWord_1467535 prefixEnd_1467535 753550832296020996263435 := by
  unfold tailWord_1467535
  simp only [CollatzResearch.WordTrace]
  refine ⟨53525398738378804869036059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35683599158919203246024039 53525398738378804869036059)
  ·
    refine ⟨80288098107568207303554089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53525398738378804869036059 80288098107568207303554089)
    ·
      refine ⟨60216073580676155477665567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80288098107568207303554089 60216073580676155477665567)
      ·
        refine ⟨90324110371014233216498351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60216073580676155477665567 90324110371014233216498351)
        ·
          refine ⟨135486165556521349824747527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90324110371014233216498351 135486165556521349824747527)
          ·
            refine ⟨203229248334782024737121291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135486165556521349824747527 203229248334782024737121291)
            ·
              refine ⟨304843872502173037105681937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203229248334782024737121291 304843872502173037105681937)
              ·
                refine ⟨228632904376629777829261453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304843872502173037105681937 228632904376629777829261453)
                ·
                  refine ⟨85737339141236166685973045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228632904376629777829261453 85737339141236166685973045)
                  ·
                    refine ⟨8037875544490890626809973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85737339141236166685973045 8037875544490890626809973)
                    ·
                      refine ⟨753550832296020996263435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8037875544490890626809973 753550832296020996263435)
                      ·
                        rfl

theorem cell23_1467535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_1467535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467535 prefixEnd_1467535 := by exact prefixLift 1467535
  have htrace : WordTrace (prefixWord ++ tailWord_1467535) baseStart_1467535 baseEnd_1467535 := by
    simpa [prefixWord, tailWord_1467535, baseEnd_1467535] using wordTrace_append hprefix tailTrace_1467535
  have hstable : (prefixWord ++ tailWord_1467535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467535).length < 2 ^ (prefixWord ++ tailWord_1467535).sum := by decide
  have hdescent : baseEnd_1467535 < baseStart_1467535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467549 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 4, 4, 2]
def baseStart_1467549 : Nat := 118140960795 + 1467549 * 2 ^ 59
def prefixEnd_1467549 : Nat := 4983230072969 + 3 ^ 40 * 1467549 * 2
def baseEnd_1467549 : Nat := 753558021025183941488371

theorem tailTrace_1467549 : CollatzResearch.WordTrace tailWord_1467549 prefixEnd_1467549 753558021025183941488371 := by
  unfold tailWord_1467549
  simp only [CollatzResearch.WordTrace]
  refine ⟨53525909360328085260045701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35683939573552056840030467 53525909360328085260045701)
  ·
    refine ⟨10036108005061515986258569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53525909360328085260045701 10036108005061515986258569)
    ·
      refine ⟨7527081003796136989693927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10036108005061515986258569 7527081003796136989693927)
      ·
        refine ⟨11290621505694205484540891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527081003796136989693927 11290621505694205484540891)
        ·
          refine ⟨16935932258541308226811337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290621505694205484540891 16935932258541308226811337)
          ·
            refine ⟨12701949193905981170108503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16935932258541308226811337 12701949193905981170108503)
            ·
              refine ⟨19052923790858971755162755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12701949193905981170108503 19052923790858971755162755)
              ·
                refine ⟨28579385686288457632744133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19052923790858971755162755 28579385686288457632744133)
                ·
                  refine ⟨5358634816179085806139525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28579385686288457632744133 5358634816179085806139525)
                  ·
                    refine ⟨1004744028033578588651161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5358634816179085806139525 1004744028033578588651161)
                    ·
                      refine ⟨753558021025183941488371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004744028033578588651161 753558021025183941488371)
                      ·
                        rfl

theorem cell23_1467549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_1467549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467549 prefixEnd_1467549 := by exact prefixLift 1467549
  have htrace : WordTrace (prefixWord ++ tailWord_1467549) baseStart_1467549 baseEnd_1467549 := by
    simpa [prefixWord, tailWord_1467549, baseEnd_1467549] using wordTrace_append hprefix tailTrace_1467549
  have hstable : (prefixWord ++ tailWord_1467549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467549).length < 2 ^ (prefixWord ++ tailWord_1467549).sum := by decide
  have hdescent : baseEnd_1467549 < baseStart_1467549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467569 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1467569 : Nat := 118140960795 + 1467569 * 2 ^ 59
def prefixEnd_1467569 : Nat := 4983230072969 + 3 ^ 40 * 1467569 * 2
def baseEnd_1467569 : Nat := 753568290638273863238279

theorem tailTrace_1467569 : CollatzResearch.WordTrace tailWord_1467569 prefixEnd_1467569 753568290638273863238279 := by
  unfold tailWord_1467569
  simp only [CollatzResearch.WordTrace]
  refine ⟨53526638820255628675773761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35684425880170419117182507 53526638820255628675773761)
  ·
    refine ⟨40144979115191721506830321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53526638820255628675773761 40144979115191721506830321)
    ·
      refine ⟨30108734336393791130122741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40144979115191721506830321 30108734336393791130122741)
      ·
        refine ⟨2822693844036917918449007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30108734336393791130122741 2822693844036917918449007)
        ·
          refine ⟨4234040766055376877673511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822693844036917918449007 4234040766055376877673511)
          ·
            refine ⟨6351061149083065316510267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234040766055376877673511 6351061149083065316510267)
            ·
              refine ⟨9526591723624597974765401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351061149083065316510267 9526591723624597974765401)
              ·
                refine ⟨7144943792718448481074051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9526591723624597974765401 7144943792718448481074051)
                ·
                  refine ⟨10717415689077672721611077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144943792718448481074051 10717415689077672721611077)
                  ·
                    refine ⟨2009515441702063635302077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10717415689077672721611077 2009515441702063635302077)
                    ·
                      refine ⟨753568290638273863238279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009515441702063635302077 753568290638273863238279)
                      ·
                        rfl

theorem cell23_1467569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1467569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467569 prefixEnd_1467569 := by exact prefixLift 1467569
  have htrace : WordTrace (prefixWord ++ tailWord_1467569) baseStart_1467569 baseEnd_1467569 := by
    simpa [prefixWord, tailWord_1467569, baseEnd_1467569] using wordTrace_append hprefix tailTrace_1467569
  have hstable : (prefixWord ++ tailWord_1467569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467569).length < 2 ^ (prefixWord ++ tailWord_1467569).sum := by decide
  have hdescent : baseEnd_1467569 < baseStart_1467569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467616 : List Nat := [2, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3]
def baseStart_1467616 : Nat := 118140960795 + 1467616 * 2 ^ 59
def prefixEnd_1467616 : Nat := 4983230072969 + 3 ^ 40 * 1467616 * 2
def baseEnd_1467616 : Nat := 753592424229035179350563

theorem tailTrace_1467616 : CollatzResearch.WordTrace tailWord_1467616 prefixEnd_1467616 753592424229035179350563 := by
  unfold tailWord_1467616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764176525542677851367351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35685568700723570468489801 26764176525542677851367351)
  ·
    refine ⟨40146264788314016777051027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26764176525542677851367351 40146264788314016777051027)
    ·
      refine ⟨60219397182471025165576541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40146264788314016777051027 60219397182471025165576541)
      ·
        refine ⟨22582273943426634437091203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60219397182471025165576541 22582273943426634437091203)
        ·
          refine ⟨33873410915139951655636805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22582273943426634437091203 33873410915139951655636805)
          ·
            refine ⟨6351264546588740935431901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33873410915139951655636805 6351264546588740935431901)
            ·
              refine ⟨2381724204970777850786963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6351264546588740935431901 2381724204970777850786963)
              ·
                refine ⟨3572586307456166776180445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381724204970777850786963 3572586307456166776180445)
                ·
                  refine ⟨1339719865296062541067667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3572586307456166776180445 1339719865296062541067667)
                  ·
                    refine ⟨2009579797944093811601501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1339719865296062541067667 2009579797944093811601501)
                    ·
                      refine ⟨753592424229035179350563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009579797944093811601501 753592424229035179350563)
                      ·
                        rfl

theorem cell23_1467616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_1467616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467616 prefixEnd_1467616 := by exact prefixLift 1467616
  have htrace : WordTrace (prefixWord ++ tailWord_1467616) baseStart_1467616 baseEnd_1467616 := by
    simpa [prefixWord, tailWord_1467616, baseEnd_1467616] using wordTrace_append hprefix tailTrace_1467616
  have hstable : (prefixWord ++ tailWord_1467616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467616).length < 2 ^ (prefixWord ++ tailWord_1467616).sum := by decide
  have hdescent : baseEnd_1467616 < baseStart_1467616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467623 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 6]
def baseStart_1467623 : Nat := 118140960795 + 1467623 * 2 ^ 59
def prefixEnd_1467623 : Nat := 4983230072969 + 3 ^ 40 * 1467623 * 2
def baseEnd_1467623 : Nat := 83732890954846294662559

theorem tailTrace_1467623 : CollatzResearch.WordTrace tailWord_1467623 prefixEnd_1467623 83732890954846294662559 := by
  unfold tailWord_1467623
  simp only [CollatzResearch.WordTrace]
  refine ⟨53528608362059995898239523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35685738908039997265493015 53528608362059995898239523)
  ·
    refine ⟨80292912543089993847359285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53528608362059995898239523 80292912543089993847359285)
    ·
      refine ⟨7527460550914686923189933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80292912543089993847359285 7527460550914686923189933)
      ·
        refine ⟨2822797706593007596196225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7527460550914686923189933 2822797706593007596196225)
        ·
          refine ⟨2117098279944755697147169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822797706593007596196225 2117098279944755697147169)
          ·
            refine ⟨1587823709958566772860377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117098279944755697147169 1587823709958566772860377)
            ·
              refine ⟨1190867782468925079645283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1587823709958566772860377 1190867782468925079645283)
              ·
                refine ⟨1786301673703387619467925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190867782468925079645283 1786301673703387619467925)
                ·
                  refine ⟨83732890954846294662559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1786301673703387619467925 83732890954846294662559)
                  ·
                    rfl

theorem cell23_1467623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 6].length) (baseStart_1467623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467623 prefixEnd_1467623 := by exact prefixLift 1467623
  have htrace : WordTrace (prefixWord ++ tailWord_1467623) baseStart_1467623 baseEnd_1467623 := by
    simpa [prefixWord, tailWord_1467623, baseEnd_1467623] using wordTrace_append hprefix tailTrace_1467623
  have hstable : (prefixWord ++ tailWord_1467623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467623).length < 2 ^ (prefixWord ++ tailWord_1467623).sum := by decide
  have hdescent : baseEnd_1467623 < baseStart_1467623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467649 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1467649 : Nat := 118140960795 + 1467649 * 2 ^ 59
def prefixEnd_1467649 : Nat := 4983230072969 + 3 ^ 40 * 1467649 * 2
def baseEnd_1467649 : Nat := 251203123030211183412637

theorem tailTrace_1467649 : CollatzResearch.WordTrace tailWord_1467649 prefixEnd_1467649 251203123030211183412637 := by
  unfold tailWord_1467649
  simp only [CollatzResearch.WordTrace]
  refine ⟨53529556659965802338686001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35686371106643868225790667 53529556659965802338686001)
  ·
    refine ⟨40147167494974351754014501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53529556659965802338686001 40147167494974351754014501)
    ·
      refine ⟨7527593905307690953877719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40147167494974351754014501 7527593905307690953877719)
      ·
        refine ⟨11291390857961536430816579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7527593905307690953877719 11291390857961536430816579)
        ·
          refine ⟨16937086286942304646224869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11291390857961536430816579 16937086286942304646224869)
          ·
            refine ⟨3175703678801682121167163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16937086286942304646224869 3175703678801682121167163)
            ·
              refine ⟨4763555518202523181750745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175703678801682121167163 4763555518202523181750745)
              ·
                refine ⟨3572666638651892386313059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4763555518202523181750745 3572666638651892386313059)
                ·
                  refine ⟨5358999957977838579469589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572666638651892386313059 5358999957977838579469589)
                  ·
                    refine ⟨251203123030211183412637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5358999957977838579469589 251203123030211183412637)
                    ·
                      rfl

theorem cell23_1467649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1467649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467649 prefixEnd_1467649 := by exact prefixLift 1467649
  have htrace : WordTrace (prefixWord ++ tailWord_1467649) baseStart_1467649 baseEnd_1467649 := by
    simpa [prefixWord, tailWord_1467649, baseEnd_1467649] using wordTrace_append hprefix tailTrace_1467649
  have hstable : (prefixWord ++ tailWord_1467649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467649).length < 2 ^ (prefixWord ++ tailWord_1467649).sum := by decide
  have hdescent : baseEnd_1467649 < baseStart_1467649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467659 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5]
def baseStart_1467659 : Nat := 118140960795 + 1467659 * 2 ^ 59
def prefixEnd_1467659 : Nat := 4983230072969 + 3 ^ 40 * 1467659 * 2
def baseEnd_1467659 : Nat := 753614503897178511112865

theorem tailTrace_1467659 : CollatzResearch.WordTrace tailWord_1467659 prefixEnd_1467659 753614503897178511112865 := by
  unfold tailWord_1467659
  simp only [CollatzResearch.WordTrace]
  refine ⟨53529921389929574046550031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35686614259953049364366687 53529921389929574046550031)
  ·
    refine ⟨80294882084894361069825047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53529921389929574046550031 80294882084894361069825047)
    ·
      refine ⟨120442323127341541604737571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80294882084894361069825047 120442323127341541604737571)
      ·
        refine ⟨180663484691012312407106357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120442323127341541604737571 180663484691012312407106357)
        ·
          refine ⟨16937201689782404288166221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180663484691012312407106357 16937201689782404288166221)
          ·
            refine ⟨6351450633668401608062333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16937201689782404288166221 6351450633668401608062333)
            ·
              refine ⟨2381793987625650603023375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6351450633668401608062333 2381793987625650603023375)
              ·
                refine ⟨3572690981438475904535063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381793987625650603023375 3572690981438475904535063)
                ·
                  refine ⟨5359036472157713856802595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572690981438475904535063 5359036472157713856802595)
                  ·
                    refine ⟨8038554708236570785203893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359036472157713856802595 8038554708236570785203893)
                    ·
                      refine ⟨753614503897178511112865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8038554708236570785203893 753614503897178511112865)
                      ·
                        rfl

theorem cell23_1467659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 5].length) (baseStart_1467659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467659 prefixEnd_1467659 := by exact prefixLift 1467659
  have htrace : WordTrace (prefixWord ++ tailWord_1467659) baseStart_1467659 baseEnd_1467659 := by
    simpa [prefixWord, tailWord_1467659, baseEnd_1467659] using wordTrace_append hprefix tailTrace_1467659
  have hstable : (prefixWord ++ tailWord_1467659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467659).length < 2 ^ (prefixWord ++ tailWord_1467659).sum := by decide
  have hdescent : baseEnd_1467659 < baseStart_1467659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467662 : List Nat := [4, 1, 1, 2, 1, 14]
def baseStart_1467662 : Nat := 118140960795 + 1467662 * 2 ^ 59
def prefixEnd_1467662 : Nat := 4983230072969 + 3 ^ 40 * 1467662 * 2
def baseEnd_1467662 : Nat := 3101300593988238680557

theorem tailTrace_1467662 : CollatzResearch.WordTrace tailWord_1467662 prefixEnd_1467662 3101300593988238680557 := by
  unfold tailWord_1467662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6691253851114838194863655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35686687205945803705939493 6691253851114838194863655)
  ·
    refine ⟨10036880776672257292295483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6691253851114838194863655 10036880776672257292295483)
    ·
      refine ⟨15055321165008385938443225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10036880776672257292295483 15055321165008385938443225)
      ·
        refine ⟨11291490873756289453832419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15055321165008385938443225 11291490873756289453832419)
        ·
          refine ⟨16937236310634434180748629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11291490873756289453832419 16937236310634434180748629)
          ·
            refine ⟨3101300593988238680557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 16937236310634434180748629 3101300593988238680557)
            ·
              rfl

theorem cell23_1467662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 14].length) (baseStart_1467662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467662 prefixEnd_1467662 := by exact prefixLift 1467662
  have htrace : WordTrace (prefixWord ++ tailWord_1467662) baseStart_1467662 baseEnd_1467662 := by
    simpa [prefixWord, tailWord_1467662, baseEnd_1467662] using wordTrace_append hprefix tailTrace_1467662
  have hstable : (prefixWord ++ tailWord_1467662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467662).length < 2 ^ (prefixWord ++ tailWord_1467662).sum := by decide
  have hdescent : baseEnd_1467662 < baseStart_1467662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467690 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_1467690 : Nat := 118140960795 + 1467690 * 2 ^ 59
def prefixEnd_1467690 : Nat := 4983230072969 + 3 ^ 40 * 1467690 * 2
def baseEnd_1467690 : Nat := 753630421797467889825223

theorem tailTrace_1467690 : CollatzResearch.WordTrace tailWord_1467690 prefixEnd_1467690 753630421797467889825223 := by
  unfold tailWord_1467690
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382763013204316585232131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35687368035211510893952349 13382763013204316585232131)
  ·
    refine ⟨20074144519806474877848197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13382763013204316585232131 20074144519806474877848197)
    ·
      refine ⟨3763902097463714039596537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20074144519806474877848197 3763902097463714039596537)
      ·
        refine ⟨2822926573097785529697403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3763902097463714039596537 2822926573097785529697403)
        ·
          refine ⟨4234389859646678294546105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822926573097785529697403 4234389859646678294546105)
          ·
            refine ⟨3175792394735008720909579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234389859646678294546105 3175792394735008720909579)
            ·
              refine ⟨4763688592102513081364369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175792394735008720909579 4763688592102513081364369)
              ·
                refine ⟨3572766444076884811023277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4763688592102513081364369 3572766444076884811023277)
                ·
                  refine ⟨1339787416528831804133729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3572766444076884811023277 1339787416528831804133729)
                  ·
                    refine ⟨1004840562396623853100297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1339787416528831804133729 1004840562396623853100297)
                    ·
                      refine ⟨753630421797467889825223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1004840562396623853100297 753630421797467889825223)
                      ·
                        rfl

theorem cell23_1467690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_1467690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467690 prefixEnd_1467690 := by exact prefixLift 1467690
  have htrace : WordTrace (prefixWord ++ tailWord_1467690) baseStart_1467690 baseEnd_1467690 := by
    simpa [prefixWord, tailWord_1467690, baseEnd_1467690] using wordTrace_append hprefix tailTrace_1467690
  have hstable : (prefixWord ++ tailWord_1467690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467690).length < 2 ^ (prefixWord ++ tailWord_1467690).sum := by decide
  have hdescent : baseEnd_1467690 < baseStart_1467690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467692 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1467692 : Nat := 118140960795 + 1467692 * 2 ^ 59
def prefixEnd_1467692 : Nat := 4983230072969 + 3 ^ 40 * 1467692 * 2
def baseEnd_1467692 : Nat := 251210482919592294000071

theorem tailTrace_1467692 : CollatzResearch.WordTrace tailWord_1467692 prefixEnd_1467692 251210482919592294000071 := by
  unfold tailWord_1467692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765562499405010341250665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35687416665873347121667553 26765562499405010341250665)
  ·
    refine ⟨20074171874553757755937999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26765562499405010341250665 20074171874553757755937999)
    ·
      refine ⟨30111257811830636633906999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20074171874553757755937999 30111257811830636633906999)
      ·
        refine ⟨45166886717745954950860499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30111257811830636633906999 45166886717745954950860499)
        ·
          refine ⟨67750330076618932426290749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45166886717745954950860499 67750330076618932426290749)
          ·
            refine ⟨25406373778732099659859031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67750330076618932426290749 25406373778732099659859031)
            ·
              refine ⟨38109560668098149489788547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25406373778732099659859031 38109560668098149489788547)
              ·
                refine ⟨57164341002147224234682821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38109560668098149489788547 57164341002147224234682821)
                ·
                  refine ⟨10718313937902604544003029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57164341002147224234682821 10718313937902604544003029)
                  ·
                    refine ⟨251210482919592294000071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10718313937902604544003029 251210482919592294000071)
                    ·
                      rfl

theorem cell23_1467692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1467692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467692 prefixEnd_1467692 := by exact prefixLift 1467692
  have htrace : WordTrace (prefixWord ++ tailWord_1467692) baseStart_1467692 baseEnd_1467692 := by
    simpa [prefixWord, tailWord_1467692, baseEnd_1467692] using wordTrace_append hprefix tailTrace_1467692
  have hstable : (prefixWord ++ tailWord_1467692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467692).length < 2 ^ (prefixWord ++ tailWord_1467692).sum := by decide
  have hdescent : baseEnd_1467692 < baseStart_1467692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467693 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1467693 : Nat := 118140960795 + 1467693 * 2 ^ 59
def prefixEnd_1467693 : Nat := 4983230072969 + 3 ^ 40 * 1467693 * 2
def baseEnd_1467693 : Nat := 753631962239431378087709

theorem tailTrace_1467693 : CollatzResearch.WordTrace tailWord_1467693 prefixEnd_1467693 753631962239431378087709 := by
  unfold tailWord_1467693
  simp only [CollatzResearch.WordTrace]
  refine ⟨53531161471806397853287733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35687440981204265235525155 53531161471806397853287733)
  ·
    refine ⟨5018546387981849798745725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53531161471806397853287733 5018546387981849798745725)
    ·
      refine ⟨1881954895493193674529647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5018546387981849798745725 1881954895493193674529647)
      ·
        refine ⟨2822932343239790511794471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881954895493193674529647 2822932343239790511794471)
        ·
          refine ⟨4234398514859685767691707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822932343239790511794471 4234398514859685767691707)
          ·
            refine ⟨6351597772289528651537561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4234398514859685767691707 6351597772289528651537561)
            ·
              refine ⟨4763698329217146488653171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351597772289528651537561 4763698329217146488653171)
              ·
                refine ⟨7145547493825719732979757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763698329217146488653171 7145547493825719732979757)
                ·
                  refine ⟨2679580310184644899867409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7145547493825719732979757 2679580310184644899867409)
                  ·
                    refine ⟨2009685232638483674900557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2679580310184644899867409 2009685232638483674900557)
                    ·
                      refine ⟨753631962239431378087709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009685232638483674900557 753631962239431378087709)
                      ·
                        rfl

theorem cell23_1467693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1467693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467693 prefixEnd_1467693 := by exact prefixLift 1467693
  have htrace : WordTrace (prefixWord ++ tailWord_1467693) baseStart_1467693 baseEnd_1467693 := by
    simpa [prefixWord, tailWord_1467693, baseEnd_1467693] using wordTrace_append hprefix tailTrace_1467693
  have hstable : (prefixWord ++ tailWord_1467693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467693).length < 2 ^ (prefixWord ++ tailWord_1467693).sum := by decide
  have hdescent : baseEnd_1467693 < baseStart_1467693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467706 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_1467706 : Nat := 118140960795 + 1467706 * 2 ^ 59
def prefixEnd_1467706 : Nat := 4983230072969 + 3 ^ 40 * 1467706 * 2
def baseEnd_1467706 : Nat := 753638637487939827225149

theorem tailTrace_1467706 : CollatzResearch.WordTrace tailWord_1467706 prefixEnd_1467706 753638637487939827225149 := by
  unfold tailWord_1467706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382908905189825268377743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35687757080506200715673981 13382908905189825268377743)
  ·
    refine ⟨20074363357784737902566615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13382908905189825268377743 20074363357784737902566615)
    ·
      refine ⟨30111545036677106853849923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20074363357784737902566615 30111545036677106853849923)
      ·
        refine ⟨45167317555015660280774885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30111545036677106853849923 45167317555015660280774885)
        ·
          refine ⟨8468872041565436302645291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45167317555015660280774885 8468872041565436302645291)
          ·
            refine ⟨12703308062348154453967937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468872041565436302645291 12703308062348154453967937)
            ·
              refine ⟨9527481046761115840475953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12703308062348154453967937 9527481046761115840475953)
              ·
                refine ⟨7145610785070836880356965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9527481046761115840475953 7145610785070836880356965)
                ·
                  refine ⟨1339802022200781915066931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7145610785070836880356965 1339802022200781915066931)
                  ·
                    refine ⟨2009703033301172872600397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1339802022200781915066931 2009703033301172872600397)
                    ·
                      refine ⟨753638637487939827225149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009703033301172872600397 753638637487939827225149)
                      ·
                        rfl

theorem cell23_1467706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_1467706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467706 prefixEnd_1467706 := by exact prefixLift 1467706
  have htrace : WordTrace (prefixWord ++ tailWord_1467706) baseStart_1467706 baseEnd_1467706 := by
    simpa [prefixWord, tailWord_1467706, baseEnd_1467706] using wordTrace_append hprefix tailTrace_1467706
  have hstable : (prefixWord ++ tailWord_1467706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467706).length < 2 ^ (prefixWord ++ tailWord_1467706).sum := by decide
  have hdescent : baseEnd_1467706 < baseStart_1467706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467734 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_1467734 : Nat := 118140960795 + 1467734 * 2 ^ 59
def prefixEnd_1467734 : Nat := 4983230072969 + 3 ^ 40 * 1467734 * 2
def baseEnd_1467734 : Nat := 251217671648755239225007

theorem tailTrace_1467734 : CollatzResearch.WordTrace tailWord_1467734 prefixEnd_1467734 251217671648755239225007 := by
  unfold tailWord_1467734
  simp only [CollatzResearch.WordTrace]
  refine ⟨3345791054041116365970641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35688437909771907903686837 3345791054041116365970641)
  ·
    refine ⟨2509343290530837274477981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3345791054041116365970641 2509343290530837274477981)
    ·
      refine ⟨941003733949063977929243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2509343290530837274477981 941003733949063977929243)
      ·
        refine ⟨1411505600923595966893865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941003733949063977929243 1411505600923595966893865)
        ·
          refine ⟨1058629200692696975170399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411505600923595966893865 1058629200692696975170399)
          ·
            refine ⟨1587943801039045462755599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058629200692696975170399 1587943801039045462755599)
            ·
              refine ⟨2381915701558568194133399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587943801039045462755599 2381915701558568194133399)
              ·
                refine ⟨3572873552337852291200099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381915701558568194133399 3572873552337852291200099)
                ·
                  refine ⟨5359310328506778436800149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572873552337852291200099 5359310328506778436800149)
                  ·
                    refine ⟨251217671648755239225007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5359310328506778436800149 251217671648755239225007)
                    ·
                      rfl

theorem cell23_1467734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_1467734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467734 prefixEnd_1467734 := by exact prefixLift 1467734
  have htrace : WordTrace (prefixWord ++ tailWord_1467734) baseStart_1467734 baseEnd_1467734 := by
    simpa [prefixWord, tailWord_1467734, baseEnd_1467734] using wordTrace_append hprefix tailTrace_1467734
  have hstable : (prefixWord ++ tailWord_1467734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467734).length < 2 ^ (prefixWord ++ tailWord_1467734).sum := by decide
  have hdescent : baseEnd_1467734 < baseStart_1467734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467749 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1467749 : Nat := 118140960795 + 1467749 * 2 ^ 59
def prefixEnd_1467749 : Nat := 4983230072969 + 3 ^ 40 * 1467749 * 2
def baseEnd_1467749 : Nat := 753660717156083158987451

theorem tailTrace_1467749 : CollatzResearch.WordTrace tailWord_1467749 prefixEnd_1467749 753660717156083158987451 := by
  unfold tailWord_1467749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53533203959603519417326301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35688802639735679611550867 53533203959603519417326301)
  ·
    refine ⟨20074951484851319781497363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53533203959603519417326301 20074951484851319781497363)
    ·
      refine ⟨30112427227276979672246045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20074951484851319781497363 30112427227276979672246045)
      ·
        refine ⟨11292160210228867377092267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30112427227276979672246045 11292160210228867377092267)
        ·
          refine ⟨16938240315343301065638401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11292160210228867377092267 16938240315343301065638401)
          ·
            refine ⟨12703680236507475799228801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16938240315343301065638401 12703680236507475799228801)
            ·
              refine ⟨9527760177380606849421601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12703680236507475799228801 9527760177380606849421601)
              ·
                refine ⟨7145820133035455137066201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9527760177380606849421601 7145820133035455137066201)
                ·
                  refine ⟨5359365099776591352799651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145820133035455137066201 5359365099776591352799651)
                  ·
                    refine ⟨8039047649664887029199477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359365099776591352799651 8039047649664887029199477)
                    ·
                      refine ⟨753660717156083158987451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8039047649664887029199477 753660717156083158987451)
                      ·
                        rfl

theorem cell23_1467749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1467749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467749 prefixEnd_1467749 := by exact prefixLift 1467749
  have htrace : WordTrace (prefixWord ++ tailWord_1467749) baseStart_1467749 baseEnd_1467749 := by
    simpa [prefixWord, tailWord_1467749, baseEnd_1467749] using wordTrace_append hprefix tailTrace_1467749
  have hstable : (prefixWord ++ tailWord_1467749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467749).length < 2 ^ (prefixWord ++ tailWord_1467749).sum := by decide
  have hdescent : baseEnd_1467749 < baseStart_1467749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467799 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 6, 5]
def baseStart_1467799 : Nat := 118140960795 + 1467799 * 2 ^ 59
def prefixEnd_1467799 : Nat := 4983230072969 + 3 ^ 40 * 1467799 * 2
def baseEnd_1467799 : Nat := 251228797062935987787407

theorem tailTrace_1467799 : CollatzResearch.WordTrace tailWord_1467799 prefixEnd_1467799 251228797062935987787407 := by
  unfold tailWord_1467799
  simp only [CollatzResearch.WordTrace]
  refine ⟨53535027609422377956646451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35690018406281585304430967 53535027609422377956646451)
  ·
    refine ⟨80302541414133566934969677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53535027609422377956646451 80302541414133566934969677)
    ·
      refine ⟨30113453030300087600613629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80302541414133566934969677 30113453030300087600613629)
      ·
        refine ⟨11292544886362532850230111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30113453030300087600613629 11292544886362532850230111)
        ·
          refine ⟨16938817329543799275345167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11292544886362532850230111 16938817329543799275345167)
          ·
            refine ⟨25408225994315698913017751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16938817329543799275345167 25408225994315698913017751)
            ·
              refine ⟨38112338991473548369526627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25408225994315698913017751 38112338991473548369526627)
              ·
                refine ⟨57168508487210322554289941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38112338991473548369526627 57168508487210322554289941)
                ·
                  refine ⟨2679773835337983869732341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57168508487210322554289941 2679773835337983869732341)
                  ·
                    refine ⟨251228797062935987787407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2679773835337983869732341 251228797062935987787407)
                    ·
                      rfl

theorem cell23_1467799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_1467799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467799 prefixEnd_1467799 := by exact prefixLift 1467799
  have htrace : WordTrace (prefixWord ++ tailWord_1467799) baseStart_1467799 baseEnd_1467799 := by
    simpa [prefixWord, tailWord_1467799, baseEnd_1467799] using wordTrace_append hprefix tailTrace_1467799
  have hstable : (prefixWord ++ tailWord_1467799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467799).length < 2 ^ (prefixWord ++ tailWord_1467799).sum := by decide
  have hdescent : baseEnd_1467799 < baseStart_1467799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467849 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_1467849 : Nat := 118140960795 + 1467849 * 2 ^ 59
def prefixEnd_1467849 : Nat := 4983230072969 + 3 ^ 40 * 1467849 * 2
def baseEnd_1467849 : Nat := 753712065221532767736991

theorem tailTrace_1467849 : CollatzResearch.WordTrace tailWord_1467849 prefixEnd_1467849 753712065221532767736991 := by
  unfold tailWord_1467849
  simp only [CollatzResearch.WordTrace]
  refine ⟨53536851259241236495966601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35691234172827490997311067 53536851259241236495966601)
  ·
    refine ⟨40152638444430927371974951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53536851259241236495966601 40152638444430927371974951)
    ·
      refine ⟨60228957666646391057962427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40152638444430927371974951 60228957666646391057962427)
      ·
        refine ⟨90343436499969586586943641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60228957666646391057962427 90343436499969586586943641)
        ·
          refine ⟨67757577374977189940207731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90343436499969586586943641 67757577374977189940207731)
          ·
            refine ⟨101636366062465784910311597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67757577374977189940207731 101636366062465784910311597)
            ·
              refine ⟨38113637273424669341366849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101636366062465784910311597 38113637273424669341366849)
              ·
                refine ⟨28585227955068502006025137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38113637273424669341366849 28585227955068502006025137)
                ·
                  refine ⟨21438920966301376504518853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28585227955068502006025137 21438920966301376504518853)
                  ·
                    refine ⟨4019797681181508094597285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21438920966301376504518853 4019797681181508094597285)
                    ·
                      refine ⟨753712065221532767736991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4019797681181508094597285 753712065221532767736991)
                      ·
                        rfl

theorem cell23_1467849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_1467849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467849 prefixEnd_1467849 := by exact prefixLift 1467849
  have htrace : WordTrace (prefixWord ++ tailWord_1467849) baseStart_1467849 baseEnd_1467849 := by
    simpa [prefixWord, tailWord_1467849, baseEnd_1467849] using wordTrace_append hprefix tailTrace_1467849
  have hstable : (prefixWord ++ tailWord_1467849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467849).length < 2 ^ (prefixWord ++ tailWord_1467849).sum := by decide
  have hdescent : baseEnd_1467849 < baseStart_1467849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467873 : List Nat := [1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_1467873 : Nat := 118140960795 + 1467873 * 2 ^ 59
def prefixEnd_1467873 : Nat := 4983230072969 + 3 ^ 40 * 1467873 * 2
def baseEnd_1467873 : Nat := 753724388757240673836881

theorem tailTrace_1467873 : CollatzResearch.WordTrace tailWord_1467873 prefixEnd_1467873 753724388757240673836881 := by
  unfold tailWord_1467873
  simp only [CollatzResearch.WordTrace]
  refine ⟨53537726611154288594840273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35691817740769525729893515 53537726611154288594840273)
  ·
    refine ⟨40153294958365716446130205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53537726611154288594840273 40153294958365716446130205)
    ·
      refine ⟨15057485609387143667298827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40153294958365716446130205 15057485609387143667298827)
      ·
        refine ⟨22586228414080715500948241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15057485609387143667298827 22586228414080715500948241)
        ·
          refine ⟨16939671310560536625711181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22586228414080715500948241 16939671310560536625711181)
          ·
            refine ⟨6352376741460201234641693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16939671310560536625711181 6352376741460201234641693)
            ·
              refine ⟨2382141278047575462990635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6352376741460201234641693 2382141278047575462990635)
              ·
                refine ⟨3573211917071363194485953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382141278047575462990635 3573211917071363194485953)
                ·
                  refine ⟨2679908937803522395864465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3573211917071363194485953 2679908937803522395864465)
                  ·
                    refine ⟨2009931703352641796898349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2679908937803522395864465 2009931703352641796898349)
                    ·
                      refine ⟨753724388757240673836881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2009931703352641796898349 753724388757240673836881)
                      ·
                        rfl

theorem cell23_1467873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_1467873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467873 prefixEnd_1467873 := by exact prefixLift 1467873
  have htrace : WordTrace (prefixWord ++ tailWord_1467873) baseStart_1467873 baseEnd_1467873 := by
    simpa [prefixWord, tailWord_1467873, baseEnd_1467873] using wordTrace_append hprefix tailTrace_1467873
  have hstable : (prefixWord ++ tailWord_1467873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467873).length < 2 ^ (prefixWord ++ tailWord_1467873).sum := by decide
  have hdescent : baseEnd_1467873 < baseStart_1467873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467880 : List Nat := [2, 1, 4, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1467880 : Nat := 118140960795 + 1467880 * 2 ^ 59
def prefixEnd_1467880 : Nat := 4983230072969 + 3 ^ 40 * 1467880 * 2
def baseEnd_1467880 : Nat := 251242661040607382149783

theorem tailTrace_1467880 : CollatzResearch.WordTrace tailWord_1467880 prefixEnd_1467880 251242661040607382149783 := by
  unfold tailWord_1467880
  simp only [CollatzResearch.WordTrace]
  refine ⟨26768990961064464395172547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35691987948085952526896729 26768990961064464395172547)
  ·
    refine ⟨40153486441596696592758821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26768990961064464395172547 40153486441596696592758821)
    ·
      refine ⟨7528778707799380611142279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40153486441596696592758821 7528778707799380611142279)
      ·
        refine ⟨11293168061699070916713419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7528778707799380611142279 11293168061699070916713419)
        ·
          refine ⟨16939752092548606375070129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293168061699070916713419 16939752092548606375070129)
          ·
            refine ⟨12704814069411454781302597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16939752092548606375070129 12704814069411454781302597)
            ·
              refine ⟨2382152638014647771494237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12704814069411454781302597 2382152638014647771494237)
              ·
                refine ⟨893307239255492914310339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382152638014647771494237 893307239255492914310339)
                ·
                  refine ⟨1339960858883239371465509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893307239255492914310339 1339960858883239371465509)
                  ·
                    refine ⟨251242661040607382149783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1339960858883239371465509 251242661040607382149783)
                    ·
                      rfl

theorem cell23_1467880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1467880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467880 prefixEnd_1467880 := by exact prefixLift 1467880
  have htrace : WordTrace (prefixWord ++ tailWord_1467880) baseStart_1467880 baseEnd_1467880 := by
    simpa [prefixWord, tailWord_1467880, baseEnd_1467880] using wordTrace_append hprefix tailTrace_1467880
  have hstable : (prefixWord ++ tailWord_1467880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467880).length < 2 ^ (prefixWord ++ tailWord_1467880).sum := by decide
  have hdescent : baseEnd_1467880 < baseStart_1467880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467893 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 8]
def baseStart_1467893 : Nat := 118140960795 + 1467893 * 2 ^ 59
def prefixEnd_1467893 : Nat := 4983230072969 + 3 ^ 40 * 1467893 * 2
def baseEnd_1467893 : Nat := 83748295374481177287421

theorem tailTrace_1467893 : CollatzResearch.WordTrace tailWord_1467893 prefixEnd_1467893 83748295374481177287421 := by
  unfold tailWord_1467893
  simp only [CollatzResearch.WordTrace]
  refine ⟨53538456071081832010568333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35692304047387888007045555 53538456071081832010568333)
  ·
    refine ⟨20076921026655687003963125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53538456071081832010568333 20076921026655687003963125)
    ·
      refine ⟨1882211346248970656621543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20076921026655687003963125 1882211346248970656621543)
      ·
        refine ⟨2823317019373455984932315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882211346248970656621543 2823317019373455984932315)
        ·
          refine ⟨4234975529060183977398473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823317019373455984932315 4234975529060183977398473)
          ·
            refine ⟨3176231646795137983048855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234975529060183977398473 3176231646795137983048855)
            ·
              refine ⟨4764347470192706974573283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176231646795137983048855 4764347470192706974573283)
              ·
                refine ⟨7146521205289060461859925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764347470192706974573283 7146521205289060461859925)
                ·
                  refine ⟨83748295374481177287421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7146521205289060461859925 83748295374481177287421)
                  ·
                    rfl

theorem cell23_1467893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 8].length) (baseStart_1467893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467893 prefixEnd_1467893 := by exact prefixLift 1467893
  have htrace : WordTrace (prefixWord ++ tailWord_1467893) baseStart_1467893 baseEnd_1467893 := by
    simpa [prefixWord, tailWord_1467893, baseEnd_1467893] using wordTrace_append hprefix tailTrace_1467893
  have hstable : (prefixWord ++ tailWord_1467893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467893).length < 2 ^ (prefixWord ++ tailWord_1467893).sum := by decide
  have hdescent : baseEnd_1467893 < baseStart_1467893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467899 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_1467899 : Nat := 118140960795 + 1467899 * 2 ^ 59
def prefixEnd_1467899 : Nat := 4983230072969 + 3 ^ 40 * 1467899 * 2
def baseEnd_1467899 : Nat := 753737739254257572111761

theorem tailTrace_1467899 : CollatzResearch.WordTrace tailWord_1467899 prefixEnd_1467899 753737739254257572111761 := by
  unfold tailWord_1467899
  simp only [CollatzResearch.WordTrace]
  refine ⟨53538674909060095035286751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35692449939373396690191167 53538674909060095035286751)
  ·
    refine ⟨80308012363590142552930127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53538674909060095035286751 80308012363590142552930127)
    ·
      refine ⟨120462018545385213829395191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80308012363590142552930127 120462018545385213829395191)
      ·
        refine ⟨180693027818077820744092787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120462018545385213829395191 180693027818077820744092787)
        ·
          refine ⟨271039541727116731116139181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180693027818077820744092787 271039541727116731116139181)
          ·
            refine ⟨101639828147668774168552193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271039541727116731116139181 101639828147668774168552193)
            ·
              refine ⟨76229871110751580626414145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101639828147668774168552193 76229871110751580626414145)
              ·
                refine ⟨57172403333063685469810609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76229871110751580626414145 57172403333063685469810609)
                ·
                  refine ⟨42879302499797764102357957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57172403333063685469810609 42879302499797764102357957)
                  ·
                    refine ⟨8039869218712080769192117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42879302499797764102357957 8039869218712080769192117)
                    ·
                      refine ⟨753737739254257572111761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8039869218712080769192117 753737739254257572111761)
                      ·
                        rfl

theorem cell23_1467899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_1467899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467899 prefixEnd_1467899 := by exact prefixLift 1467899
  have htrace : WordTrace (prefixWord ++ tailWord_1467899) baseStart_1467899 baseEnd_1467899 := by
    simpa [prefixWord, tailWord_1467899, baseEnd_1467899] using wordTrace_append hprefix tailTrace_1467899
  have hstable : (prefixWord ++ tailWord_1467899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467899).length < 2 ^ (prefixWord ++ tailWord_1467899).sum := by decide
  have hdescent : baseEnd_1467899 < baseStart_1467899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467923 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 1, 5]
def baseStart_1467923 : Nat := 118140960795 + 1467923 * 2 ^ 59
def prefixEnd_1467923 : Nat := 4983230072969 + 3 ^ 40 * 1467923 * 2
def baseEnd_1467923 : Nat := 251250020929988492737217

theorem tailTrace_1467923 : CollatzResearch.WordTrace tailWord_1467923 prefixEnd_1467923 251250020929988492737217 := by
  unfold tailWord_1467923
  simp only [CollatzResearch.WordTrace]
  refine ⟨53539550260973147134160423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35693033507315431422773615 53539550260973147134160423)
  ·
    refine ⟨80309325391459720701240635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53539550260973147134160423 80309325391459720701240635)
    ·
      refine ⟨120463988087189581051860953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80309325391459720701240635 120463988087189581051860953)
      ·
        refine ⟨90347991065392185788895715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120463988087189581051860953 90347991065392185788895715)
        ·
          refine ⟨135521986598088278683343573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90347991065392185788895715 135521986598088278683343573)
          ·
            refine ⟨3176296560892694031640865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 135521986598088278683343573 3176296560892694031640865)
            ·
              refine ⟨2382222420669520523730649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176296560892694031640865 2382222420669520523730649)
              ·
                refine ⟨1786666815502140392797987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382222420669520523730649 1786666815502140392797987)
                ·
                  refine ⟨2680000223253210589196981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786666815502140392797987 2680000223253210589196981)
                  ·
                    refine ⟨251250020929988492737217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2680000223253210589196981 251250020929988492737217)
                    ·
                      rfl

theorem cell23_1467923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 5].length) (baseStart_1467923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467923 prefixEnd_1467923 := by exact prefixLift 1467923
  have htrace : WordTrace (prefixWord ++ tailWord_1467923) baseStart_1467923 baseEnd_1467923 := by
    simpa [prefixWord, tailWord_1467923, baseEnd_1467923] using wordTrace_append hprefix tailTrace_1467923
  have hstable : (prefixWord ++ tailWord_1467923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467923).length < 2 ^ (prefixWord ++ tailWord_1467923).sum := by decide
  have hdescent : baseEnd_1467923 < baseStart_1467923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467937 : List Nat := [1, 2, 3, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1467937 : Nat := 118140960795 + 1467937 * 2 ^ 59
def prefixEnd_1467937 : Nat := 4983230072969 + 3 ^ 40 * 1467937 * 2
def baseEnd_1467937 : Nat := 753757251519128423436587

theorem tailTrace_1467937 : CollatzResearch.WordTrace tailWord_1467937 prefixEnd_1467937 753757251519128423436587 := by
  unfold tailWord_1467937
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540060882922427525170065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35693373921948285016780043 53540060882922427525170065)
  ·
    refine ⟨40155045662191820643877549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53540060882922427525170065 40155045662191820643877549)
    ·
      refine ⟨15058142123321932741454081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40155045662191820643877549 15058142123321932741454081)
      ·
        refine ⟨11293606592491449556090561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15058142123321932741454081 11293606592491449556090561)
        ·
          refine ⟨8470204944368587167067921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11293606592491449556090561 8470204944368587167067921)
          ·
            refine ⟨6352653708276440375300941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8470204944368587167067921 6352653708276440375300941)
            ·
              refine ⟨2382245140603665140737853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6352653708276440375300941 2382245140603665140737853)
              ·
                refine ⟨893341927726374427776695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382245140603665140737853 893341927726374427776695)
                ·
                  refine ⟨1340012891589561641665043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893341927726374427776695 1340012891589561641665043)
                  ·
                    refine ⟨2010019337384342462497565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340012891589561641665043 2010019337384342462497565)
                    ·
                      refine ⟨753757251519128423436587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010019337384342462497565 753757251519128423436587)
                      ·
                        rfl

theorem cell23_1467937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1467937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467937 prefixEnd_1467937 := by exact prefixLift 1467937
  have htrace : WordTrace (prefixWord ++ tailWord_1467937) baseStart_1467937 baseEnd_1467937 := by
    simpa [prefixWord, tailWord_1467937, baseEnd_1467937] using wordTrace_append hprefix tailTrace_1467937
  have hstable : (prefixWord ++ tailWord_1467937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467937).length < 2 ^ (prefixWord ++ tailWord_1467937).sum := by decide
  have hdescent : baseEnd_1467937 < baseStart_1467937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467953 : List Nat := [1, 2, 2, 3, 1, 1, 1, 6, 2, 4]
def baseStart_1467953 : Nat := 118140960795 + 1467953 * 2 ^ 59
def prefixEnd_1467953 : Nat := 4983230072969 + 3 ^ 40 * 1467953 * 2
def baseEnd_1467953 : Nat := 251255155736533453612171

theorem tailTrace_1467953 : CollatzResearch.WordTrace tailWord_1467953 prefixEnd_1467953 251255155736533453612171 := by
  unfold tailWord_1467953
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540644450864462257752513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35693762967242974838501675 53540644450864462257752513)
  ·
    refine ⟨40155483338148346693314385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53540644450864462257752513 40155483338148346693314385)
    ·
      refine ⟨30116612503611260019985789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40155483338148346693314385 30116612503611260019985789)
      ·
        refine ⟨11293729688854222507494671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30116612503611260019985789 11293729688854222507494671)
        ·
          refine ⟨16940594533281333761242007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293729688854222507494671 16940594533281333761242007)
          ·
            refine ⟨25410891799922000641863011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16940594533281333761242007 25410891799922000641863011)
            ·
              refine ⟨38116337699883000962794517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25410891799922000641863011 38116337699883000962794517)
              ·
                refine ⟨1786703329682015670130993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38116337699883000962794517 1786703329682015670130993)
                ·
                  refine ⟨1340027497261511752598245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786703329682015670130993 1340027497261511752598245)
                  ·
                    refine ⟨251255155736533453612171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1340027497261511752598245 251255155736533453612171)
                    ·
                      rfl

theorem cell23_1467953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_1467953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467953 prefixEnd_1467953 := by exact prefixLift 1467953
  have htrace : WordTrace (prefixWord ++ tailWord_1467953) baseStart_1467953 baseEnd_1467953 := by
    simpa [prefixWord, tailWord_1467953, baseEnd_1467953] using wordTrace_append hprefix tailTrace_1467953
  have hstable : (prefixWord ++ tailWord_1467953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467953).length < 2 ^ (prefixWord ++ tailWord_1467953).sum := by decide
  have hdescent : baseEnd_1467953 < baseStart_1467953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467974 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1467974 : Nat := 118140960795 + 1467974 * 2 ^ 59
def prefixEnd_1467974 : Nat := 4983230072969 + 3 ^ 40 * 1467974 * 2
def baseEnd_1467974 : Nat := 251258750101114926224639

theorem tailTrace_1467974 : CollatzResearch.WordTrace tailWord_1467974 prefixEnd_1467974 251258750101114926224639 := by
  unfold tailWord_1467974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673169074493386963883343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35694273589192255229511317 1673169074493386963883343)
  ·
    refine ⟨2509753611740080445825015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673169074493386963883343 2509753611740080445825015)
    ·
      refine ⟨3764630417610120668737523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2509753611740080445825015 3764630417610120668737523)
      ·
        refine ⟨5646945626415181003106285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764630417610120668737523 5646945626415181003106285)
        ·
          refine ⟨2117604609905692876164857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5646945626415181003106285 2117604609905692876164857)
          ·
            refine ⟨1588203457429269657123643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2117604609905692876164857 1588203457429269657123643)
            ·
              refine ⟨2382305186143904485685465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588203457429269657123643 2382305186143904485685465)
              ·
                refine ⟨1786728889607928364264099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382305186143904485685465 1786728889607928364264099)
                ·
                  refine ⟨2680093334411892546396149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786728889607928364264099 2680093334411892546396149)
                  ·
                    refine ⟨251258750101114926224639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2680093334411892546396149 251258750101114926224639)
                    ·
                      rfl

theorem cell23_1467974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1467974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467974 prefixEnd_1467974 := by exact prefixLift 1467974
  have htrace : WordTrace (prefixWord ++ tailWord_1467974) baseStart_1467974 baseEnd_1467974 := by
    simpa [prefixWord, tailWord_1467974, baseEnd_1467974] using wordTrace_append hprefix tailTrace_1467974
  have hstable : (prefixWord ++ tailWord_1467974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467974).length < 2 ^ (prefixWord ++ tailWord_1467974).sum := by decide
  have hdescent : baseEnd_1467974 < baseStart_1467974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467980 : List Nat := [2, 2, 1, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1467980 : Nat := 118140960795 + 1467980 * 2 ^ 59
def prefixEnd_1467980 : Nat := 4983230072969 + 3 ^ 40 * 1467980 * 2
def baseEnd_1467980 : Nat := 753779331187271755198889

theorem tailTrace_1467980 : CollatzResearch.WordTrace tailWord_1467980 prefixEnd_1467980 753779331187271755198889 := by
  unfold tailWord_1467980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26770814610883322934492697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35694419481177763912656929 26770814610883322934492697)
  ·
    refine ⟨20078110958162492200869523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26770814610883322934492697 20078110958162492200869523)
    ·
      refine ⟨30117166437243738301304285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20078110958162492200869523 30117166437243738301304285)
      ·
        refine ⟨11293937413966401862989107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30117166437243738301304285 11293937413966401862989107)
        ·
          refine ⟨16940906120949602794483661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293937413966401862989107 16940906120949602794483661)
          ·
            refine ⟨6352839795356101047931373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16940906120949602794483661 6352839795356101047931373)
            ·
              refine ⟨2382314923258537892974265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6352839795356101047931373 2382314923258537892974265)
              ·
                refine ⟨1786736192443903419730699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382314923258537892974265 1786736192443903419730699)
                ·
                  refine ⟨2680104288665855129596049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786736192443903419730699 2680104288665855129596049)
                  ·
                    refine ⟨2010078216499391347197037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2680104288665855129596049 2010078216499391347197037)
                    ·
                      refine ⟨753779331187271755198889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010078216499391347197037 753779331187271755198889)
                      ·
                        rfl

theorem cell23_1467980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1467980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467980 prefixEnd_1467980 := by exact prefixLift 1467980
  have htrace : WordTrace (prefixWord ++ tailWord_1467980) baseStart_1467980 baseEnd_1467980 := by
    simpa [prefixWord, tailWord_1467980, baseEnd_1467980] using wordTrace_append hprefix tailTrace_1467980
  have hstable : (prefixWord ++ tailWord_1467980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467980).length < 2 ^ (prefixWord ++ tailWord_1467980).sum := by decide
  have hdescent : baseEnd_1467980 < baseStart_1467980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1467993 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 3]
def baseStart_1467993 : Nat := 118140960795 + 1467993 * 2 ^ 59
def prefixEnd_1467993 : Nat := 4983230072969 + 3 ^ 40 * 1467993 * 2
def baseEnd_1467993 : Nat := 753786006435780204336329

theorem tailTrace_1467993 : CollatzResearch.WordTrace tailWord_1467993 prefixEnd_1467993 753786006435780204336329 := by
  unfold tailWord_1467993
  simp only [CollatzResearch.WordTrace]
  refine ⟨53542103370719549089208633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35694735580479699392805755 53542103370719549089208633)
  ·
    refine ⟨40156577528039661816906475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53542103370719549089208633 40156577528039661816906475)
    ·
      refine ⟨60234866292059492725359713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40156577528039661816906475 60234866292059492725359713)
      ·
        refine ⟨45176149719044619544019785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60234866292059492725359713 45176149719044619544019785)
        ·
          refine ⟨33882112289283464658014839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45176149719044619544019785 33882112289283464658014839)
          ·
            refine ⟨50823168433925196987022259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33882112289283464658014839 50823168433925196987022259)
            ·
              refine ⟨76234752650887795480533389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50823168433925196987022259 76234752650887795480533389)
              ·
                refine ⟨28588032244082923305200021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76234752650887795480533389 28588032244082923305200021)
                ·
                  refine ⟨1340064011441387029931251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28588032244082923305200021 1340064011441387029931251)
                  ·
                    refine ⟨2010096017162080544896877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340064011441387029931251 2010096017162080544896877)
                    ·
                      refine ⟨753786006435780204336329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010096017162080544896877 753786006435780204336329)
                      ·
                        rfl

theorem cell23_1467993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_1467993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1467993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1467993 prefixEnd_1467993 := by exact prefixLift 1467993
  have htrace : WordTrace (prefixWord ++ tailWord_1467993) baseStart_1467993 baseEnd_1467993 := by
    simpa [prefixWord, tailWord_1467993, baseEnd_1467993] using wordTrace_append hprefix tailTrace_1467993
  have hstable : (prefixWord ++ tailWord_1467993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1467993).length < 2 ^ (prefixWord ++ tailWord_1467993).sum := by decide
  have hdescent : baseEnd_1467993 < baseStart_1467993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1467993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468083 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3]
def baseStart_1468083 : Nat := 118140960795 + 1468083 * 2 ^ 59
def prefixEnd_1468083 : Nat := 4983230072969 + 3 ^ 40 * 1468083 * 2
def baseEnd_1468083 : Nat := 753832219694684852210915

theorem tailTrace_1468083 : CollatzResearch.WordTrace tailWord_1468083 prefixEnd_1468083 753832219694684852210915 := by
  unfold tailWord_1468083
  simp only [CollatzResearch.WordTrace]
  refine ⟨53545385940393494459984903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35696923960262329639989935 53545385940393494459984903)
  ·
    refine ⟨80318078910590241689977355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53545385940393494459984903 80318078910590241689977355)
    ·
      refine ⟨120477118365885362534966033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80318078910590241689977355 120477118365885362534966033)
      ·
        refine ⟨90357838774414021901224525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120477118365885362534966033 90357838774414021901224525)
        ·
          refine ⟨33884189540405258212959197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90357838774414021901224525 33884189540405258212959197)
          ·
            refine ⟨12706571077651971829859699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33884189540405258212959197 12706571077651971829859699)
            ·
              refine ⟨19059856616477957744789549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12706571077651971829859699 19059856616477957744789549)
              ·
                refine ⟨7147446231179234154296081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19059856616477957744789549 7147446231179234154296081)
                ·
                  refine ⟨5360584673384425615722061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7147446231179234154296081 5360584673384425615722061)
                  ·
                    refine ⟨2010219252519159605895773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5360584673384425615722061 2010219252519159605895773)
                    ·
                      refine ⟨753832219694684852210915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010219252519159605895773 753832219694684852210915)
                      ·
                        rfl

theorem cell23_1468083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_1468083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468083 prefixEnd_1468083 := by exact prefixLift 1468083
  have htrace : WordTrace (prefixWord ++ tailWord_1468083) baseStart_1468083 baseEnd_1468083 := by
    simpa [prefixWord, tailWord_1468083, baseEnd_1468083] using wordTrace_append hprefix tailTrace_1468083
  have hstable : (prefixWord ++ tailWord_1468083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468083).length < 2 ^ (prefixWord ++ tailWord_1468083).sum := by decide
  have hdescent : baseEnd_1468083 < baseStart_1468083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468103 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 2, 5]
def baseStart_1468103 : Nat := 118140960795 + 1468103 * 2 ^ 59
def prefixEnd_1468103 : Nat := 4983230072969 + 3 ^ 40 * 1468103 * 2
def baseEnd_1468103 : Nat := 251280829769258257986941

theorem tailTrace_1468103 : CollatzResearch.WordTrace tailWord_1468103 prefixEnd_1468103 251280829769258257986941 := by
  unfold tailWord_1468103
  simp only [CollatzResearch.WordTrace]
  refine ⟨53546115400321037875712963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35697410266880691917141975 53546115400321037875712963)
  ·
    refine ⟨80319173100481556813569445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53546115400321037875712963 80319173100481556813569445)
    ·
      refine ⟨15059844956340291902544271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80319173100481556813569445 15059844956340291902544271)
      ·
        refine ⟨22589767434510437853816407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15059844956340291902544271 22589767434510437853816407)
        ·
          refine ⟨33884651151765656780724611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22589767434510437853816407 33884651151765656780724611)
          ·
            refine ⟨50826976727648485171086917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33884651151765656780724611 50826976727648485171086917)
            ·
              refine ⟨9530058136434090969578797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50826976727648485171086917 9530058136434090969578797)
              ·
                refine ⟨3573771801162784113592049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9530058136434090969578797 3573771801162784113592049)
                ·
                  refine ⟨2680328850872088085194037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3573771801162784113592049 2680328850872088085194037)
                  ·
                    refine ⟨251280829769258257986941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2680328850872088085194037 251280829769258257986941)
                    ·
                      rfl

theorem cell23_1468103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_1468103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468103 prefixEnd_1468103 := by exact prefixLift 1468103
  have htrace : WordTrace (prefixWord ++ tailWord_1468103) baseStart_1468103 baseEnd_1468103 := by
    simpa [prefixWord, tailWord_1468103, baseEnd_1468103] using wordTrace_append hprefix tailTrace_1468103
  have hstable : (prefixWord ++ tailWord_1468103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468103).length < 2 ^ (prefixWord ++ tailWord_1468103).sum := by decide
  have hdescent : baseEnd_1468103 < baseStart_1468103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468124 : List Nat := [2, 2, 5, 1, 3, 1, 1, 1, 7]
def baseStart_1468124 : Nat := 118140960795 + 1468124 * 2 ^ 59
def prefixEnd_1468124 : Nat := 4983230072969 + 3 ^ 40 * 1468124 * 2
def baseEnd_1468124 : Nat := 83761474711279910199803

theorem tailTrace_1468124 : CollatzResearch.WordTrace tailWord_1468124 prefixEnd_1468124 83761474711279910199803 := by
  unfold tailWord_1468124
  simp only [CollatzResearch.WordTrace]
  refine ⟨26773440666622479231113713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35697920888829972308151617 26773440666622479231113713)
  ·
    refine ⟨20080080499966859423335285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26773440666622479231113713 20080080499966859423335285)
    ·
      refine ⟨1882507546871893070937683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20080080499966859423335285 1882507546871893070937683)
      ·
        refine ⟨2823761320307839606406525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882507546871893070937683 2823761320307839606406525)
        ·
          refine ⟨1058910495115439852402447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2823761320307839606406525 1058910495115439852402447)
          ·
            refine ⟨1588365742673159778603671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058910495115439852402447 1588365742673159778603671)
            ·
              refine ⟨2382548614009739667905507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588365742673159778603671 2382548614009739667905507)
              ·
                refine ⟨3573822921014609501858261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382548614009739667905507 3573822921014609501858261)
                ·
                  refine ⟨83761474711279910199803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3573822921014609501858261 83761474711279910199803)
                  ·
                    rfl

theorem cell23_1468124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_1468124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468124 prefixEnd_1468124 := by exact prefixLift 1468124
  have htrace : WordTrace (prefixWord ++ tailWord_1468124) baseStart_1468124 baseEnd_1468124 := by
    simpa [prefixWord, tailWord_1468124, baseEnd_1468124] using wordTrace_append hprefix tailTrace_1468124
  have hstable : (prefixWord ++ tailWord_1468124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468124).length < 2 ^ (prefixWord ++ tailWord_1468124).sum := by decide
  have hdescent : baseEnd_1468124 < baseStart_1468124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468135 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1468135 : Nat := 118140960795 + 1468135 * 2 ^ 59
def prefixEnd_1468135 : Nat := 4983230072969 + 3 ^ 40 * 1468135 * 2
def baseEnd_1468135 : Nat := 753858920688718648760677

theorem tailTrace_1468135 : CollatzResearch.WordTrace tailWord_1468135 prefixEnd_1468135 753858920688718648760677 := by
  unfold tailWord_1468135
  simp only [CollatzResearch.WordTrace]
  refine ⟨53547282536205107340877859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35698188357470071560585239 53547282536205107340877859)
  ·
    refine ⟨80320923804307661011316789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53547282536205107340877859 80320923804307661011316789)
    ·
      refine ⟨7530086606653843219810949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80320923804307661011316789 7530086606653843219810949)
      ·
        refine ⟨1411891238747595603714553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7530086606653843219810949 1411891238747595603714553)
        ·
          refine ⟨1058918429060696702785915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1411891238747595603714553 1058918429060696702785915)
          ·
            refine ⟨1588377643591045054178873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1058918429060696702785915 1588377643591045054178873)
            ·
              refine ⟨1191283232693283790634155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588377643591045054178873 1191283232693283790634155)
              ·
                refine ⟨1786924849039925685951233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191283232693283790634155 1786924849039925685951233)
                ·
                  refine ⟨1340193636779944264463425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1786924849039925685951233 1340193636779944264463425)
                  ·
                    refine ⟨1005145227584958198347569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340193636779944264463425 1005145227584958198347569)
                    ·
                      refine ⟨753858920688718648760677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005145227584958198347569 753858920688718648760677)
                      ·
                        rfl

theorem cell23_1468135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1468135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468135 prefixEnd_1468135 := by exact prefixLift 1468135
  have htrace : WordTrace (prefixWord ++ tailWord_1468135) baseStart_1468135 baseEnd_1468135 := by
    simpa [prefixWord, tailWord_1468135, baseEnd_1468135] using wordTrace_append hprefix tailTrace_1468135
  have hstable : (prefixWord ++ tailWord_1468135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468135).length < 2 ^ (prefixWord ++ tailWord_1468135).sum := by decide
  have hdescent : baseEnd_1468135 < baseStart_1468135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468140 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_1468140 : Nat := 118140960795 + 1468140 * 2 ^ 59
def prefixEnd_1468140 : Nat := 4983230072969 + 3 ^ 40 * 1468140 * 2
def baseEnd_1468140 : Nat := 753861488091991129198153

theorem tailTrace_1468140 : CollatzResearch.WordTrace tailWord_1468140 prefixEnd_1468140 753861488091991129198153 := by
  unfold tailWord_1468140
  simp only [CollatzResearch.WordTrace]
  refine ⟨26773732450593496597404937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35698309934124662129873249 26773732450593496597404937)
  ·
    refine ⟨20080299337945122448053703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26773732450593496597404937 20080299337945122448053703)
    ·
      refine ⟨30120449006917683672080555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20080299337945122448053703 30120449006917683672080555)
      ·
        refine ⟨45180673510376525508120833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30120449006917683672080555 45180673510376525508120833)
        ·
          refine ⟨33885505132782394131090625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45180673510376525508120833 33885505132782394131090625)
          ·
            refine ⟨25414128849586795598317969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33885505132782394131090625 25414128849586795598317969)
            ·
              refine ⟨19060596637190096698738477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25414128849586795598317969 19060596637190096698738477)
              ·
                refine ⟨7147723738946286262026929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19060596637190096698738477 7147723738946286262026929)
                ·
                  refine ⟨5360792804209714696520197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7147723738946286262026929 5360792804209714696520197)
                  ·
                    refine ⟨1005148650789321505597537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5360792804209714696520197 1005148650789321505597537)
                    ·
                      refine ⟨753861488091991129198153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005148650789321505597537 753861488091991129198153)
                      ·
                        rfl

theorem cell23_1468140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_1468140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468140 prefixEnd_1468140 := by exact prefixLift 1468140
  have htrace : WordTrace (prefixWord ++ tailWord_1468140) baseStart_1468140 baseEnd_1468140 := by
    simpa [prefixWord, tailWord_1468140, baseEnd_1468140] using wordTrace_append hprefix tailTrace_1468140
  have hstable : (prefixWord ++ tailWord_1468140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468140).length < 2 ^ (prefixWord ++ tailWord_1468140).sum := by decide
  have hdescent : baseEnd_1468140 < baseStart_1468140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468184 : List Nat := [2, 1, 2, 3, 1, 1, 6, 2, 1, 4]
def baseStart_1468184 : Nat := 118140960795 + 1468184 * 2 ^ 59
def prefixEnd_1468184 : Nat := 4983230072969 + 3 ^ 40 * 1468184 * 2
def baseEnd_1468184 : Nat := 251294693746929652349317

theorem tailTrace_1468184 : CollatzResearch.WordTrace tailWord_1468184 prefixEnd_1468184 251294693746929652349317 := by
  unfold tailWord_1468184
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774534856513794354705803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35699379808685059139607737 26774534856513794354705803)
  ·
    refine ⟨40161802284770691532058705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26774534856513794354705803 40161802284770691532058705)
    ·
      refine ⟨30121351713578018649044029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40161802284770691532058705 30121351713578018649044029)
      ·
        refine ⟨11295506892591756993391511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30121351713578018649044029 11295506892591756993391511)
        ·
          refine ⟨16943260338887635490087267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295506892591756993391511 16943260338887635490087267)
          ·
            refine ⟨25414890508331453235130901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16943260338887635490087267 25414890508331453235130901)
            ·
              refine ⟨1191322992578036870396761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25414890508331453235130901 1191322992578036870396761)
              ·
                refine ⟨893492244433527652797571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191322992578036870396761 893492244433527652797571)
                ·
                  refine ⟨1340238366650291479196357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893492244433527652797571 1340238366650291479196357)
                  ·
                    refine ⟨251294693746929652349317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1340238366650291479196357 251294693746929652349317)
                    ·
                      rfl

theorem cell23_1468184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_1468184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468184 prefixEnd_1468184 := by exact prefixLift 1468184
  have htrace : WordTrace (prefixWord ++ tailWord_1468184) baseStart_1468184 baseEnd_1468184 := by
    simpa [prefixWord, tailWord_1468184, baseEnd_1468184] using wordTrace_append hprefix tailTrace_1468184
  have hstable : (prefixWord ++ tailWord_1468184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468184).length < 2 ^ (prefixWord ++ tailWord_1468184).sum := by decide
  have hdescent : baseEnd_1468184 < baseStart_1468184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468210 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1468210 : Nat := 118140960795 + 1468210 * 2 ^ 59
def prefixEnd_1468210 : Nat := 4983230072969 + 3 ^ 40 * 1468210 * 2
def baseEnd_1468210 : Nat := 251299143912601951774277

theorem tailTrace_1468210 : CollatzResearch.WordTrace tailWord_1468210 prefixEnd_1468210 251299143912601951774277 := by
  unfold tailWord_1468210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13387504502733348787464521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35700012007288930099905389 13387504502733348787464521)
  ·
    refine ⟨10040628377050011590598391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13387504502733348787464521 10040628377050011590598391)
    ·
      refine ⟨15060942565575017385897587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040628377050011590598391 15060942565575017385897587)
      ·
        refine ⟨22591413848362526078846381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060942565575017385897587 22591413848362526078846381)
        ·
          refine ⟨8471780193135947279567393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22591413848362526078846381 8471780193135947279567393)
          ·
            refine ⟨6353835144851960459675545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8471780193135947279567393 6353835144851960459675545)
            ·
              refine ⟨4765376358638970344756659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6353835144851960459675545 4765376358638970344756659)
              ·
                refine ⟨7148064537958455517134989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4765376358638970344756659 7148064537958455517134989)
                ·
                  refine ⟨2680524201734420818925621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7148064537958455517134989 2680524201734420818925621)
                  ·
                    refine ⟨251299143912601951774277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2680524201734420818925621 251299143912601951774277)
                    ·
                      rfl

theorem cell23_1468210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1468210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468210 prefixEnd_1468210 := by exact prefixLift 1468210
  have htrace : WordTrace (prefixWord ++ tailWord_1468210) baseStart_1468210 baseEnd_1468210 := by
    simpa [prefixWord, tailWord_1468210, baseEnd_1468210] using wordTrace_append hprefix tailTrace_1468210
  have hstable : (prefixWord ++ tailWord_1468210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468210).length < 2 ^ (prefixWord ++ tailWord_1468210).sum := by decide
  have hdescent : baseEnd_1468210 < baseStart_1468210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468227 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 1, 5]
def baseStart_1468227 : Nat := 118140960795 + 1468227 * 2 ^ 59
def prefixEnd_1468227 : Nat := 4983230072969 + 3 ^ 40 * 1468227 * 2
def baseEnd_1468227 : Nat := 251302053636310762936751

theorem tailTrace_1468227 : CollatzResearch.WordTrace tailWord_1468227 prefixEnd_1468227 251302053636310762936751 := by
  unfold tailWord_1468227
  simp only [CollatzResearch.WordTrace]
  refine ⟨53550638051871807053226935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35700425367914538035484623 53550638051871807053226935)
  ·
    refine ⟨80325957077807710579840403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53550638051871807053226935 80325957077807710579840403)
    ·
      refine ⟨120488935616711565869760605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80325957077807710579840403 120488935616711565869760605)
      ·
        refine ⟨45183350856266837201160227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120488935616711565869760605 45183350856266837201160227)
        ·
          refine ⟨67775026284400255801740341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45183350856266837201160227 67775026284400255801740341)
          ·
            refine ⟨6353908714162523981413157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67775026284400255801740341 6353908714162523981413157)
            ·
              refine ⟨1191357883905473246514967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6353908714162523981413157 1191357883905473246514967)
              ·
                refine ⟨1787036825858209869772451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191357883905473246514967 1787036825858209869772451)
                ·
                  refine ⟨2680555238787314804658677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787036825858209869772451 2680555238787314804658677)
                  ·
                    refine ⟨251302053636310762936751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2680555238787314804658677 251302053636310762936751)
                    ·
                      rfl

theorem cell23_1468227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 5].length) (baseStart_1468227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468227 prefixEnd_1468227 := by exact prefixLift 1468227
  have htrace : WordTrace (prefixWord ++ tailWord_1468227) baseStart_1468227 baseEnd_1468227 := by
    simpa [prefixWord, tailWord_1468227, baseEnd_1468227] using wordTrace_append hprefix tailTrace_1468227
  have hstable : (prefixWord ++ tailWord_1468227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468227).length < 2 ^ (prefixWord ++ tailWord_1468227).sum := by decide
  have hdescent : baseEnd_1468227 < baseStart_1468227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468243 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_1468243 : Nat := 118140960795 + 1468243 * 2 ^ 59
def prefixEnd_1468243 : Nat := 4983230072969 + 3 ^ 40 * 1468243 * 2
def baseEnd_1468243 : Nat := 753914376599404226210179

theorem tailTrace_1468243 : CollatzResearch.WordTrace tailWord_1468243 prefixEnd_1468243 753914376599404226210179 := by
  unfold tailWord_1468243
  simp only [CollatzResearch.WordTrace]
  refine ⟨53551221619813841785809383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35700814413209227857206255 53551221619813841785809383)
  ·
    refine ⟨80326832429720762678714075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53551221619813841785809383 80326832429720762678714075)
    ·
      refine ⟨120490248644581144018071113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80326832429720762678714075 120490248644581144018071113)
      ·
        refine ⟨90367686483435858013553335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120490248644581144018071113 90367686483435858013553335)
        ·
          refine ⟨135551529725153787020330003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90367686483435858013553335 135551529725153787020330003)
          ·
            refine ⟨203327294587730680530495005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135551529725153787020330003 203327294587730680530495005)
            ·
              refine ⟨76247735470399005198935627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203327294587730680530495005 76247735470399005198935627)
              ·
                refine ⟨114371603205598507798403441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76247735470399005198935627 114371603205598507798403441)
                ·
                  refine ⟨85778702404198880848802581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114371603205598507798403441 85778702404198880848802581)
                  ·
                    refine ⟨4020876675196822539787621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85778702404198880848802581 4020876675196822539787621)
                    ·
                      refine ⟨753914376599404226210179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4020876675196822539787621 753914376599404226210179)
                      ·
                        rfl

theorem cell23_1468243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_1468243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468243 prefixEnd_1468243 := by exact prefixLift 1468243
  have htrace : WordTrace (prefixWord ++ tailWord_1468243) baseStart_1468243 baseEnd_1468243 := by
    simpa [prefixWord, tailWord_1468243, baseEnd_1468243] using wordTrace_append hprefix tailTrace_1468243
  have hstable : (prefixWord ++ tailWord_1468243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468243).length < 2 ^ (prefixWord ++ tailWord_1468243).sum := by decide
  have hdescent : baseEnd_1468243 < baseStart_1468243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468250 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_1468250 : Nat := 118140960795 + 1468250 * 2 ^ 59
def prefixEnd_1468250 : Nat := 4983230072969 + 3 ^ 40 * 1468250 * 2
def baseEnd_1468250 : Nat := 753917970963985698822647

theorem tailTrace_1468250 : CollatzResearch.WordTrace tailWord_1468250 prefixEnd_1468250 753917970963985698822647 := by
  unfold tailWord_1468250
  simp only [CollatzResearch.WordTrace]
  refine ⟨13387869232697120495328551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35700984620525654654209469 13387869232697120495328551)
  ·
    refine ⟨20081803849045680742992827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13387869232697120495328551 20081803849045680742992827)
    ·
      refine ⟨30122705773568521114489241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20081803849045680742992827 30122705773568521114489241)
      ·
        refine ⟨22592029330176390835866931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30122705773568521114489241 22592029330176390835866931)
        ·
          refine ⟨33888043995264586253800397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22592029330176390835866931 33888043995264586253800397)
          ·
            refine ⟨12708016498224219845175149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33888043995264586253800397 12708016498224219845175149)
            ·
              refine ⟨4765506186834082441940681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12708016498224219845175149 4765506186834082441940681)
              ·
                refine ⟨3574129640125561831455511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765506186834082441940681 3574129640125561831455511)
                ·
                  refine ⟨5361194460188342747183267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574129640125561831455511 5361194460188342747183267)
                  ·
                    refine ⟨8041791690282514120774901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5361194460188342747183267 8041791690282514120774901)
                    ·
                      refine ⟨753917970963985698822647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8041791690282514120774901 753917970963985698822647)
                      ·
                        rfl

theorem cell23_1468250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_1468250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468250 prefixEnd_1468250 := by exact prefixLift 1468250
  have htrace : WordTrace (prefixWord ++ tailWord_1468250) baseStart_1468250 baseEnd_1468250 := by
    simpa [prefixWord, tailWord_1468250, baseEnd_1468250] using wordTrace_append hprefix tailTrace_1468250
  have hstable : (prefixWord ++ tailWord_1468250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468250).length < 2 ^ (prefixWord ++ tailWord_1468250).sum := by decide
  have hdescent : baseEnd_1468250 < baseStart_1468250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468264 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1468264 : Nat := 118140960795 + 1468264 * 2 ^ 59
def prefixEnd_1468264 : Nat := 4983230072969 + 3 ^ 40 * 1468264 * 2
def baseEnd_1468264 : Nat := 753925159693148644047583

theorem tailTrace_1468264 : CollatzResearch.WordTrace tailWord_1468264 prefixEnd_1468264 753925159693148644047583 := by
  unfold tailWord_1468264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26775993776368881186161923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35701325035158508248215897 26775993776368881186161923)
  ·
    refine ⟨40163990664553321779242885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26775993776368881186161923 40163990664553321779242885)
    ·
      refine ⟨7530748249603747833608041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40163990664553321779242885 7530748249603747833608041)
      ·
        refine ⟨5648061187202810875206031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7530748249603747833608041 5648061187202810875206031)
        ·
          refine ⟨8472091780804216312809047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648061187202810875206031 8472091780804216312809047)
          ·
            refine ⟨12708137671206324469213571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472091780804216312809047 12708137671206324469213571)
            ·
              refine ⟨19062206506809486703820357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12708137671206324469213571 19062206506809486703820357)
              ·
                refine ⟨3574163720026778756966317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19062206506809486703820357 3574163720026778756966317)
                ·
                  refine ⟨1340311395010042033862369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3574163720026778756966317 1340311395010042033862369)
                  ·
                    refine ⟨1005233546257531525396777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340311395010042033862369 1005233546257531525396777)
                    ·
                      refine ⟨753925159693148644047583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005233546257531525396777 753925159693148644047583)
                      ·
                        rfl

theorem cell23_1468264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1468264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468264 prefixEnd_1468264 := by exact prefixLift 1468264
  have htrace : WordTrace (prefixWord ++ tailWord_1468264) baseStart_1468264 baseEnd_1468264 := by
    simpa [prefixWord, tailWord_1468264, baseEnd_1468264] using wordTrace_append hprefix tailTrace_1468264
  have hstable : (prefixWord ++ tailWord_1468264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468264).length < 2 ^ (prefixWord ++ tailWord_1468264).sum := by decide
  have hdescent : baseEnd_1468264 < baseStart_1468264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468283 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 9]
def baseStart_1468283 : Nat := 118140960795 + 1468283 * 2 ^ 59
def prefixEnd_1468283 : Nat := 4983230072969 + 3 ^ 40 * 1468283 * 2
def baseEnd_1468283 : Nat := 251311638608528023236665

theorem tailTrace_1468283 : CollatzResearch.WordTrace tailWord_1468283 prefixEnd_1468283 251311638608528023236665 := by
  unfold tailWord_1468283
  simp only [CollatzResearch.WordTrace]
  refine ⟨53552680539668928617265503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35701787026445952411510335 53552680539668928617265503)
  ·
    refine ⟨80329020809503392925898255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53552680539668928617265503 80329020809503392925898255)
    ·
      refine ⟨120493531214255089388847383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80329020809503392925898255 120493531214255089388847383)
      ·
        refine ⟨180740296821382634083271075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120493531214255089388847383 180740296821382634083271075)
        ·
          refine ⟨271110445232073951124906613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180740296821382634083271075 271110445232073951124906613)
          ·
            refine ⟨25416604240506932917959995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 271110445232073951124906613 25416604240506932917959995)
            ·
              refine ⟨38124906360760399376939993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25416604240506932917959995 38124906360760399376939993)
              ·
                refine ⟨28593679770570299532704995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38124906360760399376939993 28593679770570299532704995)
                ·
                  refine ⟨42890519655855449299057493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28593679770570299532704995 42890519655855449299057493)
                  ·
                    refine ⟨251311638608528023236665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42890519655855449299057493 251311638608528023236665)
                    ·
                      rfl

theorem cell23_1468283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_1468283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468283 prefixEnd_1468283 := by exact prefixLift 1468283
  have htrace : WordTrace (prefixWord ++ tailWord_1468283) baseStart_1468283 baseEnd_1468283 := by
    simpa [prefixWord, tailWord_1468283, baseEnd_1468283] using wordTrace_append hprefix tailTrace_1468283
  have hstable : (prefixWord ++ tailWord_1468283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468283).length < 2 ^ (prefixWord ++ tailWord_1468283).sum := by decide
  have hdescent : baseEnd_1468283 < baseStart_1468283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468297 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 3]
def baseStart_1468297 : Nat := 118140960795 + 1468297 * 2 ^ 59
def prefixEnd_1468297 : Nat := 4983230072969 + 3 ^ 40 * 1468297 * 2
def baseEnd_1468297 : Nat := 753942104554747014934931

theorem tailTrace_1468297 : CollatzResearch.WordTrace tailWord_1468297 prefixEnd_1468297 753942104554747014934931 := by
  unfold tailWord_1468297
  simp only [CollatzResearch.WordTrace]
  refine ⟨53553191161618209008275145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35702127441078806005516763 53553191161618209008275145)
  ·
    refine ⟨40164893371213656756206359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53553191161618209008275145 40164893371213656756206359)
    ·
      refine ⟨60247340056820485134309539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40164893371213656756206359 60247340056820485134309539)
      ·
        refine ⟨90371010085230727701464309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60247340056820485134309539 90371010085230727701464309)
        ·
          refine ⟨8472282195490380722012279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90371010085230727701464309 8472282195490380722012279)
          ·
            refine ⟨12708423293235571083018419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472282195490380722012279 12708423293235571083018419)
            ·
              refine ⟨19062634939853356624527629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12708423293235571083018419 19062634939853356624527629)
              ·
                refine ⟨7148488102445008734197861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19062634939853356624527629 7148488102445008734197861)
                ·
                  refine ⟨1340341519208439137662099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7148488102445008734197861 1340341519208439137662099)
                  ·
                    refine ⟨2010512278812658706493149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340341519208439137662099 2010512278812658706493149)
                    ·
                      refine ⟨753942104554747014934931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010512278812658706493149 753942104554747014934931)
                      ·
                        rfl

theorem cell23_1468297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 4, 1, 3].length) (baseStart_1468297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468297 prefixEnd_1468297 := by exact prefixLift 1468297
  have htrace : WordTrace (prefixWord ++ tailWord_1468297) baseStart_1468297 baseEnd_1468297 := by
    simpa [prefixWord, tailWord_1468297, baseEnd_1468297] using wordTrace_append hprefix tailTrace_1468297
  have hstable : (prefixWord ++ tailWord_1468297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468297).length < 2 ^ (prefixWord ++ tailWord_1468297).sum := by decide
  have hdescent : baseEnd_1468297 < baseStart_1468297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468298 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1468298 : Nat := 118140960795 + 1468298 * 2 ^ 59
def prefixEnd_1468298 : Nat := 4983230072969 + 3 ^ 40 * 1468298 * 2
def baseEnd_1468298 : Nat := 753942618035401511022427

theorem tailTrace_1468298 : CollatzResearch.WordTrace tailWord_1468298 prefixEnd_1468298 753942618035401511022427 := by
  unfold tailWord_1468298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13388306908653646544765387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35702151756409724119374365 13388306908653646544765387)
  ·
    refine ⟨20082460362980469817148081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13388306908653646544765387 20082460362980469817148081)
    ·
      refine ⟨15061845272235352362861061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20082460362980469817148081 15061845272235352362861061)
      ·
        refine ⟨2824095988544128568036449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15061845272235352362861061 2824095988544128568036449)
        ·
          refine ⟨2118071991408096426027337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2824095988544128568036449 2118071991408096426027337)
          ·
            refine ⟨1588553993556072319520503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2118071991408096426027337 1588553993556072319520503)
            ·
              refine ⟨2382830990334108479280755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588553993556072319520503 2382830990334108479280755)
              ·
                refine ⟨3574246485501162718921133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382830990334108479280755 3574246485501162718921133)
                ·
                  refine ⟨1340342432062936019595425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3574246485501162718921133 1340342432062936019595425)
                  ·
                    refine ⟨1005256824047202014696569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340342432062936019595425 1005256824047202014696569)
                    ·
                      refine ⟨753942618035401511022427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005256824047202014696569 753942618035401511022427)
                      ·
                        rfl

theorem cell23_1468298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1468298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468298 prefixEnd_1468298 := by exact prefixLift 1468298
  have htrace : WordTrace (prefixWord ++ tailWord_1468298) baseStart_1468298 baseEnd_1468298 := by
    simpa [prefixWord, tailWord_1468298, baseEnd_1468298] using wordTrace_append hprefix tailTrace_1468298
  have hstable : (prefixWord ++ tailWord_1468298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468298).length < 2 ^ (prefixWord ++ tailWord_1468298).sum := by decide
  have hdescent : baseEnd_1468298 < baseStart_1468298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468303 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_1468303 : Nat := 118140960795 + 1468303 * 2 ^ 59
def prefixEnd_1468303 : Nat := 4983230072969 + 3 ^ 40 * 1468303 * 2
def baseEnd_1468303 : Nat := 753945185438673991459903

theorem tailTrace_1468303 : CollatzResearch.WordTrace tailWord_1468303 prefixEnd_1468303 753945185438673991459903 := by
  unfold tailWord_1468303
  simp only [CollatzResearch.WordTrace]
  refine ⟨53553409999596472032993563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35702273333064314688662375 53553409999596472032993563)
  ·
    refine ⟨80330114999394708049490345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53553409999596472032993563 80330114999394708049490345)
    ·
      refine ⟨60247586249546031037117759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80330114999394708049490345 60247586249546031037117759)
      ·
        refine ⟨90371379374319046555676639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60247586249546031037117759 90371379374319046555676639)
        ·
          refine ⟨135557069061478569833514959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90371379374319046555676639 135557069061478569833514959)
          ·
            refine ⟨203335603592217854750272439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135557069061478569833514959 203335603592217854750272439)
            ·
              refine ⟨305003405388326782125408659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203335603592217854750272439 305003405388326782125408659)
              ·
                refine ⟨457505108082490173188112989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305003405388326782125408659 457505108082490173188112989)
                ·
                  refine ⟨171564415530933814945542371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457505108082490173188112989 171564415530933814945542371)
                  ·
                    refine ⟨257346623296400722418313557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171564415530933814945542371 257346623296400722418313557)
                    ·
                      refine ⟨753945185438673991459903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 257346623296400722418313557 753945185438673991459903)
                      ·
                        rfl

theorem cell23_1468303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_1468303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468303 prefixEnd_1468303 := by exact prefixLift 1468303
  have htrace : WordTrace (prefixWord ++ tailWord_1468303) baseStart_1468303 baseEnd_1468303 := by
    simpa [prefixWord, tailWord_1468303, baseEnd_1468303] using wordTrace_append hprefix tailTrace_1468303
  have hstable : (prefixWord ++ tailWord_1468303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468303).length < 2 ^ (prefixWord ++ tailWord_1468303).sum := by decide
  have hdescent : baseEnd_1468303 < baseStart_1468303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468324 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_1468324 : Nat := 118140960795 + 1468324 * 2 ^ 59
def prefixEnd_1468324 : Nat := 4983230072969 + 3 ^ 40 * 1468324 * 2
def baseEnd_1468324 : Nat := 753955968532418409297307

theorem tailTrace_1468324 : CollatzResearch.WordTrace tailWord_1468324 prefixEnd_1468324 753955968532418409297307 := by
  unfold tailWord_1468324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26777087966260196309754013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35702783955013595079672017 26777087966260196309754013)
  ·
    refine ⟨10041407987347573616157755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26777087966260196309754013 10041407987347573616157755)
    ·
      refine ⟨15062111981021360424236633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10041407987347573616157755 15062111981021360424236633)
      ·
        refine ⟨11296583985766020318177475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15062111981021360424236633 11296583985766020318177475)
        ·
          refine ⟨16944875978649030477266213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11296583985766020318177475 16944875978649030477266213)
          ·
            refine ⟨3177164245996693214487415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16944875978649030477266213 3177164245996693214487415)
            ·
              refine ⟨4765746368995039821731123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177164245996693214487415 4765746368995039821731123)
              ·
                refine ⟨7148619553492559732596685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4765746368995039821731123 7148619553492559732596685)
                ·
                  refine ⟨2680732332559709899723757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7148619553492559732596685 2680732332559709899723757)
                  ·
                    refine ⟨1005274624709891212396409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2680732332559709899723757 1005274624709891212396409)
                    ·
                      refine ⟨753955968532418409297307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005274624709891212396409 753955968532418409297307)
                      ·
                        rfl

theorem cell23_1468324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_1468324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468324 prefixEnd_1468324 := by exact prefixLift 1468324
  have htrace : WordTrace (prefixWord ++ tailWord_1468324) baseStart_1468324 baseEnd_1468324 := by
    simpa [prefixWord, tailWord_1468324, baseEnd_1468324] using wordTrace_append hprefix tailTrace_1468324
  have hstable : (prefixWord ++ tailWord_1468324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468324).length < 2 ^ (prefixWord ++ tailWord_1468324).sum := by decide
  have hdescent : baseEnd_1468324 < baseStart_1468324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468348 : List Nat := [2, 2, 2, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1468348 : Nat := 118140960795 + 1468348 * 2 ^ 59
def prefixEnd_1468348 : Nat := 4983230072969 + 3 ^ 40 * 1468348 * 2
def baseEnd_1468348 : Nat := 753968292068126315397197

theorem tailTrace_1468348 : CollatzResearch.WordTrace tailWord_1468348 prefixEnd_1468348 753968292068126315397197 := by
  unfold tailWord_1468348
  simp only [CollatzResearch.WordTrace]
  refine ⟨26777525642216722359190849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35703367522955629812254465 26777525642216722359190849)
  ·
    refine ⟨20083144231662541769393137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26777525642216722359190849 20083144231662541769393137)
    ·
      refine ⟨15062358173746906327044853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20083144231662541769393137 15062358173746906327044853)
      ·
        refine ⟨1412096078788772468160455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15062358173746906327044853 1412096078788772468160455)
        ·
          refine ⟨2118144118183158702240683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412096078788772468160455 2118144118183158702240683)
          ·
            refine ⟨3177216177274738053361025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118144118183158702240683 3177216177274738053361025)
            ·
              refine ⟨2382912132956053540020769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177216177274738053361025 2382912132956053540020769)
              ·
                refine ⟨1787184099717040155015577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382912132956053540020769 1787184099717040155015577)
                ·
                  refine ⟨1340388074787780116261683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787184099717040155015577 1340388074787780116261683)
                  ·
                    refine ⟨2010582112181670174392525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340388074787780116261683 2010582112181670174392525)
                    ·
                      refine ⟨753968292068126315397197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010582112181670174392525 753968292068126315397197)
                      ·
                        rfl

theorem cell23_1468348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1468348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468348 prefixEnd_1468348 := by exact prefixLift 1468348
  have htrace : WordTrace (prefixWord ++ tailWord_1468348) baseStart_1468348 baseEnd_1468348 := by
    simpa [prefixWord, tailWord_1468348, baseEnd_1468348] using wordTrace_append hprefix tailTrace_1468348
  have hstable : (prefixWord ++ tailWord_1468348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468348).length < 2 ^ (prefixWord ++ tailWord_1468348).sum := by decide
  have hdescent : baseEnd_1468348 < baseStart_1468348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468377 : List Nat := [1, 2, 1, 2, 6, 1, 1, 2, 7]
def baseStart_1468377 : Nat := 118140960795 + 1468377 * 2 ^ 59
def prefixEnd_1468377 : Nat := 4983230072969 + 3 ^ 40 * 1468377 * 2
def baseEnd_1468377 : Nat := 83775909223011855770507

theorem tailTrace_1468377 : CollatzResearch.WordTrace tailWord_1468377 prefixEnd_1468377 83775909223011855770507 := by
  unfold tailWord_1468377
  simp only [CollatzResearch.WordTrace]
  refine ⟨53556109001328382671187385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35704072667552255114124923 53556109001328382671187385)
  ·
    refine ⟨40167081750996287003390539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53556109001328382671187385 40167081750996287003390539)
    ·
      refine ⟨60250622626494430505085809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40167081750996287003390539 60250622626494430505085809)
      ·
        refine ⟨45187966969870822878814357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60250622626494430505085809 45187966969870822878814357)
        ·
          refine ⟨2118185951712694822444423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45187966969870822878814357 2118185951712694822444423)
          ·
            refine ⟨3177278927569042233666635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118185951712694822444423 3177278927569042233666635)
            ·
              refine ⟨4765918391353563350499953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177278927569042233666635 4765918391353563350499953)
              ·
                refine ⟨3574438793515172512874965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765918391353563350499953 3574438793515172512874965)
                ·
                  refine ⟨83775909223011855770507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3574438793515172512874965 83775909223011855770507)
                  ·
                    rfl

theorem cell23_1468377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 7].length) (baseStart_1468377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468377 prefixEnd_1468377 := by exact prefixLift 1468377
  have htrace : WordTrace (prefixWord ++ tailWord_1468377) baseStart_1468377 baseEnd_1468377 := by
    simpa [prefixWord, tailWord_1468377, baseEnd_1468377] using wordTrace_append hprefix tailTrace_1468377
  have hstable : (prefixWord ++ tailWord_1468377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468377).length < 2 ^ (prefixWord ++ tailWord_1468377).sum := by decide
  have hdescent : baseEnd_1468377 < baseStart_1468377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468394 : List Nat := [3, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_1468394 : Nat := 118140960795 + 1468394 * 2 ^ 59
def prefixEnd_1468394 : Nat := 4983230072969 + 3 ^ 40 * 1468394 * 2
def baseEnd_1468394 : Nat := 83776879130914792824665

theorem tailTrace_1468394 : CollatzResearch.WordTrace tailWord_1468394 prefixEnd_1468394 83776879130914792824665 := by
  unfold tailWord_1468394
  simp only [CollatzResearch.WordTrace]
  refine ⟨13389182260566698643639059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35704486028177863049704157 13389182260566698643639059)
  ·
    refine ⟨20083773390850047965458589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13389182260566698643639059 20083773390850047965458589)
    ·
      refine ⟨7531415021568767987046971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20083773390850047965458589 7531415021568767987046971)
      ·
        refine ⟨11297122532353151980570457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7531415021568767987046971 11297122532353151980570457)
        ·
          refine ⟨8472841899264863985427843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11297122532353151980570457 8472841899264863985427843)
          ·
            refine ⟨12709262848897295978141765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472841899264863985427843 12709262848897295978141765)
            ·
              refine ⟨2382986784168242995901581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12709262848897295978141765 2382986784168242995901581)
              ·
                refine ⟨893620044063091123463093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2382986784168242995901581 893620044063091123463093)
                ·
                  refine ⟨83776879130914792824665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 893620044063091123463093 83776879130914792824665)
                  ·
                    rfl

theorem cell23_1468394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_1468394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468394 prefixEnd_1468394 := by exact prefixLift 1468394
  have htrace : WordTrace (prefixWord ++ tailWord_1468394) baseStart_1468394 baseEnd_1468394 := by
    simpa [prefixWord, tailWord_1468394, baseEnd_1468394] using wordTrace_append hprefix tailTrace_1468394
  have hstable : (prefixWord ++ tailWord_1468394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468394).length < 2 ^ (prefixWord ++ tailWord_1468394).sum := by decide
  have hdescent : baseEnd_1468394 < baseStart_1468394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468400 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5]
def baseStart_1468400 : Nat := 118140960795 + 1468400 * 2 ^ 59
def prefixEnd_1468400 : Nat := 4983230072969 + 3 ^ 40 * 1468400 * 2
def baseEnd_1468400 : Nat := 753994993062160111946957

theorem tailTrace_1468400 : CollatzResearch.WordTrace tailWord_1468400 prefixEnd_1468400 753994993062160111946957 := by
  unfold tailWord_1468400
  simp only [CollatzResearch.WordTrace]
  refine ⟨26778473940122528799637327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35704631920163371732849769 26778473940122528799637327)
  ·
    refine ⟨40167710910183793199455991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26778473940122528799637327 40167710910183793199455991)
    ·
      refine ⟨60251566365275689799183987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40167710910183793199455991 60251566365275689799183987)
      ·
        refine ⟨90377349547913534698775981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60251566365275689799183987 90377349547913534698775981)
        ·
          refine ⟨33891506080467575512040993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90377349547913534698775981 33891506080467575512040993)
          ·
            refine ⟨25418629560350681634030745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33891506080467575512040993 25418629560350681634030745)
            ·
              refine ⟨19063972170263011225523059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25418629560350681634030745 19063972170263011225523059)
              ·
                refine ⟨28595958255394516838284589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19063972170263011225523059 28595958255394516838284589)
                ·
                  refine ⟨10723484345772943814356721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28595958255394516838284589 10723484345772943814356721)
                  ·
                    refine ⟨8042613259329707860767541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10723484345772943814356721 8042613259329707860767541)
                    ·
                      refine ⟨753994993062160111946957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8042613259329707860767541 753994993062160111946957)
                      ·
                        rfl

theorem cell23_1468400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_1468400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468400 prefixEnd_1468400 := by exact prefixLift 1468400
  have htrace : WordTrace (prefixWord ++ tailWord_1468400) baseStart_1468400 baseEnd_1468400 := by
    simpa [prefixWord, tailWord_1468400, baseEnd_1468400] using wordTrace_append hprefix tailTrace_1468400
  have hstable : (prefixWord ++ tailWord_1468400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468400).length < 2 ^ (prefixWord ++ tailWord_1468400).sum := by decide
  have hdescent : baseEnd_1468400 < baseStart_1468400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468447 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1468447 : Nat := 118140960795 + 1468447 * 2 ^ 59
def prefixEnd_1468447 : Nat := 4983230072969 + 3 ^ 40 * 1468447 * 2
def baseEnd_1468447 : Nat := 754019126652921428059241

theorem tailTrace_1468447 : CollatzResearch.WordTrace tailWord_1468447 prefixEnd_1468447 754019126652921428059241 := by
  unfold tailWord_1468447
  simp only [CollatzResearch.WordTrace]
  refine ⟨53558662111074784626235595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35705774740716523084157063 53558662111074784626235595)
  ·
    refine ⟨80337993166612176939353393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53558662111074784626235595 80337993166612176939353393)
    ·
      refine ⟨60253494874959132704515045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80337993166612176939353393 60253494874959132704515045)
      ·
        refine ⟨11297530289054837382096571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60253494874959132704515045 11297530289054837382096571)
        ·
          refine ⟨16946295433582256073144857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11297530289054837382096571 16946295433582256073144857)
          ·
            refine ⟨12709721575186692054858643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16946295433582256073144857 12709721575186692054858643)
            ·
              refine ⟨19064582362780038082287965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12709721575186692054858643 19064582362780038082287965)
              ·
                refine ⟨7149218386042514280857987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19064582362780038082287965 7149218386042514280857987)
                ·
                  refine ⟨10723827579063771421286981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149218386042514280857987 10723827579063771421286981)
                  ·
                    refine ⟨2010717671074457141491309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10723827579063771421286981 2010717671074457141491309)
                    ·
                      refine ⟨754019126652921428059241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010717671074457141491309 754019126652921428059241)
                      ·
                        rfl

theorem cell23_1468447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1468447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468447 prefixEnd_1468447 := by exact prefixLift 1468447
  have htrace : WordTrace (prefixWord ++ tailWord_1468447) baseStart_1468447 baseEnd_1468447 := by
    simpa [prefixWord, tailWord_1468447, baseEnd_1468447] using wordTrace_append hprefix tailTrace_1468447
  have hstable : (prefixWord ++ tailWord_1468447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468447).length < 2 ^ (prefixWord ++ tailWord_1468447).sum := by decide
  have hdescent : baseEnd_1468447 < baseStart_1468447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468464 : List Nat := [2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3]
def baseStart_1468464 : Nat := 118140960795 + 1468464 * 2 ^ 59
def prefixEnd_1468464 : Nat := 4983230072969 + 3 ^ 40 * 1468464 * 2
def baseEnd_1468464 : Nat := 754027855824047861546663

theorem tailTrace_1468464 : CollatzResearch.WordTrace tailWord_1468464 prefixEnd_1468464 754027855824047861546663 := by
  unfold tailWord_1468464
  simp only [CollatzResearch.WordTrace]
  refine ⟨26779641076006598264802223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35706188101342131019736297 26779641076006598264802223)
  ·
    refine ⟨40169461614009897397203335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26779641076006598264802223 40169461614009897397203335)
    ·
      refine ⟨60254192421014846095805003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40169461614009897397203335 60254192421014846095805003)
      ·
        refine ⟨90381288631522269143707505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60254192421014846095805003 90381288631522269143707505)
        ·
          refine ⟨67785966473641701857780629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90381288631522269143707505 67785966473641701857780629)
          ·
            refine ⟨3177467178451954774583467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67785966473641701857780629 3177467178451954774583467)
            ·
              refine ⟨4766200767677932161875201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177467178451954774583467 4766200767677932161875201)
              ·
                refine ⟨3574650575758449121406401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766200767677932161875201 3574650575758449121406401)
                ·
                  refine ⟨2680987931818836841054801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574650575758449121406401 2680987931818836841054801)
                  ·
                    refine ⟨2010740948864127630791101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2680987931818836841054801 2010740948864127630791101)
                    ·
                      refine ⟨754027855824047861546663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010740948864127630791101 754027855824047861546663)
                      ·
                        rfl

theorem cell23_1468464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_1468464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468464 prefixEnd_1468464 := by exact prefixLift 1468464
  have htrace : WordTrace (prefixWord ++ tailWord_1468464) baseStart_1468464 baseEnd_1468464 := by
    simpa [prefixWord, tailWord_1468464, baseEnd_1468464] using wordTrace_append hprefix tailTrace_1468464
  have hstable : (prefixWord ++ tailWord_1468464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468464).length < 2 ^ (prefixWord ++ tailWord_1468464).sum := by decide
  have hdescent : baseEnd_1468464 < baseStart_1468464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468522 : List Nat := [3, 1, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1468522 : Nat := 118140960795 + 1468522 * 2 ^ 59
def prefixEnd_1468522 : Nat := 4983230072969 + 3 ^ 40 * 1468522 * 2
def baseEnd_1468522 : Nat := 251352545900669544873799

theorem tailTrace_1468522 : CollatzResearch.WordTrace tailWord_1468522 prefixEnd_1468522 251352545900669544873799 := by
  unfold tailWord_1468522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390349396450768108803955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35707598390535381623477213 13390349396450768108803955)
  ·
    refine ⟨20085524094676152163205933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13390349396450768108803955 20085524094676152163205933)
    ·
      refine ⟨7532071535503557061202225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20085524094676152163205933 7532071535503557061202225)
      ·
        refine ⟨5649053651627667795901669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7532071535503557061202225 5649053651627667795901669)
        ·
          refine ⟨1059197559680187711731563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5649053651627667795901669 1059197559680187711731563)
          ·
            refine ⟨1588796339520281567597345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059197559680187711731563 1588796339520281567597345)
            ·
              refine ⟨1191597254640211175698009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1588796339520281567597345 1191597254640211175698009)
              ·
                refine ⟨893697940980158381773507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191597254640211175698009 893697940980158381773507)
                ·
                  refine ⟨1340546911470237572660261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893697940980158381773507 1340546911470237572660261)
                  ·
                    refine ⟨251352545900669544873799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1340546911470237572660261 251352545900669544873799)
                    ·
                      rfl

theorem cell23_1468522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1468522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468522 prefixEnd_1468522 := by exact prefixLift 1468522
  have htrace : WordTrace (prefixWord ++ tailWord_1468522) baseStart_1468522 baseEnd_1468522 := by
    simpa [prefixWord, tailWord_1468522, baseEnd_1468522] using wordTrace_append hprefix tailTrace_1468522
  have hstable : (prefixWord ++ tailWord_1468522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468522).length < 2 ^ (prefixWord ++ tailWord_1468522).sum := by decide
  have hdescent : baseEnd_1468522 < baseStart_1468522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468528 : List Nat := [2, 1, 1, 1, 5, 3, 1, 4, 1, 1, 3]
def baseStart_1468528 : Nat := 118140960795 + 1468528 * 2 ^ 59
def prefixEnd_1468528 : Nat := 4983230072969 + 3 ^ 40 * 1468528 * 2
def baseEnd_1468528 : Nat := 754060718585935611146369

theorem tailTrace_1468528 : CollatzResearch.WordTrace tailWord_1468528 prefixEnd_1468528 754060718585935611146369 := by
  unfold tailWord_1468528
  simp only [CollatzResearch.WordTrace]
  refine ⟨26780808211890667729967119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35707744282520890306622825 26780808211890667729967119)
  ·
    refine ⟨40171212317836001594950679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26780808211890667729967119 40171212317836001594950679)
    ·
      refine ⟨60256818476754002392426019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40171212317836001594950679 60256818476754002392426019)
      ·
        refine ⟨90385227715131003588639029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60256818476754002392426019 90385227715131003588639029)
        ·
          refine ⟨8473615098293531586434909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90385227715131003588639029 8473615098293531586434909)
          ·
            refine ⟨3177605661860074344913091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8473615098293531586434909 3177605661860074344913091)
            ·
              refine ⟨4766408492790111517369637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177605661860074344913091 4766408492790111517369637)
              ·
                refine ⟨893701592398145909506807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4766408492790111517369637 893701592398145909506807)
                ·
                  refine ⟨1340552388597218864260211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893701592398145909506807 1340552388597218864260211)
                  ·
                    refine ⟨2010828582895828296390317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340552388597218864260211 2010828582895828296390317)
                    ·
                      refine ⟨754060718585935611146369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010828582895828296390317 754060718585935611146369)
                      ·
                        rfl

theorem cell23_1468528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 4, 1, 1, 3].length) (baseStart_1468528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468528 prefixEnd_1468528 := by exact prefixLift 1468528
  have htrace : WordTrace (prefixWord ++ tailWord_1468528) baseStart_1468528 baseEnd_1468528 := by
    simpa [prefixWord, tailWord_1468528, baseEnd_1468528] using wordTrace_append hprefix tailTrace_1468528
  have hstable : (prefixWord ++ tailWord_1468528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468528).length < 2 ^ (prefixWord ++ tailWord_1468528).sum := by decide
  have hdescent : baseEnd_1468528 < baseStart_1468528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468551 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_1468551 : Nat := 118140960795 + 1468551 * 2 ^ 59
def prefixEnd_1468551 : Nat := 4983230072969 + 3 ^ 40 * 1468551 * 2
def baseEnd_1468551 : Nat := 754072528640989021158763

theorem tailTrace_1468551 : CollatzResearch.WordTrace tailWord_1468551 prefixEnd_1468551 754072528640989021158763 := by
  unfold tailWord_1468551
  simp only [CollatzResearch.WordTrace]
  refine ⟨53562455302698010388021507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35708303535132006925347671 53562455302698010388021507)
  ·
    refine ⟨80343682954047015582032261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53562455302698010388021507 80343682954047015582032261)
    ·
      refine ⟨15064440553883815421631049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80343682954047015582032261 15064440553883815421631049)
      ·
        refine ⟨11298330415412861566223287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15064440553883815421631049 11298330415412861566223287)
        ·
          refine ⟨16947495623119292349334931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298330415412861566223287 16947495623119292349334931)
          ·
            refine ⟨25421243434678938524002397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16947495623119292349334931 25421243434678938524002397)
            ·
              refine ⟨9532966288004601946500899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25421243434678938524002397 9532966288004601946500899)
              ·
                refine ⟨14299449432006902919751349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9532966288004601946500899 14299449432006902919751349)
                ·
                  refine ⟨1340573384250647148726689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14299449432006902919751349 1340573384250647148726689)
                  ·
                    refine ⟨1005430038187985361545017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340573384250647148726689 1005430038187985361545017)
                    ·
                      refine ⟨754072528640989021158763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005430038187985361545017 754072528640989021158763)
                      ·
                        rfl

theorem cell23_1468551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_1468551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468551 prefixEnd_1468551 := by exact prefixLift 1468551
  have htrace : WordTrace (prefixWord ++ tailWord_1468551) baseStart_1468551 baseEnd_1468551 := by
    simpa [prefixWord, tailWord_1468551, baseEnd_1468551] using wordTrace_append hprefix tailTrace_1468551
  have hstable : (prefixWord ++ tailWord_1468551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468551).length < 2 ^ (prefixWord ++ tailWord_1468551).sum := by decide
  have hdescent : baseEnd_1468551 < baseStart_1468551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468578 : List Nat := [3, 3, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1468578 : Nat := 118140960795 + 1468578 * 2 ^ 59
def prefixEnd_1468578 : Nat := 4983230072969 + 3 ^ 40 * 1468578 * 2
def baseEnd_1468578 : Nat := 251362130872886805173713

theorem tailTrace_1468578 : CollatzResearch.WordTrace tailWord_1468578 prefixEnd_1468578 251362130872886805173713 := by
  unfold tailWord_1468578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390860018400048499813597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35708960049066795999502925 13390860018400048499813597)
  ·
    refine ⟨5021572506900018187430099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13390860018400048499813597 5021572506900018187430099)
    ·
      refine ⟨7532358760350027281145149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5021572506900018187430099 7532358760350027281145149)
      ·
        refine ⟨2824634535131260230429431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7532358760350027281145149 2824634535131260230429431)
        ·
          refine ⟨4236951802696890345644147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824634535131260230429431 4236951802696890345644147)
          ·
            refine ⟨6355427704045335518466221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236951802696890345644147 6355427704045335518466221)
            ·
              refine ⟨2383285389017000819424833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6355427704045335518466221 2383285389017000819424833)
              ·
                refine ⟨1787464041762750614568625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383285389017000819424833 1787464041762750614568625)
                ·
                  refine ⟨1340598031322062960926469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787464041762750614568625 1340598031322062960926469)
                  ·
                    refine ⟨251362130872886805173713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1340598031322062960926469 251362130872886805173713)
                    ·
                      rfl

theorem cell23_1468578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1468578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468578 prefixEnd_1468578 := by exact prefixLift 1468578
  have htrace : WordTrace (prefixWord ++ tailWord_1468578) baseStart_1468578 baseEnd_1468578 := by
    simpa [prefixWord, tailWord_1468578, baseEnd_1468578] using wordTrace_append hprefix tailTrace_1468578
  have hstable : (prefixWord ++ tailWord_1468578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468578).length < 2 ^ (prefixWord ++ tailWord_1468578).sum := by decide
  have hdescent : baseEnd_1468578 < baseStart_1468578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468617 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 4, 6]
def baseStart_1468617 : Nat := 118140960795 + 1468617 * 2 ^ 59
def prefixEnd_1468617 : Nat := 4983230072969 + 3 ^ 40 * 1468617 * 2
def baseEnd_1468617 : Nat := 251368806121395254311153

theorem tailTrace_1468617 : CollatzResearch.WordTrace tailWord_1468617 prefixEnd_1468617 251368806121395254311153 := by
  unfold tailWord_1468617
  simp only [CollatzResearch.WordTrace]
  refine ⟨53564862520458903659924105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35709908346972602439949403 53564862520458903659924105)
  ·
    refine ⟨40173646890344177744943079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53564862520458903659924105 40173646890344177744943079)
    ·
      refine ⟨60260470335516266617414619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40173646890344177744943079 60260470335516266617414619)
      ·
        refine ⟨90390705503274399926121929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60260470335516266617414619 90390705503274399926121929)
        ·
          refine ⟨67793029127455799944591447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90390705503274399926121929 67793029127455799944591447)
          ·
            refine ⟨101689543691183699916887171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67793029127455799944591447 101689543691183699916887171)
            ·
              refine ⟨152534315536775549875330757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101689543691183699916887171 152534315536775549875330757)
              ·
                refine ⟨28600184163145415601624517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152534315536775549875330757 28600184163145415601624517)
                ·
                  refine ⟨5362534530589765425304597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28600184163145415601624517 5362534530589765425304597)
                  ·
                    refine ⟨251368806121395254311153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5362534530589765425304597 251368806121395254311153)
                    ·
                      rfl

theorem cell23_1468617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_1468617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468617 prefixEnd_1468617 := by exact prefixLift 1468617
  have htrace : WordTrace (prefixWord ++ tailWord_1468617) baseStart_1468617 baseEnd_1468617 := by
    simpa [prefixWord, tailWord_1468617, baseEnd_1468617] using wordTrace_append hprefix tailTrace_1468617
  have hstable : (prefixWord ++ tailWord_1468617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468617).length < 2 ^ (prefixWord ++ tailWord_1468617).sum := by decide
  have hdescent : baseEnd_1468617 < baseStart_1468617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468636 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1468636 : Nat := 118140960795 + 1468636 * 2 ^ 59
def prefixEnd_1468636 : Nat := 4983230072969 + 3 ^ 40 * 1468636 * 2
def baseEnd_1468636 : Nat := 754116174496621188595873

theorem tailTrace_1468636 : CollatzResearch.WordTrace tailWord_1468636 prefixEnd_1468636 754116174496621188595873 := by
  unfold tailWord_1468636
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782777753695034952432881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35710370338260046603243841 26782777753695034952432881)
  ·
    refine ⟨20087083315271276214324661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26782777753695034952432881 20087083315271276214324661)
    ·
      refine ⟨1883164060806682145092937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20087083315271276214324661 1883164060806682145092937)
      ·
        refine ⟨1412373045605011608819703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1883164060806682145092937 1412373045605011608819703)
        ·
          refine ⟨2118559568407517413229555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412373045605011608819703 2118559568407517413229555)
          ·
            refine ⟨3177839352611276119844333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118559568407517413229555 3177839352611276119844333)
            ·
              refine ⟨1191689757229228544941625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3177839352611276119844333 1191689757229228544941625)
              ·
                refine ⟨893767317921921408706219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1191689757229228544941625 893767317921921408706219)
                ·
                  refine ⟨1340650976882882113059329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 893767317921921408706219 1340650976882882113059329)
                  ·
                    refine ⟨1005488232662161584794497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1340650976882882113059329 1005488232662161584794497)
                    ·
                      refine ⟨754116174496621188595873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005488232662161584794497 754116174496621188595873)
                      ·
                        rfl

theorem cell23_1468636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1468636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468636 prefixEnd_1468636 := by exact prefixLift 1468636
  have htrace : WordTrace (prefixWord ++ tailWord_1468636) baseStart_1468636 baseEnd_1468636 := by
    simpa [prefixWord, tailWord_1468636, baseEnd_1468636] using wordTrace_append hprefix tailTrace_1468636
  have hstable : (prefixWord ++ tailWord_1468636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468636).length < 2 ^ (prefixWord ++ tailWord_1468636).sum := by decide
  have hdescent : baseEnd_1468636 < baseStart_1468636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468644 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_1468644 : Nat := 118140960795 + 1468644 * 2 ^ 59
def prefixEnd_1468644 : Nat := 4983230072969 + 3 ^ 40 * 1468644 * 2
def baseEnd_1468644 : Nat := 754120282341857157295835

theorem tailTrace_1468644 : CollatzResearch.WordTrace tailWord_1468644 prefixEnd_1468644 754120282341857157295835 := by
  unfold tailWord_1468644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782923645680543635578493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35710564860907391514104657 26782923645680543635578493)
  ·
    refine ⟨10043596367130203863341935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26782923645680543635578493 10043596367130203863341935)
    ·
      refine ⟨15065394550695305795012903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10043596367130203863341935 15065394550695305795012903)
      ·
        refine ⟨22598091826042958692519355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065394550695305795012903 22598091826042958692519355)
        ·
          refine ⟨33897137739064438038779033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22598091826042958692519355 33897137739064438038779033)
          ·
            refine ⟨25422853304298328529084275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33897137739064438038779033 25422853304298328529084275)
            ·
              refine ⟨38134279956447492793626413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25422853304298328529084275 38134279956447492793626413)
              ·
                refine ⟨14300354983667809797609905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38134279956447492793626413 14300354983667809797609905)
                ·
                  refine ⟨10725266237750857348207429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14300354983667809797609905 10725266237750857348207429)
                  ·
                    refine ⟨2010987419578285752788893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10725266237750857348207429 2010987419578285752788893)
                    ·
                      refine ⟨754120282341857157295835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2010987419578285752788893 754120282341857157295835)
                      ·
                        rfl

theorem cell23_1468644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_1468644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468644 prefixEnd_1468644 := by exact prefixLift 1468644
  have htrace : WordTrace (prefixWord ++ tailWord_1468644) baseStart_1468644 baseEnd_1468644 := by
    simpa [prefixWord, tailWord_1468644, baseEnd_1468644] using wordTrace_append hprefix tailTrace_1468644
  have hstable : (prefixWord ++ tailWord_1468644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468644).length < 2 ^ (prefixWord ++ tailWord_1468644).sum := by decide
  have hdescent : baseEnd_1468644 < baseStart_1468644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468654 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1468654 : Nat := 118140960795 + 1468654 * 2 ^ 59
def prefixEnd_1468654 : Nat := 4983230072969 + 3 ^ 40 * 1468654 * 2
def baseEnd_1468654 : Nat := 754125417148402118170789

theorem tailTrace_1468654 : CollatzResearch.WordTrace tailWord_1468654 prefixEnd_1468654 754125417148402118170789 := by
  unfold tailWord_1468654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6695776502665607372377627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35710808014216572652680677 6695776502665607372377627)
  ·
    refine ⟨10043664753998411058566441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6695776502665607372377627 10043664753998411058566441)
    ·
      refine ⟨7532748565498808293924831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10043664753998411058566441 7532748565498808293924831)
      ·
        refine ⟨11299122848248212440887247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7532748565498808293924831 11299122848248212440887247)
        ·
          refine ⟨16948684272372318661330871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11299122848248212440887247 16948684272372318661330871)
          ·
            refine ⟨25423026408558477991996307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948684272372318661330871 25423026408558477991996307)
            ·
              refine ⟨38134539612837716987994461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25423026408558477991996307 38134539612837716987994461)
              ·
                refine ⟨14300452354814143870497923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38134539612837716987994461 14300452354814143870497923)
                ·
                  refine ⟨21450678532221215805746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14300452354814143870497923 21450678532221215805746885)
                  ·
                    refine ⟨4022002224791477963577541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21450678532221215805746885 4022002224791477963577541)
                    ·
                      refine ⟨754125417148402118170789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4022002224791477963577541 754125417148402118170789)
                      ·
                        rfl

theorem cell23_1468654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1468654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468654 prefixEnd_1468654 := by exact prefixLift 1468654
  have htrace : WordTrace (prefixWord ++ tailWord_1468654) baseStart_1468654 baseEnd_1468654 := by
    simpa [prefixWord, tailWord_1468654, baseEnd_1468654] using wordTrace_append hprefix tailTrace_1468654
  have hstable : (prefixWord ++ tailWord_1468654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468654).length < 2 ^ (prefixWord ++ tailWord_1468654).sum := by decide
  have hdescent : baseEnd_1468654 < baseStart_1468654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468667 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_1468667 : Nat := 118140960795 + 1468667 * 2 ^ 59
def prefixEnd_1468667 : Nat := 4983230072969 + 3 ^ 40 * 1468667 * 2
def baseEnd_1468667 : Nat := 754132092396910567308229

theorem tailTrace_1468667 : CollatzResearch.WordTrace tailWord_1468667 prefixEnd_1468667 754132092396910567308229 := by
  unfold tailWord_1468667
  simp only [CollatzResearch.WordTrace]
  refine ⟨53566686170277762199244255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35711124113518508132829503 53566686170277762199244255)
  ·
    refine ⟨80350029255416643298866383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53566686170277762199244255 80350029255416643298866383)
    ·
      refine ⟨120525043883124964948299575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80350029255416643298866383 120525043883124964948299575)
      ·
        refine ⟨180787565824687447422449363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120525043883124964948299575 180787565824687447422449363)
        ·
          refine ⟨271181348737031171133674045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180787565824687447422449363 271181348737031171133674045)
          ·
            refine ⟨101693005776386689175127767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271181348737031171133674045 101693005776386689175127767)
            ·
              refine ⟨152539508664580033762691651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101693005776386689175127767 152539508664580033762691651)
              ·
                refine ⟨228809262996870050644037477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152539508664580033762691651 228809262996870050644037477)
                ·
                  refine ⟨42901736811913134495757027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228809262996870050644037477 42901736811913134495757027)
                  ·
                    refine ⟨64352605217869701743635541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42901736811913134495757027 64352605217869701743635541)
                    ·
                      refine ⟨754132092396910567308229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 64352605217869701743635541 754132092396910567308229)
                      ·
                        rfl

theorem cell23_1468667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_1468667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468667 prefixEnd_1468667 := by exact prefixLift 1468667
  have htrace : WordTrace (prefixWord ++ tailWord_1468667) baseStart_1468667 baseEnd_1468667 := by
    simpa [prefixWord, tailWord_1468667, baseEnd_1468667] using wordTrace_append hprefix tailTrace_1468667
  have hstable : (prefixWord ++ tailWord_1468667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468667).length < 2 ^ (prefixWord ++ tailWord_1468667).sum := by decide
  have hdescent : baseEnd_1468667 < baseStart_1468667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468698 : List Nat := [3, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_1468698 : Nat := 118140960795 + 1468698 * 2 ^ 59
def prefixEnd_1468698 : Nat := 4983230072969 + 3 ^ 40 * 1468698 * 2
def baseEnd_1468698 : Nat := 83794223366355549557843

theorem tailTrace_1468698 : CollatzResearch.WordTrace tailWord_1468698 prefixEnd_1468698 83794223366355549557843 := by
  unfold tailWord_1468698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391954208291363623405687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35711877888776969662415165 13391954208291363623405687)
  ·
    refine ⟨20087931312437045435108531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13391954208291363623405687 20087931312437045435108531)
    ·
      refine ⟨30131896968655568152662797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20087931312437045435108531 30131896968655568152662797)
      ·
        refine ⟨11299461363245838057248549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30131896968655568152662797 11299461363245838057248549)
        ·
          refine ⟨2118649005608594635734103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11299461363245838057248549 2118649005608594635734103)
          ·
            refine ⟨3177973508412891953601155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118649005608594635734103 3177973508412891953601155)
            ·
              refine ⟨4766960262619337930401733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177973508412891953601155 4766960262619337930401733)
              ·
                refine ⟨893805049241125861950325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4766960262619337930401733 893805049241125861950325)
                ·
                  refine ⟨83794223366355549557843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 893805049241125861950325 83794223366355549557843)
                  ·
                    rfl

theorem cell23_1468698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_1468698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468698 prefixEnd_1468698 := by exact prefixLift 1468698
  have htrace : WordTrace (prefixWord ++ tailWord_1468698) baseStart_1468698 baseEnd_1468698 := by
    simpa [prefixWord, tailWord_1468698, baseEnd_1468698] using wordTrace_append hprefix tailTrace_1468698
  have hstable : (prefixWord ++ tailWord_1468698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468698).length < 2 ^ (prefixWord ++ tailWord_1468698).sum := by decide
  have hdescent : baseEnd_1468698 < baseStart_1468698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468744 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1468744 : Nat := 118140960795 + 1468744 * 2 ^ 59
def prefixEnd_1468744 : Nat := 4983230072969 + 3 ^ 40 * 1468744 * 2
def baseEnd_1468744 : Nat := 754171630407306766045375

theorem tailTrace_1468744 : CollatzResearch.WordTrace tailWord_1468744 prefixEnd_1468744 754171630407306766045375 := by
  unfold tailWord_1468744
  simp only [CollatzResearch.WordTrace]
  refine ⟨26784747295499402174898643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35712996393999202899864857 26784747295499402174898643)
  ·
    refine ⟨40177120943249103262347965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26784747295499402174898643 40177120943249103262347965)
    ·
      refine ⟨15066420353718413723380487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40177120943249103262347965 15066420353718413723380487)
      ·
        refine ⟨22599630530577620585070731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15066420353718413723380487 22599630530577620585070731)
        ·
          refine ⟨33899445795866430877606097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22599630530577620585070731 33899445795866430877606097)
          ·
            refine ⟨25424584346899823158204573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33899445795866430877606097 25424584346899823158204573)
            ·
              refine ⟨9534219130087433684326715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25424584346899823158204573 9534219130087433684326715)
              ·
                refine ⟨14301328695131150526490073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534219130087433684326715 14301328695131150526490073)
                ·
                  refine ⟨10725996521348362894867555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301328695131150526490073 10725996521348362894867555)
                  ·
                    refine ⟨16088994782022544342301333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10725996521348362894867555 16088994782022544342301333)
                    ·
                      refine ⟨754171630407306766045375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16088994782022544342301333 754171630407306766045375)
                      ·
                        rfl

theorem cell23_1468744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1468744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468744 prefixEnd_1468744 := by exact prefixLift 1468744
  have htrace : WordTrace (prefixWord ++ tailWord_1468744) baseStart_1468744 baseEnd_1468744 := by
    simpa [prefixWord, tailWord_1468744, baseEnd_1468744] using wordTrace_append hprefix tailTrace_1468744
  have hstable : (prefixWord ++ tailWord_1468744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468744).length < 2 ^ (prefixWord ++ tailWord_1468744).sum := by decide
  have hdescent : baseEnd_1468744 < baseStart_1468744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468781 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1468781 : Nat := 118140960795 + 1468781 * 2 ^ 59
def prefixEnd_1468781 : Nat := 4983230072969 + 3 ^ 40 * 1468781 * 2
def baseEnd_1468781 : Nat := 754190629191523121282705

theorem tailTrace_1468781 : CollatzResearch.WordTrace tailWord_1468781 prefixEnd_1468781 754190629191523121282705 := by
  unfold tailWord_1468781
  simp only [CollatzResearch.WordTrace]
  refine ⟨53570844091864759668894197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35713896061243173112596131 53570844091864759668894197)
  ·
    refine ⟨5022266633612321218958831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53570844091864759668894197 5022266633612321218958831)
    ·
      refine ⟨7533399950418481828438247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5022266633612321218958831 7533399950418481828438247)
      ·
        refine ⟨11300099925627722742657371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533399950418481828438247 11300099925627722742657371)
        ·
          refine ⟨16950149888441584113986057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11300099925627722742657371 16950149888441584113986057)
          ·
            refine ⟨12712612416331188085489543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16950149888441584113986057 12712612416331188085489543)
            ·
              refine ⟨19068918624496782128234315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12712612416331188085489543 19068918624496782128234315)
              ·
                refine ⟨28603377936745173192351473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19068918624496782128234315 28603377936745173192351473)
                ·
                  refine ⟨21452533452558879894263605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28603377936745173192351473 21452533452558879894263605)
                  ·
                    refine ⟨2011175011177394990087213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21452533452558879894263605 2011175011177394990087213)
                    ·
                      refine ⟨754190629191523121282705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011175011177394990087213 754190629191523121282705)
                      ·
                        rfl

theorem cell23_1468781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1468781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468781 prefixEnd_1468781 := by exact prefixLift 1468781
  have htrace : WordTrace (prefixWord ++ tailWord_1468781) baseStart_1468781 baseEnd_1468781 := by
    simpa [prefixWord, tailWord_1468781, baseEnd_1468781] using wordTrace_append hprefix tailTrace_1468781
  have hstable : (prefixWord ++ tailWord_1468781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468781).length < 2 ^ (prefixWord ++ tailWord_1468781).sum := by decide
  have hdescent : baseEnd_1468781 < baseStart_1468781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468794 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_1468794 : Nat := 118140960795 + 1468794 * 2 ^ 59
def prefixEnd_1468794 : Nat := 4983230072969 + 3 ^ 40 * 1468794 * 2
def baseEnd_1468794 : Nat := 754197304440031570420145

theorem tailTrace_1468794 : CollatzResearch.WordTrace tailWord_1468794 prefixEnd_1468794 754197304440031570420145 := by
  unfold tailWord_1468794
  simp only [CollatzResearch.WordTrace]
  refine ⟨13392829560204415722279359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35714212160545108592744957 13392829560204415722279359)
  ·
    refine ⟨20089244340306623583419039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13392829560204415722279359 20089244340306623583419039)
    ·
      refine ⟨30133866510459935375128559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20089244340306623583419039 30133866510459935375128559)
      ·
        refine ⟨45200799765689903062692839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30133866510459935375128559 45200799765689903062692839)
        ·
          refine ⟨67801199648534854594039259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45200799765689903062692839 67801199648534854594039259)
          ·
            refine ⟨101701799472802281891058889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67801199648534854594039259 101701799472802281891058889)
            ·
              refine ⟨76276349604601711418294167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101701799472802281891058889 76276349604601711418294167)
              ·
                refine ⟨114414524406902567127441251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76276349604601711418294167 114414524406902567127441251)
                ·
                  refine ⟨171621786610353850691161877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114414524406902567127441251 171621786610353850691161877)
                  ·
                    refine ⟨8044771247360336751148213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 171621786610353850691161877 8044771247360336751148213)
                    ·
                      refine ⟨754197304440031570420145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8044771247360336751148213 754197304440031570420145)
                      ·
                        rfl

theorem cell23_1468794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_1468794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468794 prefixEnd_1468794 := by exact prefixLift 1468794
  have htrace : WordTrace (prefixWord ++ tailWord_1468794) baseStart_1468794 baseEnd_1468794 := by
    simpa [prefixWord, tailWord_1468794, baseEnd_1468794] using wordTrace_append hprefix tailTrace_1468794
  have hstable : (prefixWord ++ tailWord_1468794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468794).length < 2 ^ (prefixWord ++ tailWord_1468794).sum := by decide
  have hdescent : baseEnd_1468794 < baseStart_1468794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468802 : List Nat := [3, 4, 2, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1468802 : Nat := 118140960795 + 1468802 * 2 ^ 59
def prefixEnd_1468802 : Nat := 4983230072969 + 3 ^ 40 * 1468802 * 2
def baseEnd_1468802 : Nat := 754201412285267539120109

theorem tailTrace_1468802 : CollatzResearch.WordTrace tailWord_1468802 prefixEnd_1468802 754201412285267539120109 := by
  unfold tailWord_1468802
  simp only [CollatzResearch.WordTrace]
  refine ⟨13392902506197170063852165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35714406683192453503605773 13392902506197170063852165)
  ·
    refine ⟨2511169219911969386972281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13392902506197170063852165 2511169219911969386972281)
    ·
      refine ⟨1883376914933977040229211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2511169219911969386972281 1883376914933977040229211)
      ·
        refine ⟨2825065372400965560343817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883376914933977040229211 2825065372400965560343817)
        ·
          refine ⟨2118799029300724170257863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2825065372400965560343817 2118799029300724170257863)
          ·
            refine ⟨3178198543951086255386795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118799029300724170257863 3178198543951086255386795)
            ·
              refine ⟨4767297815926629383080193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178198543951086255386795 4767297815926629383080193)
              ·
                refine ⟨3575473361944972037310145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4767297815926629383080193 3575473361944972037310145)
                ·
                  refine ⟨2681605021458729027982609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3575473361944972037310145 2681605021458729027982609)
                  ·
                    refine ⟨2011203766094046770986957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681605021458729027982609 2011203766094046770986957)
                    ·
                      refine ⟨754201412285267539120109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011203766094046770986957 754201412285267539120109)
                      ·
                        rfl

theorem cell23_1468802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1468802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468802 prefixEnd_1468802 := by exact prefixLift 1468802
  have htrace : WordTrace (prefixWord ++ tailWord_1468802) baseStart_1468802 baseEnd_1468802 := by
    simpa [prefixWord, tailWord_1468802, baseEnd_1468802] using wordTrace_append hprefix tailTrace_1468802
  have hstable : (prefixWord ++ tailWord_1468802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468802).length < 2 ^ (prefixWord ++ tailWord_1468802).sum := by decide
  have hdescent : baseEnd_1468802 < baseStart_1468802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468821 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_1468821 : Nat := 118140960795 + 1468821 * 2 ^ 59
def prefixEnd_1468821 : Nat := 4983230072969 + 3 ^ 40 * 1468821 * 2
def baseEnd_1468821 : Nat := 754211168417702964782521

theorem tailTrace_1468821 : CollatzResearch.WordTrace tailWord_1468821 prefixEnd_1468821 754211168417702964782521 := by
  unfold tailWord_1468821
  simp only [CollatzResearch.WordTrace]
  refine ⟨53572303011719846500350317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35714868674479897666900211 53572303011719846500350317)
  ·
    refine ⟨20089613629394942437631369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53572303011719846500350317 20089613629394942437631369)
    ·
      refine ⟨15067210222046206828223527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20089613629394942437631369 15067210222046206828223527)
      ·
        refine ⟨22600815333069310242335291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15067210222046206828223527 22600815333069310242335291)
        ·
          refine ⟨33901222999603965363502937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22600815333069310242335291 33901222999603965363502937)
          ·
            refine ⟨25425917249702974022627203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33901222999603965363502937 25425917249702974022627203)
            ·
              refine ⟨38138875874554461033940805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25425917249702974022627203 38138875874554461033940805)
              ·
                refine ⟨7151039226478961443863901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38138875874554461033940805 7151039226478961443863901)
                ·
                  refine ⟨2681639709929610541448963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7151039226478961443863901 2681639709929610541448963)
                  ·
                    refine ⟨4022459564894415812173445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2681639709929610541448963 4022459564894415812173445)
                    ·
                      refine ⟨754211168417702964782521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4022459564894415812173445 754211168417702964782521)
                      ·
                        rfl

theorem cell23_1468821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_1468821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468821 prefixEnd_1468821 := by exact prefixLift 1468821
  have htrace : WordTrace (prefixWord ++ tailWord_1468821) baseStart_1468821 baseEnd_1468821 := by
    simpa [prefixWord, tailWord_1468821, baseEnd_1468821] using wordTrace_append hprefix tailTrace_1468821
  have hstable : (prefixWord ++ tailWord_1468821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468821).length < 2 ^ (prefixWord ++ tailWord_1468821).sum := by decide
  have hdescent : baseEnd_1468821 < baseStart_1468821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468831 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 1, 6]
def baseStart_1468831 : Nat := 118140960795 + 1468831 * 2 ^ 59
def prefixEnd_1468831 : Nat := 4983230072969 + 3 ^ 40 * 1468831 * 2
def baseEnd_1468831 : Nat := 251405434408082641885825

theorem tailTrace_1468831 : CollatzResearch.WordTrace tailWord_1468831 prefixEnd_1468831 251405434408082641885825 := by
  unfold tailWord_1468831
  simp only [CollatzResearch.WordTrace]
  refine ⟨53572667741683618208214347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35715111827789078805476231 53572667741683618208214347)
  ·
    refine ⟨80359001612525427312321521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53572667741683618208214347 80359001612525427312321521)
    ·
      refine ⟨60269251209394070484241141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80359001612525427312321521 60269251209394070484241141)
      ·
        refine ⟨5650242300880694107897607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60269251209394070484241141 5650242300880694107897607)
        ·
          refine ⟨8475363451321041161846411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650242300880694107897607 8475363451321041161846411)
          ·
            refine ⟨12713045176981561742769617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475363451321041161846411 12713045176981561742769617)
            ·
              refine ⟨9534783882736171307077213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12713045176981561742769617 9534783882736171307077213)
              ·
                refine ⟨3575543956026064240153955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9534783882736171307077213 3575543956026064240153955)
                ·
                  refine ⟨5363315934039096360230933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575543956026064240153955 5363315934039096360230933)
                  ·
                    refine ⟨251405434408082641885825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5363315934039096360230933 251405434408082641885825)
                    ·
                      rfl

theorem cell23_1468831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 6].length) (baseStart_1468831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468831 prefixEnd_1468831 := by exact prefixLift 1468831
  have htrace : WordTrace (prefixWord ++ tailWord_1468831) baseStart_1468831 baseEnd_1468831 := by
    simpa [prefixWord, tailWord_1468831, baseEnd_1468831] using wordTrace_append hprefix tailTrace_1468831
  have hstable : (prefixWord ++ tailWord_1468831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468831).length < 2 ^ (prefixWord ++ tailWord_1468831).sum := by decide
  have hdescent : baseEnd_1468831 < baseStart_1468831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468855 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 1, 1, 4]
def baseStart_1468855 : Nat := 118140960795 + 1468855 * 2 ^ 59
def prefixEnd_1468855 : Nat := 4983230072969 + 3 ^ 40 * 1468855 * 2
def baseEnd_1468855 : Nat := 754228626759955831757365

theorem tailTrace_1468855 : CollatzResearch.WordTrace tailWord_1468855 prefixEnd_1468855 754228626759955831757365 := by
  unfold tailWord_1468855
  simp only [CollatzResearch.WordTrace]
  refine ⟨53573543093596670307088019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35715695395731113538058679 53573543093596670307088019)
  ·
    refine ⟨80360314640395005460632029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53573543093596670307088019 80360314640395005460632029)
    ·
      refine ⟨30135117990148127047737011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80360314640395005460632029 30135117990148127047737011)
      ·
        refine ⟨45202676985222190571605517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30135117990148127047737011 45202676985222190571605517)
        ·
          refine ⟨16951003869458321464352069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45202676985222190571605517 16951003869458321464352069)
          ·
            refine ⟨3178313225523435274566013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16951003869458321464352069 3178313225523435274566013)
            ·
              refine ⟨1191867459571288227962255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3178313225523435274566013 1191867459571288227962255)
              ·
                refine ⟨1787801189356932341943383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191867459571288227962255 1787801189356932341943383)
                ·
                  refine ⟨2681701784035398512915075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787801189356932341943383 2681701784035398512915075)
                  ·
                    refine ⟨4022552676053097769372613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2681701784035398512915075 4022552676053097769372613)
                    ·
                      refine ⟨754228626759955831757365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4022552676053097769372613 754228626759955831757365)
                      ·
                        rfl

theorem cell23_1468855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_1468855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468855 prefixEnd_1468855 := by exact prefixLift 1468855
  have htrace : WordTrace (prefixWord ++ tailWord_1468855) baseStart_1468855 baseEnd_1468855 := by
    simpa [prefixWord, tailWord_1468855, baseEnd_1468855] using wordTrace_append hprefix tailTrace_1468855
  have hstable : (prefixWord ++ tailWord_1468855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468855).length < 2 ^ (prefixWord ++ tailWord_1468855).sum := by decide
  have hdescent : baseEnd_1468855 < baseStart_1468855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468858 : List Nat := [3, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_1468858 : Nat := 118140960795 + 1468858 * 2 ^ 59
def prefixEnd_1468858 : Nat := 4983230072969 + 3 ^ 40 * 1468858 * 2
def baseEnd_1468858 : Nat := 754230167201919320019851

theorem tailTrace_1468858 : CollatzResearch.WordTrace tailWord_1468858 prefixEnd_1468858 754230167201919320019851 := by
  unfold tailWord_1468858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13393413128146450454861807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35715768341723867879631485 13393413128146450454861807)
  ·
    refine ⟨20090119692219675682292711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13393413128146450454861807 20090119692219675682292711)
    ·
      refine ⟨30135179538329513523439067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090119692219675682292711 30135179538329513523439067)
      ·
        refine ⟨45202769307494270285158601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30135179538329513523439067 45202769307494270285158601)
        ·
          refine ⟨33902076980620702713868951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45202769307494270285158601 33902076980620702713868951)
          ·
            refine ⟨50853115470931054070803427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33902076980620702713868951 50853115470931054070803427)
            ·
              refine ⟨76279673206396581106205141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50853115470931054070803427 76279673206396581106205141)
              ·
                refine ⟨1787804840774919869676683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 76279673206396581106205141 1787804840774919869676683)
                ·
                  refine ⟨2681707261162379804515025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787804840774919869676683 2681707261162379804515025)
                  ·
                    refine ⟨2011280445871784853386269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681707261162379804515025 2011280445871784853386269)
                    ·
                      refine ⟨754230167201919320019851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011280445871784853386269 754230167201919320019851)
                      ·
                        rfl

theorem cell23_1468858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_1468858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468858 prefixEnd_1468858 := by exact prefixLift 1468858
  have htrace : WordTrace (prefixWord ++ tailWord_1468858) baseStart_1468858 baseEnd_1468858 := by
    simpa [prefixWord, tailWord_1468858, baseEnd_1468858] using wordTrace_append hprefix tailTrace_1468858
  have hstable : (prefixWord ++ tailWord_1468858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468858).length < 2 ^ (prefixWord ++ tailWord_1468858).sum := by decide
  have hdescent : baseEnd_1468858 < baseStart_1468858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468888 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1468888 : Nat := 118140960795 + 1468888 * 2 ^ 59
def prefixEnd_1468888 : Nat := 4983230072969 + 3 ^ 40 * 1468888 * 2
def baseEnd_1468888 : Nat := 754245571621554202644713

theorem tailTrace_1468888 : CollatzResearch.WordTrace tailWord_1468888 prefixEnd_1468888 754245571621554202644713 := by
  unfold tailWord_1468888
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787373351238558471519659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35716497801651411295359545 26787373351238558471519659)
  ·
    refine ⟨40181060026857837707279489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26787373351238558471519659 40181060026857837707279489)
    ·
      refine ⟨30135795020143378280459617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40181060026857837707279489 30135795020143378280459617)
      ·
        refine ⟨22601846265107533710344713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30135795020143378280459617 22601846265107533710344713)
        ·
          refine ⟨16951384698830650282758535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22601846265107533710344713 16951384698830650282758535)
          ·
            refine ⟨25427077048245975424137803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16951384698830650282758535 25427077048245975424137803)
            ·
              refine ⟨38140615572368963136206705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25427077048245975424137803 38140615572368963136206705)
              ·
                refine ⟨28605461679276722352155029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38140615572368963136206705 28605461679276722352155029)
                ·
                  refine ⟨1340881016216096360257267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28605461679276722352155029 1340881016216096360257267)
                  ·
                    refine ⟨2011321524324144540385901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1340881016216096360257267 2011321524324144540385901)
                    ·
                      refine ⟨754245571621554202644713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011321524324144540385901 754245571621554202644713)
                      ·
                        rfl

theorem cell23_1468888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1468888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468888 prefixEnd_1468888 := by exact prefixLift 1468888
  have htrace : WordTrace (prefixWord ++ tailWord_1468888) baseStart_1468888 baseEnd_1468888 := by
    simpa [prefixWord, tailWord_1468888, baseEnd_1468888] using wordTrace_append hprefix tailTrace_1468888
  have hstable : (prefixWord ++ tailWord_1468888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468888).length < 2 ^ (prefixWord ++ tailWord_1468888).sum := by decide
  have hdescent : baseEnd_1468888 < baseStart_1468888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468909 : List Nat := [1, 5, 1, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_1468909 : Nat := 118140960795 + 1468909 * 2 ^ 59
def prefixEnd_1468909 : Nat := 4983230072969 + 3 ^ 40 * 1468909 * 2
def baseEnd_1468909 : Nat := 754256354715298620482117

theorem tailTrace_1468909 : CollatzResearch.WordTrace tailWord_1468909 prefixEnd_1468909 754256354715298620482117 := by
  unfold tailWord_1468909
  simp only [CollatzResearch.WordTrace]
  refine ⟨53575512635401037529553781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35717008423600691686369187 53575512635401037529553781)
  ·
    refine ⟨5022704309568847268395667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53575512635401037529553781 5022704309568847268395667)
    ·
      refine ⟨7534056464353270902593501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5022704309568847268395667 7534056464353270902593501)
      ·
        refine ⟨2825271174132476588472563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7534056464353270902593501 2825271174132476588472563)
        ·
          refine ⟨4237906761198714882708845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825271174132476588472563 4237906761198714882708845)
          ·
            refine ⟨1589215035449518081015817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4237906761198714882708845 1589215035449518081015817)
            ·
              refine ⟨1191911276587138560761863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589215035449518081015817 1191911276587138560761863)
              ·
                refine ⟨1787866914880707841142795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191911276587138560761863 1787866914880707841142795)
                ·
                  refine ⟨2681800372321061761714193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787866914880707841142795 2681800372321061761714193)
                  ·
                    refine ⟨2011350279240796321285645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681800372321061761714193 2011350279240796321285645)
                    ·
                      refine ⟨754256354715298620482117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011350279240796321285645 754256354715298620482117)
                      ·
                        rfl

theorem cell23_1468909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_1468909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468909 prefixEnd_1468909 := by exact prefixLift 1468909
  have htrace : WordTrace (prefixWord ++ tailWord_1468909) baseStart_1468909 baseEnd_1468909 := by
    simpa [prefixWord, tailWord_1468909, baseEnd_1468909] using wordTrace_append hprefix tailTrace_1468909
  have hstable : (prefixWord ++ tailWord_1468909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468909).length < 2 ^ (prefixWord ++ tailWord_1468909).sum := by decide
  have hdescent : baseEnd_1468909 < baseStart_1468909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468915 : List Nat := [1, 1, 1, 2, 2, 2, 5, 3, 1, 3, 2]
def baseStart_1468915 : Nat := 118140960795 + 1468915 * 2 ^ 59
def prefixEnd_1468915 : Nat := 4983230072969 + 3 ^ 40 * 1468915 * 2
def baseEnd_1468915 : Nat := 754259435599225597007089

theorem tailTrace_1468915 : CollatzResearch.WordTrace tailWord_1468915 prefixEnd_1468915 754259435599225597007089 := by
  unfold tailWord_1468915
  simp only [CollatzResearch.WordTrace]
  refine ⟨53575731473379300554272199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35717154315586200369514799 53575731473379300554272199)
  ·
    refine ⟨80363597210068950831408299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53575731473379300554272199 80363597210068950831408299)
    ·
      refine ⟨120545395815103426247112449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80363597210068950831408299 120545395815103426247112449)
      ·
        refine ⟨90409046861327569685334337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120545395815103426247112449 90409046861327569685334337)
        ·
          refine ⟨67806785145995677264000753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90409046861327569685334337 67806785145995677264000753)
          ·
            refine ⟨50855088859496757948000565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67806785145995677264000753 50855088859496757948000565)
            ·
              refine ⟨4767664580577821057625053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50855088859496757948000565 4767664580577821057625053)
              ·
                refine ⟨1787874217716682896609395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767664580577821057625053 1787874217716682896609395)
                ·
                  refine ⟨2681811326575024344914093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787874217716682896609395 2681811326575024344914093)
                  ·
                    refine ⟨1005679247465634129342785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2681811326575024344914093 1005679247465634129342785)
                    ·
                      refine ⟨754259435599225597007089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005679247465634129342785 754259435599225597007089)
                      ·
                        rfl

theorem cell23_1468915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 3, 1, 3, 2].length) (baseStart_1468915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468915 prefixEnd_1468915 := by exact prefixLift 1468915
  have htrace : WordTrace (prefixWord ++ tailWord_1468915) baseStart_1468915 baseEnd_1468915 := by
    simpa [prefixWord, tailWord_1468915, baseEnd_1468915] using wordTrace_append hprefix tailTrace_1468915
  have hstable : (prefixWord ++ tailWord_1468915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468915).length < 2 ^ (prefixWord ++ tailWord_1468915).sum := by decide
  have hdescent : baseEnd_1468915 < baseStart_1468915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468921 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 2, 6]
def baseStart_1468921 : Nat := 118140960795 + 1468921 * 2 ^ 59
def prefixEnd_1468921 : Nat := 4983230072969 + 3 ^ 40 * 1468921 * 2
def baseEnd_1468921 : Nat := 251420838827717524510687

theorem tailTrace_1468921 : CollatzResearch.WordTrace tailWord_1468921 prefixEnd_1468921 251420838827717524510687 := by
  unfold tailWord_1468921
  simp only [CollatzResearch.WordTrace]
  refine ⟨53575950311357563578990617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35717300207571709052660411 53575950311357563578990617)
  ·
    refine ⟨40181962733518172684242963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53575950311357563578990617 40181962733518172684242963)
    ·
      refine ⟨60272944100277259026364445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40181962733518172684242963 60272944100277259026364445)
      ·
        refine ⟨22602354037603972134886667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60272944100277259026364445 22602354037603972134886667)
        ·
          refine ⟨33903531056405958202330001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22602354037603972134886667 33903531056405958202330001)
          ·
            refine ⟨25427648292304468651747501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33903531056405958202330001 25427648292304468651747501)
            ·
              refine ⟨9535368109614175744405313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25427648292304468651747501 9535368109614175744405313)
              ·
                refine ⟨7151526082210631808303985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9535368109614175744405313 7151526082210631808303985)
                ·
                  refine ⟨5363644561657973856227989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7151526082210631808303985 5363644561657973856227989)
                  ·
                    refine ⟨251420838827717524510687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5363644561657973856227989 251420838827717524510687)
                    ·
                      rfl

theorem cell23_1468921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_1468921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468921 prefixEnd_1468921 := by exact prefixLift 1468921
  have htrace : WordTrace (prefixWord ++ tailWord_1468921) baseStart_1468921 baseEnd_1468921 := by
    simpa [prefixWord, tailWord_1468921, baseEnd_1468921] using wordTrace_append hprefix tailTrace_1468921
  have hstable : (prefixWord ++ tailWord_1468921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468921).length < 2 ^ (prefixWord ++ tailWord_1468921).sum := by decide
  have hdescent : baseEnd_1468921 < baseStart_1468921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1468978 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_1468978 : Nat := 118140960795 + 1468978 * 2 ^ 59
def prefixEnd_1468978 : Nat := 4983230072969 + 3 ^ 40 * 1468978 * 2
def baseEnd_1468978 : Nat := 754291784880458850519299

theorem tailTrace_1468978 : CollatzResearch.WordTrace tailWord_1468978 prefixEnd_1468978 754291784880458850519299 := by
  unfold tailWord_1468978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13394507318037765578453897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35718686181434041542543725 13394507318037765578453897)
  ·
    refine ⟨10045880488528324183840423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13394507318037765578453897 10045880488528324183840423)
    ·
      refine ⟨15068820732792486275760635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045880488528324183840423 15068820732792486275760635)
      ·
        refine ⟨22603231099188729413640953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068820732792486275760635 22603231099188729413640953)
        ·
          refine ⟨16952423324391547060230715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22603231099188729413640953 16952423324391547060230715)
          ·
            refine ⟨25428634986587320590346073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16952423324391547060230715 25428634986587320590346073)
            ·
              refine ⟨19071476239940490442759555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25428634986587320590346073 19071476239940490442759555)
              ·
                refine ⟨28607214359910735664139333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19071476239940490442759555 28607214359910735664139333)
                ·
                  refine ⟨5363852692483262937026125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28607214359910735664139333 5363852692483262937026125)
                  ·
                    refine ⟨2011444759681223601384797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5363852692483262937026125 2011444759681223601384797)
                    ·
                      refine ⟨754291784880458850519299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011444759681223601384797 754291784880458850519299)
                      ·
                        rfl

theorem cell23_1468978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_1468978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1468978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1468978 prefixEnd_1468978 := by exact prefixLift 1468978
  have htrace : WordTrace (prefixWord ++ tailWord_1468978) baseStart_1468978 baseEnd_1468978 := by
    simpa [prefixWord, tailWord_1468978, baseEnd_1468978] using wordTrace_append hprefix tailTrace_1468978
  have hstable : (prefixWord ++ tailWord_1468978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1468978).length < 2 ^ (prefixWord ++ tailWord_1468978).sum := by decide
  have hdescent : baseEnd_1468978 < baseStart_1468978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1468978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469068 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1469068 : Nat := 118140960795 + 1469068 * 2 ^ 59
def prefixEnd_1469068 : Nat := 4983230072969 + 3 ^ 40 * 1469068 * 2
def baseEnd_1469068 : Nat := 754337998139363498393885

theorem tailTrace_1469068 : CollatzResearch.WordTrace tailWord_1469068 prefixEnd_1469068 754337998139363498393885 := by
  unfold tailWord_1469068
  simp only [CollatzResearch.WordTrace]
  refine ⟨26790655920912503842295929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35720874561216671789727905 26790655920912503842295929)
  ·
    refine ⟨20092991940684377881721947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26790655920912503842295929 20092991940684377881721947)
    ·
      refine ⟨30139487911026566822582921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20092991940684377881721947 30139487911026566822582921)
      ·
        refine ⟨22604615933269925116937191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30139487911026566822582921 22604615933269925116937191)
        ·
          refine ⟨33906923899904887675405787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22604615933269925116937191 33906923899904887675405787)
          ·
            refine ⟨50860385849857331513108681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33906923899904887675405787 50860385849857331513108681)
            ·
              refine ⟨38145289387392998634831511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50860385849857331513108681 38145289387392998634831511)
              ·
                refine ⟨57217934081089497952247267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38145289387392998634831511 57217934081089497952247267)
                ·
                  refine ⟨85826901121634246928370901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57217934081089497952247267 85826901121634246928370901)
                  ·
                    refine ⟨2011567995038302662383693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 85826901121634246928370901 2011567995038302662383693)
                    ·
                      refine ⟨754337998139363498393885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011567995038302662383693 754337998139363498393885)
                      ·
                        rfl

theorem cell23_1469068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1469068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469068 prefixEnd_1469068 := by exact prefixLift 1469068
  have htrace : WordTrace (prefixWord ++ tailWord_1469068) baseStart_1469068 baseEnd_1469068 := by
    simpa [prefixWord, tailWord_1469068, baseEnd_1469068] using wordTrace_append hprefix tailTrace_1469068
  have hstable : (prefixWord ++ tailWord_1469068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469068).length < 2 ^ (prefixWord ++ tailWord_1469068).sum := by decide
  have hdescent : baseEnd_1469068 < baseStart_1469068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469145 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_1469145 : Nat := 118140960795 + 1469145 * 2 ^ 59
def prefixEnd_1469145 : Nat := 4983230072969 + 3 ^ 40 * 1469145 * 2
def baseEnd_1469145 : Nat := 754377536149759697131031

theorem tailTrace_1469145 : CollatzResearch.WordTrace tailWord_1469145 prefixEnd_1469145 754377536149759697131031 := by
  unfold tailWord_1469145
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584120262546049835144889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35722746841697366556763259 53584120262546049835144889)
  ·
    refine ⟨40188090196909537376358667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53584120262546049835144889 40188090196909537376358667)
    ·
      refine ⟨60282135295364306064538001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40188090196909537376358667 60282135295364306064538001)
      ·
        refine ⟨45211601471523229548403501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60282135295364306064538001 45211601471523229548403501)
        ·
          refine ⟨16954350551821211080651313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45211601471523229548403501 16954350551821211080651313)
          ·
            refine ⟨12715762913865908310488485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16954350551821211080651313 12715762913865908310488485)
            ·
              refine ⟨2384205546349857808216591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12715762913865908310488485 2384205546349857808216591)
              ·
                refine ⟨3576308319524786712324887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384205546349857808216591 3576308319524786712324887)
                ·
                  refine ⟨5364462479287180068487331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576308319524786712324887 5364462479287180068487331)
                  ·
                    refine ⟨8046693718930770102730997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364462479287180068487331 8046693718930770102730997)
                    ·
                      refine ⟨754377536149759697131031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8046693718930770102730997 754377536149759697131031)
                      ·
                        rfl

theorem cell23_1469145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_1469145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469145 prefixEnd_1469145 := by exact prefixLift 1469145
  have htrace : WordTrace (prefixWord ++ tailWord_1469145) baseStart_1469145 baseEnd_1469145 := by
    simpa [prefixWord, tailWord_1469145, baseEnd_1469145] using wordTrace_append hprefix tailTrace_1469145
  have hstable : (prefixWord ++ tailWord_1469145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469145).length < 2 ^ (prefixWord ++ tailWord_1469145).sum := by decide
  have hdescent : baseEnd_1469145 < baseStart_1469145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469155 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1469155 : Nat := 118140960795 + 1469155 * 2 ^ 59
def prefixEnd_1469155 : Nat := 4983230072969 + 3 ^ 40 * 1469155 * 2
def baseEnd_1469155 : Nat := 754382670956304658005985

theorem tailTrace_1469155 : CollatzResearch.WordTrace tailWord_1469155 prefixEnd_1469155 754382670956304658005985 := by
  unfold tailWord_1469155
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584484992509821543008919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35722989995006547695339279 53584484992509821543008919)
  ·
    refine ⟨80376727488764732314513379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53584484992509821543008919 80376727488764732314513379)
    ·
      refine ⟨120565091233147098471770069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80376727488764732314513379 120565091233147098471770069)
      ·
        refine ⟨2825744325776885120432111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 120565091233147098471770069 2825744325776885120432111)
        ·
          refine ⟨4238616488665327680648167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825744325776885120432111 4238616488665327680648167)
          ·
            refine ⟨6357924732997991520972251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238616488665327680648167 6357924732997991520972251)
            ·
              refine ⟨9536887099496987281458377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357924732997991520972251 9536887099496987281458377)
              ·
                refine ⟨7152665324622740461093783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9536887099496987281458377 7152665324622740461093783)
                ·
                  refine ⟨10728997986934110691640675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7152665324622740461093783 10728997986934110691640675)
                  ·
                    refine ⟨16093496980401166037461013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10728997986934110691640675 16093496980401166037461013)
                    ·
                      refine ⟨754382670956304658005985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16093496980401166037461013 754382670956304658005985)
                      ·
                        rfl

theorem cell23_1469155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1469155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469155 prefixEnd_1469155 := by exact prefixLift 1469155
  have htrace : WordTrace (prefixWord ++ tailWord_1469155) baseStart_1469155 baseEnd_1469155 := by
    simpa [prefixWord, tailWord_1469155, baseEnd_1469155] using wordTrace_append hprefix tailTrace_1469155
  have hstable : (prefixWord ++ tailWord_1469155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469155).length < 2 ^ (prefixWord ++ tailWord_1469155).sum := by decide
  have hdescent : baseEnd_1469155 < baseStart_1469155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469165 : List Nat := [1, 5, 1, 2, 1, 1, 4, 8]
def baseStart_1469165 : Nat := 118140960795 + 1469165 * 2 ^ 59
def prefixEnd_1469165 : Nat := 4983230072969 + 3 ^ 40 * 1469165 * 2
def baseEnd_1469165 : Nat := 27940289102327763662257

theorem tailTrace_1469165 : CollatzResearch.WordTrace tailWord_1469165 prefixEnd_1469165 27940289102327763662257 := by
  unfold tailWord_1469165
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584849722473593250872949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35723233148315728833915299 53584849722473593250872949)
  ·
    refine ⟨5023579661481899367269339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53584849722473593250872949 5023579661481899367269339)
    ·
      refine ⟨7535369492222849050904009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5023579661481899367269339 7535369492222849050904009)
      ·
        refine ⟨5651527119167136788178007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7535369492222849050904009 5651527119167136788178007)
        ·
          refine ⟨8477290678750705182267011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5651527119167136788178007 8477290678750705182267011)
          ·
            refine ⟨12715936018126057773400517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477290678750705182267011 12715936018126057773400517)
            ·
              refine ⟨2384238003398635832512597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12715936018126057773400517 2384238003398635832512597)
              ·
                refine ⟨27940289102327763662257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2384238003398635832512597 27940289102327763662257)
                ·
                  rfl

theorem cell23_1469165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 8].length) (baseStart_1469165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469165 prefixEnd_1469165 := by exact prefixLift 1469165
  have htrace : WordTrace (prefixWord ++ tailWord_1469165) baseStart_1469165 baseEnd_1469165 := by
    simpa [prefixWord, tailWord_1469165, baseEnd_1469165] using wordTrace_append hprefix tailTrace_1469165
  have hstable : (prefixWord ++ tailWord_1469165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469165).length < 2 ^ (prefixWord ++ tailWord_1469165).sum := by decide
  have hdescent : baseEnd_1469165 < baseStart_1469165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469168 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6]
def baseStart_1469168 : Nat := 118140960795 + 1469168 * 2 ^ 59
def prefixEnd_1469168 : Nat := 4983230072969 + 3 ^ 40 * 1469168 * 2
def baseEnd_1469168 : Nat := 754389346204813107143425

theorem tailTrace_1469168 : CollatzResearch.WordTrace tailWord_1469168 prefixEnd_1469168 754389346204813107143425 := by
  unfold tailWord_1469168
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792479570731362381616079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35723306094308483175488105 26792479570731362381616079)
  ·
    refine ⟨40188719356097043572424119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26792479570731362381616079 40188719356097043572424119)
    ·
      refine ⟨60283079034145565358636179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40188719356097043572424119 60283079034145565358636179)
      ·
        refine ⟨90424618551218348037954269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60283079034145565358636179 90424618551218348037954269)
        ·
          refine ⟨33909231956706880514232851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90424618551218348037954269 33909231956706880514232851)
          ·
            refine ⟨50863847935060320771349277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33909231956706880514232851 50863847935060320771349277)
            ·
              refine ⟨19073942975647620289255979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50863847935060320771349277 19073942975647620289255979)
              ·
                refine ⟨28610914463471430433883969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19073942975647620289255979 28610914463471430433883969)
                ·
                  refine ⟨21458185847603572825412977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28610914463471430433883969 21458185847603572825412977)
                  ·
                    refine ⟨16093639385702679619059733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21458185847603572825412977 16093639385702679619059733)
                    ·
                      refine ⟨754389346204813107143425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16093639385702679619059733 754389346204813107143425)
                      ·
                        rfl

theorem cell23_1469168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_1469168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469168 prefixEnd_1469168 := by exact prefixLift 1469168
  have htrace : WordTrace (prefixWord ++ tailWord_1469168) baseStart_1469168 baseEnd_1469168 := by
    simpa [prefixWord, tailWord_1469168, baseEnd_1469168] using wordTrace_append hprefix tailTrace_1469168
  have hstable : (prefixWord ++ tailWord_1469168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469168).length < 2 ^ (prefixWord ++ tailWord_1469168).sum := by decide
  have hdescent : baseEnd_1469168 < baseStart_1469168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469173 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1469173 : Nat := 118140960795 + 1469173 * 2 ^ 59
def prefixEnd_1469173 : Nat := 4983230072969 + 3 ^ 40 * 1469173 * 2
def baseEnd_1469173 : Nat := 251463971202695195860301

theorem tailTrace_1469173 : CollatzResearch.WordTrace tailWord_1469173 prefixEnd_1469173 251463971202695195860301 := by
  unfold tailWord_1469173
  simp only [CollatzResearch.WordTrace]
  refine ⟨53585141506444610617164173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35723427670963073744776115 53585141506444610617164173)
  ·
    refine ⟨20094428064916728981436565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53585141506444610617164173 20094428064916728981436565)
    ·
      refine ⟨941926315542971671004839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20094428064916728981436565 941926315542971671004839)
      ·
        refine ⟨1412889473314457506507259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 941926315542971671004839 1412889473314457506507259)
        ·
          refine ⟨2119334209971686259760889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412889473314457506507259 2119334209971686259760889)
          ·
            refine ⟨1589500657478764694820667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119334209971686259760889 1589500657478764694820667)
            ·
              refine ⟨2384250986218147042231001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589500657478764694820667 2384250986218147042231001)
              ·
                refine ⟨1788188239663610281673251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384250986218147042231001 1788188239663610281673251)
                ·
                  refine ⟨2682282359495415422509877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788188239663610281673251 2682282359495415422509877)
                  ·
                    refine ⟨251463971202695195860301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2682282359495415422509877 251463971202695195860301)
                    ·
                      rfl

theorem cell23_1469173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1469173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469173 prefixEnd_1469173 := by exact prefixLift 1469173
  have htrace : WordTrace (prefixWord ++ tailWord_1469173) baseStart_1469173 baseEnd_1469173 := by
    simpa [prefixWord, tailWord_1469173, baseEnd_1469173] using wordTrace_append hprefix tailTrace_1469173
  have hstable : (prefixWord ++ tailWord_1469173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469173).length < 2 ^ (prefixWord ++ tailWord_1469173).sum := by decide
  have hdescent : baseEnd_1469173 < baseStart_1469173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469175 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_1469175 : Nat := 118140960795 + 1469175 * 2 ^ 59
def prefixEnd_1469175 : Nat := 4983230072969 + 3 ^ 40 * 1469175 * 2
def baseEnd_1469175 : Nat := 754392940569394579755893

theorem tailTrace_1469175 : CollatzResearch.WordTrace tailWord_1469175 prefixEnd_1469175 754392940569394579755893 := by
  unfold tailWord_1469175
  simp only [CollatzResearch.WordTrace]
  refine ⟨53585214452437364958736979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35723476301624909972491319 53585214452437364958736979)
  ·
    refine ⟨80377821678656047438105469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53585214452437364958736979 80377821678656047438105469)
    ·
      refine ⟨30141683129496017789289551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80377821678656047438105469 30141683129496017789289551)
      ·
        refine ⟨45212524694244026683934327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30141683129496017789289551 45212524694244026683934327)
        ·
          refine ⟨67818787041366040025901491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45212524694244026683934327 67818787041366040025901491)
          ·
            refine ⟨101728180562049060038852237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67818787041366040025901491 101728180562049060038852237)
            ·
              refine ⟨38148067710768397514569589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101728180562049060038852237 38148067710768397514569589)
              ·
                refine ⟨3576381347884537266990899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38148067710768397514569589 3576381347884537266990899)
                ·
                  refine ⟨5364572021826805900486349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576381347884537266990899 5364572021826805900486349)
                  ·
                    refine ⟨2011714508185052212682381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5364572021826805900486349 2011714508185052212682381)
                    ·
                      refine ⟨754392940569394579755893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011714508185052212682381 754392940569394579755893)
                      ·
                        rfl

theorem cell23_1469175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_1469175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469175 prefixEnd_1469175 := by exact prefixLift 1469175
  have htrace : WordTrace (prefixWord ++ tailWord_1469175) baseStart_1469175 baseEnd_1469175 := by
    simpa [prefixWord, tailWord_1469175, baseEnd_1469175] using wordTrace_append hprefix tailTrace_1469175
  have hstable : (prefixWord ++ tailWord_1469175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469175).length < 2 ^ (prefixWord ++ tailWord_1469175).sum := by decide
  have hdescent : baseEnd_1469175 < baseStart_1469175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469192 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1469192 : Nat := 118140960795 + 1469192 * 2 ^ 59
def prefixEnd_1469192 : Nat := 4983230072969 + 3 ^ 40 * 1469192 * 2
def baseEnd_1469192 : Nat := 754401669740521013243315

theorem tailTrace_1469192 : CollatzResearch.WordTrace tailWord_1469192 prefixEnd_1469192 754401669740521013243315 := by
  unfold tailWord_1469192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26792917246687888431052915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35723889662250517908070553 26792917246687888431052915)
  ·
    refine ⟨40189375870031832646579373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26792917246687888431052915 40189375870031832646579373)
    ·
      refine ⟨15071015951261937242467265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40189375870031832646579373 15071015951261937242467265)
      ·
        refine ⟨11303261963446452931850449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15071015951261937242467265 11303261963446452931850449)
        ·
          refine ⟨8477446472584839698887837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303261963446452931850449 8477446472584839698887837)
          ·
            refine ⟨3179042427219314887082939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8477446472584839698887837 3179042427219314887082939)
            ·
              refine ⟨4768563640828972330624409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179042427219314887082939 4768563640828972330624409)
              ·
                refine ⟨3576422730621729247968307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4768563640828972330624409 3576422730621729247968307)
                ·
                  refine ⟨5364634095932593871952461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576422730621729247968307 5364634095932593871952461)
                  ·
                    refine ⟨2011737785974722701982173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5364634095932593871952461 2011737785974722701982173)
                    ·
                      refine ⟨754401669740521013243315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011737785974722701982173 754401669740521013243315)
                      ·
                        rfl

theorem cell23_1469192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1469192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469192 prefixEnd_1469192 := by exact prefixLift 1469192
  have htrace : WordTrace (prefixWord ++ tailWord_1469192) baseStart_1469192 baseEnd_1469192 := by
    simpa [prefixWord, tailWord_1469192, baseEnd_1469192] using wordTrace_append hprefix tailTrace_1469192
  have hstable : (prefixWord ++ tailWord_1469192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469192).length < 2 ^ (prefixWord ++ tailWord_1469192).sum := by decide
  have hdescent : baseEnd_1469192 < baseStart_1469192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469215 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1469215 : Nat := 118140960795 + 1469215 * 2 ^ 59
def prefixEnd_1469215 : Nat := 4983230072969 + 3 ^ 40 * 1469215 * 2
def baseEnd_1469215 : Nat := 754413479795574423255709

theorem tailTrace_1469215 : CollatzResearch.WordTrace tailWord_1469215 prefixEnd_1469215 754413479795574423255709 := by
  unfold tailWord_1469215
  simp only [CollatzResearch.WordTrace]
  refine ⟨53586673372292451790193099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35724448914861634526795399 53586673372292451790193099)
  ·
    refine ⟨80380010058438677685289649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53586673372292451790193099 80380010058438677685289649)
    ·
      refine ⟨60285007543829008263967237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80380010058438677685289649 60285007543829008263967237)
      ·
        refine ⟨11303438914467939049493857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60285007543829008263967237 11303438914467939049493857)
        ·
          refine ⟨8477579185850954287120393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303438914467939049493857 8477579185850954287120393)
          ·
            refine ⟨6358184389388215715340295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8477579185850954287120393 6358184389388215715340295)
            ·
              refine ⟨9537276584082323573010443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6358184389388215715340295 9537276584082323573010443)
              ·
                refine ⟨14305914876123485359515665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9537276584082323573010443 14305914876123485359515665)
                ·
                  refine ⟨10729436157092614019636749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14305914876123485359515665 10729436157092614019636749)
                  ·
                    refine ⟨4023538558909730257363781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10729436157092614019636749 4023538558909730257363781)
                    ·
                      refine ⟨754413479795574423255709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4023538558909730257363781 754413479795574423255709)
                      ·
                        rfl

theorem cell23_1469215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1469215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469215 prefixEnd_1469215 := by exact prefixLift 1469215
  have htrace : WordTrace (prefixWord ++ tailWord_1469215) baseStart_1469215 baseEnd_1469215 := by
    simpa [prefixWord, tailWord_1469215, baseEnd_1469215] using wordTrace_append hprefix tailTrace_1469215
  have hstable : (prefixWord ++ tailWord_1469215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469215).length < 2 ^ (prefixWord ++ tailWord_1469215).sum := by decide
  have hdescent : baseEnd_1469215 < baseStart_1469215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469226 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_1469226 : Nat := 118140960795 + 1469226 * 2 ^ 59
def prefixEnd_1469226 : Nat := 4983230072969 + 3 ^ 40 * 1469226 * 2
def baseEnd_1469226 : Nat := 754419128082773880218159

theorem tailTrace_1469226 : CollatzResearch.WordTrace tailWord_1469226 prefixEnd_1469226 754419128082773880218159 := by
  unfold tailWord_1469226
  simp only [CollatzResearch.WordTrace]
  refine ⟨13396768643813150167210883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35724716383501733779229021 13396768643813150167210883)
  ·
    refine ⟨20095152965719725250816325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13396768643813150167210883 20095152965719725250816325)
    ·
      refine ⟨3767841181072448484528061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20095152965719725250816325 3767841181072448484528061)
      ·
        refine ⟨1412940442902168181698023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3767841181072448484528061 1412940442902168181698023)
        ·
          refine ⟨2119410664353252272547035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1412940442902168181698023 2119410664353252272547035)
          ·
            refine ⟨3179115996529878408820553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119410664353252272547035 3179115996529878408820553)
            ·
              refine ⟨2384336997397408806615415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179115996529878408820553 2384336997397408806615415)
              ·
                refine ⟨3576505496096113209923123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384336997397408806615415 3576505496096113209923123)
                ·
                  refine ⟨5364758244144169814884685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576505496096113209923123 5364758244144169814884685)
                  ·
                    refine ⟨2011784341554063680581757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5364758244144169814884685 2011784341554063680581757)
                    ·
                      refine ⟨754419128082773880218159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2011784341554063680581757 754419128082773880218159)
                      ·
                        rfl

theorem cell23_1469226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_1469226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469226 prefixEnd_1469226 := by exact prefixLift 1469226
  have htrace : WordTrace (prefixWord ++ tailWord_1469226) baseStart_1469226 baseEnd_1469226 := by
    simpa [prefixWord, tailWord_1469226, baseEnd_1469226] using wordTrace_append hprefix tailTrace_1469226
  have hstable : (prefixWord ++ tailWord_1469226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469226).length < 2 ^ (prefixWord ++ tailWord_1469226).sum := by decide
  have hdescent : baseEnd_1469226 < baseStart_1469226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469283 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 2, 2, 2]
def baseStart_1469283 : Nat := 118140960795 + 1469283 * 2 ^ 59
def prefixEnd_1469283 : Nat := 4983230072969 + 3 ^ 40 * 1469283 * 2
def baseEnd_1469283 : Nat := 754448396480080157205397

theorem tailTrace_1469283 : CollatzResearch.WordTrace tailWord_1469283 prefixEnd_1469283 754448396480080157205397 := by
  unfold tailWord_1469283
  simp only [CollatzResearch.WordTrace]
  refine ⟨53589153536046099403668503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35726102357364066269112335 53589153536046099403668503)
  ·
    refine ⟨80383730304069149105502755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53589153536046099403668503 80383730304069149105502755)
    ·
      refine ⟨120575595456103723658254133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80383730304069149105502755 120575595456103723658254133)
      ·
        refine ⟨11303962074009724092961325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120575595456103723658254133 11303962074009724092961325)
        ·
          refine ⟨4238985777753646534860497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11303962074009724092961325 4238985777753646534860497)
          ·
            refine ⟨3179239333315234901145373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238985777753646534860497 3179239333315234901145373)
            ·
              refine ⟨1192214749993213087929515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3179239333315234901145373 1192214749993213087929515)
              ·
                refine ⟨1788322124989819631894273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192214749993213087929515 1788322124989819631894273)
                ·
                  refine ⟨1341241593742364723920705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1788322124989819631894273 1341241593742364723920705)
                  ·
                    refine ⟨1005931195306773542940529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341241593742364723920705 1005931195306773542940529)
                    ·
                      refine ⟨754448396480080157205397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005931195306773542940529 754448396480080157205397)
                      ·
                        rfl

theorem cell23_1469283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_1469283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469283 prefixEnd_1469283 := by exact prefixLift 1469283
  have htrace : WordTrace (prefixWord ++ tailWord_1469283) baseStart_1469283 baseEnd_1469283 := by
    simpa [prefixWord, tailWord_1469283, baseEnd_1469283] using wordTrace_append hprefix tailTrace_1469283
  have hstable : (prefixWord ++ tailWord_1469283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469283).length < 2 ^ (prefixWord ++ tailWord_1469283).sum := by decide
  have hdescent : baseEnd_1469283 < baseStart_1469283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469285 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1469285 : Nat := 118140960795 + 1469285 * 2 ^ 59
def prefixEnd_1469285 : Nat := 4983230072969 + 3 ^ 40 * 1469285 * 2
def baseEnd_1469285 : Nat := 251483141147129716460129

theorem tailTrace_1469285 : CollatzResearch.WordTrace tailWord_1469285 prefixEnd_1469285 251483141147129716460129 := by
  unfold tailWord_1469285
  simp only [CollatzResearch.WordTrace]
  refine ⟨53589226482038853745241309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35726150988025902496827539 53589226482038853745241309)
  ·
    refine ⟨20095959930764570154465491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53589226482038853745241309 20095959930764570154465491)
    ·
      refine ⟨30143939896146855231698237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20095959930764570154465491 30143939896146855231698237)
      ·
        refine ⟨11303977461055070711886839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30143939896146855231698237 11303977461055070711886839)
        ·
          refine ⟨16955966191582606067830259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303977461055070711886839 16955966191582606067830259)
          ·
            refine ⟨25433949287373909101745389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16955966191582606067830259 25433949287373909101745389)
            ·
              refine ⟨9537730982765215913154521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25433949287373909101745389 9537730982765215913154521)
              ·
                refine ⟨7153298237073911934865891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9537730982765215913154521 7153298237073911934865891)
                ·
                  refine ⟨10729947355610867902298837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153298237073911934865891 10729947355610867902298837)
                  ·
                    refine ⟨251483141147129716460129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10729947355610867902298837 251483141147129716460129)
                    ·
                      rfl

theorem cell23_1469285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1469285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469285 prefixEnd_1469285 := by exact prefixLift 1469285
  have htrace : WordTrace (prefixWord ++ tailWord_1469285) baseStart_1469285 baseEnd_1469285 := by
    simpa [prefixWord, tailWord_1469285, baseEnd_1469285] using wordTrace_append hprefix tailTrace_1469285
  have hstable : (prefixWord ++ tailWord_1469285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469285).length < 2 ^ (prefixWord ++ tailWord_1469285).sum := by decide
  have hdescent : baseEnd_1469285 < baseStart_1469285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469334 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_1469334 : Nat := 118140960795 + 1469334 * 2 ^ 59
def prefixEnd_1469334 : Nat := 4983230072969 + 3 ^ 40 * 1469334 * 2
def baseEnd_1469334 : Nat := 754474583993459457667663

theorem tailTrace_1469334 : CollatzResearch.WordTrace tailWord_1469334 prefixEnd_1469334 754474583993459457667663 := by
  unfold tailWord_1469334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349438353678833444610941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35727342439240890075850037 3349438353678833444610941)
  ·
    refine ⟨1256039382629562541729103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3349438353678833444610941 1256039382629562541729103)
    ·
      refine ⟨1884059073944343812593655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256039382629562541729103 1884059073944343812593655)
      ·
        refine ⟨2826088610916515718890483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1884059073944343812593655 2826088610916515718890483)
        ·
          refine ⟨4239132916374773578335725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826088610916515718890483 4239132916374773578335725)
          ·
            refine ⟨1589674843640540091875897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4239132916374773578335725 1589674843640540091875897)
            ·
              refine ⟨1192256132730405068906923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1589674843640540091875897 1192256132730405068906923)
              ·
                refine ⟨1788384199095607603360385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192256132730405068906923 1788384199095607603360385)
                ·
                  refine ⟨1341288149321705702520289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1788384199095607603360385 1341288149321705702520289)
                  ·
                    refine ⟨1005966111991279276890217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341288149321705702520289 1005966111991279276890217)
                    ·
                      refine ⟨754474583993459457667663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1005966111991279276890217 754474583993459457667663)
                      ·
                        rfl

theorem cell23_1469334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_1469334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469334 prefixEnd_1469334 := by exact prefixLift 1469334
  have htrace : WordTrace (prefixWord ++ tailWord_1469334) baseStart_1469334 baseEnd_1469334 := by
    simpa [prefixWord, tailWord_1469334, baseEnd_1469334] using wordTrace_append hprefix tailTrace_1469334
  have hstable : (prefixWord ++ tailWord_1469334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469334).length < 2 ^ (prefixWord ++ tailWord_1469334).sum := by decide
  have hdescent : baseEnd_1469334 < baseStart_1469334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469385 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_1469385 : Nat := 118140960795 + 1469385 * 2 ^ 59
def prefixEnd_1469385 : Nat := 4983230072969 + 3 ^ 40 * 1469385 * 2
def baseEnd_1469385 : Nat := 754500771506838758129927

theorem tailTrace_1469385 : CollatzResearch.WordTrace tailWord_1469385 prefixEnd_1469385 754500771506838758129927 := by
  unfold tailWord_1469385
  simp only [CollatzResearch.WordTrace]
  refine ⟨53592873781676570823881609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35728582521117713882587739 53592873781676570823881609)
  ·
    refine ⟨40194655336257428117911207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53592873781676570823881609 40194655336257428117911207)
    ·
      refine ⟨60291983004386142176866811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40194655336257428117911207 60291983004386142176866811)
      ·
        refine ⟨90437974506579213265300217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60291983004386142176866811 90437974506579213265300217)
        ·
          refine ⟨67828480879934409948975163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90437974506579213265300217 67828480879934409948975163)
          ·
            refine ⟨101742721319901614923462745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67828480879934409948975163 101742721319901614923462745)
            ·
              refine ⟨76307040989926211192597059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101742721319901614923462745 76307040989926211192597059)
              ·
                refine ⟨114460561484889316788895589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76307040989926211192597059 114460561484889316788895589)
                ·
                  refine ⟨21461355278416746897917923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114460561484889316788895589 21461355278416746897917923)
                  ·
                    refine ⟨32192032917625120346876885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21461355278416746897917923 32192032917625120346876885)
                    ·
                      refine ⟨754500771506838758129927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32192032917625120346876885 754500771506838758129927)
                      ·
                        rfl

theorem cell23_1469385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_1469385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469385 prefixEnd_1469385 := by exact prefixLift 1469385
  have htrace : WordTrace (prefixWord ++ tailWord_1469385) baseStart_1469385 baseEnd_1469385 := by
    simpa [prefixWord, tailWord_1469385, baseEnd_1469385] using wordTrace_append hprefix tailTrace_1469385
  have hstable : (prefixWord ++ tailWord_1469385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469385).length < 2 ^ (prefixWord ++ tailWord_1469385).sum := by decide
  have hdescent : baseEnd_1469385 < baseStart_1469385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469416 : List Nat := [2, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_1469416 : Nat := 118140960795 + 1469416 * 2 ^ 59
def prefixEnd_1469416 : Nat := 4983230072969 + 3 ^ 40 * 1469416 * 2
def baseEnd_1469416 : Nat := 754516689407128136842285

theorem tailTrace_1469416 : CollatzResearch.WordTrace tailWord_1469416 prefixEnd_1469416 754516689407128136842285 := by
  unfold tailWord_1469416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797002222282131559130051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35729336296376175412173401 26797002222282131559130051)
  ·
    refine ⟨40195503333423197338695077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26797002222282131559130051 40195503333423197338695077)
    ·
      refine ⟨7536656875016849501005327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40195503333423197338695077 7536656875016849501005327)
      ·
        refine ⟨11304985312525274251507991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536656875016849501005327 11304985312525274251507991)
        ·
          refine ⟨16957477968787911377261987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11304985312525274251507991 16957477968787911377261987)
          ·
            refine ⟨25436216953181867065892981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16957477968787911377261987 25436216953181867065892981)
            ·
              refine ⟨2384645339360800037427467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25436216953181867065892981 2384645339360800037427467)
              ·
                refine ⟨3576968009041200056141201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384645339360800037427467 3576968009041200056141201)
                ·
                  refine ⟨2682726006780900042105901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3576968009041200056141201 2682726006780900042105901)
                  ·
                    refine ⟨1006022252542837515789713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2682726006780900042105901 1006022252542837515789713)
                    ·
                      refine ⟨754516689407128136842285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006022252542837515789713 754516689407128136842285)
                      ·
                        rfl

theorem cell23_1469416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_1469416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469416 prefixEnd_1469416 := by exact prefixLift 1469416
  have htrace : WordTrace (prefixWord ++ tailWord_1469416) baseStart_1469416 baseEnd_1469416 := by
    simpa [prefixWord, tailWord_1469416, baseEnd_1469416] using wordTrace_append hprefix tailTrace_1469416
  have hstable : (prefixWord ++ tailWord_1469416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469416).length < 2 ^ (prefixWord ++ tailWord_1469416).sum := by decide
  have hdescent : baseEnd_1469416 < baseStart_1469416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469423 : List Nat := [1, 1, 2, 1, 4, 4, 2, 3, 1, 1, 3]
def baseStart_1469423 : Nat := 118140960795 + 1469423 * 2 ^ 59
def prefixEnd_1469423 : Nat := 4983230072969 + 3 ^ 40 * 1469423 * 2
def baseEnd_1469423 : Nat := 754520283771709609454753

theorem tailTrace_1469423 : CollatzResearch.WordTrace tailWord_1469423 prefixEnd_1469423 754520283771709609454753 := by
  unfold tailWord_1469423
  simp only [CollatzResearch.WordTrace]
  refine ⟨53594259755538903313764923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35729506503692602209176615 53594259755538903313764923)
  ·
    refine ⟨80391389633308354970647385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53594259755538903313764923 80391389633308354970647385)
    ·
      refine ⟨60293542224981266227985539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80391389633308354970647385 60293542224981266227985539)
      ·
        refine ⟨90440313337471899341978309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60293542224981266227985539 90440313337471899341978309)
        ·
          refine ⟨16957558750775981126620933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90440313337471899341978309 16957558750775981126620933)
          ·
            refine ⟨3179542265770496461241425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16957558750775981126620933 3179542265770496461241425)
            ·
              refine ⟨2384656699327872345931069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179542265770496461241425 2384656699327872345931069)
              ·
                refine ⟨894246262247952129724151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2384656699327872345931069 894246262247952129724151)
                ·
                  refine ⟨1341369393371928194586227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894246262247952129724151 1341369393371928194586227)
                  ·
                    refine ⟨2012054090057892291879341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1341369393371928194586227 2012054090057892291879341)
                    ·
                      refine ⟨754520283771709609454753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012054090057892291879341 754520283771709609454753)
                      ·
                        rfl

theorem cell23_1469423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 3, 1, 1, 3].length) (baseStart_1469423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469423 prefixEnd_1469423 := by exact prefixLift 1469423
  have htrace : WordTrace (prefixWord ++ tailWord_1469423) baseStart_1469423 baseEnd_1469423 := by
    simpa [prefixWord, tailWord_1469423, baseEnd_1469423] using wordTrace_append hprefix tailTrace_1469423
  have hstable : (prefixWord ++ tailWord_1469423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469423).length < 2 ^ (prefixWord ++ tailWord_1469423).sum := by decide
  have hdescent : baseEnd_1469423 < baseStart_1469423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469432 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1469432 : Nat := 118140960795 + 1469432 * 2 ^ 59
def prefixEnd_1469432 : Nat := 4983230072969 + 3 ^ 40 * 1469432 * 2
def baseEnd_1469432 : Nat := 754524905097600074242211

theorem tailTrace_1469432 : CollatzResearch.WordTrace tailWord_1469432 prefixEnd_1469432 754524905097600074242211 := by
  unfold tailWord_1469432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26797294006253148925421275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35729725341670865233895033 26797294006253148925421275)
  ·
    refine ⟨40195941009379723388131913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26797294006253148925421275 40195941009379723388131913)
    ·
      refine ⟨30146955757034792541098935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40195941009379723388131913 30146955757034792541098935)
      ·
        refine ⟨45220433635552188811648403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30146955757034792541098935 45220433635552188811648403)
        ·
          refine ⟨67830650453328283217472605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45220433635552188811648403 67830650453328283217472605)
          ·
            refine ⟨25436493919998106206552227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67830650453328283217472605 25436493919998106206552227)
            ·
              refine ⟨38154740879997159309828341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25436493919998106206552227 38154740879997159309828341)
              ·
                refine ⟨3577006957499733685296407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38154740879997159309828341 3577006957499733685296407)
                ·
                  refine ⟨5365510436249600527944611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577006957499733685296407 5365510436249600527944611)
                  ·
                    refine ⟨8048265654374400791916917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365510436249600527944611 8048265654374400791916917)
                    ·
                      refine ⟨754524905097600074242211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8048265654374400791916917 754524905097600074242211)
                      ·
                        rfl

theorem cell23_1469432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1469432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469432 prefixEnd_1469432 := by exact prefixLift 1469432
  have htrace : WordTrace (prefixWord ++ tailWord_1469432) baseStart_1469432 baseEnd_1469432 := by
    simpa [prefixWord, tailWord_1469432, baseEnd_1469432] using wordTrace_append hprefix tailTrace_1469432
  have hstable : (prefixWord ++ tailWord_1469432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469432).length < 2 ^ (prefixWord ++ tailWord_1469432).sum := by decide
  have hdescent : baseEnd_1469432 < baseStart_1469432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469463 : List Nat := [1, 1, 3, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1469463 : Nat := 118140960795 + 1469463 * 2 ^ 59
def prefixEnd_1469463 : Nat := 4983230072969 + 3 ^ 40 * 1469463 * 2
def baseEnd_1469463 : Nat := 754540822997889452954569

theorem tailTrace_1469463 : CollatzResearch.WordTrace tailWord_1469463 prefixEnd_1469463 754540822997889452954569 := by
  unfold tailWord_1469463
  simp only [CollatzResearch.WordTrace]
  refine ⟨53595718675393990145221043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35730479116929326763480695 53595718675393990145221043)
  ·
    refine ⟨80393578013090985217831565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53595718675393990145221043 80393578013090985217831565)
    ·
      refine ⟨30147591754909119456686837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80393578013090985217831565 30147591754909119456686837)
      ·
        refine ⟨2826336727022729949064391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30147591754909119456686837 2826336727022729949064391)
        ·
          refine ⟨4239505090534094923596587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826336727022729949064391 4239505090534094923596587)
          ·
            refine ⟨6359257635801142385394881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239505090534094923596587 6359257635801142385394881)
            ·
              refine ⟨4769443226850856789046161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359257635801142385394881 4769443226850856789046161)
              ·
                refine ⟨3577082420138142591784621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769443226850856789046161 3577082420138142591784621)
                ·
                  refine ⟨1341405907551803471919233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3577082420138142591784621 1341405907551803471919233)
                  ·
                    refine ⟨1006054430663852603939425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341405907551803471919233 1006054430663852603939425)
                    ·
                      refine ⟨754540822997889452954569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006054430663852603939425 754540822997889452954569)
                      ·
                        rfl

theorem cell23_1469463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1469463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469463 prefixEnd_1469463 := by exact prefixLift 1469463
  have htrace : WordTrace (prefixWord ++ tailWord_1469463) baseStart_1469463 baseEnd_1469463 := by
    simpa [prefixWord, tailWord_1469463, baseEnd_1469463] using wordTrace_append hprefix tailTrace_1469463
  have hstable : (prefixWord ++ tailWord_1469463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469463).length < 2 ^ (prefixWord ++ tailWord_1469463).sum := by decide
  have hdescent : baseEnd_1469463 < baseStart_1469463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469466 : List Nat := [3, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_1469466 : Nat := 118140960795 + 1469466 * 2 ^ 59
def prefixEnd_1469466 : Nat := 4983230072969 + 3 ^ 40 * 1469466 * 2
def baseEnd_1469466 : Nat := 754542363439852941217055

theorem tailTrace_1469466 : CollatzResearch.WordTrace tailWord_1469466 prefixEnd_1469466 754542363439852941217055 := by
  unfold tailWord_1469466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398957023595780414395063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35730552062922081105053501 13398957023595780414395063)
  ·
    refine ⟨20098435535393670621592595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13398957023595780414395063 20098435535393670621592595)
    ·
      refine ⟨30147653303090505932388893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20098435535393670621592595 30147653303090505932388893)
      ·
        refine ⟨11305369988658939724645835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30147653303090505932388893 11305369988658939724645835)
        ·
          refine ⟨16958054982988409586968753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11305369988658939724645835 16958054982988409586968753)
          ·
            refine ⟨12718541237241307190226565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16958054982988409586968753 12718541237241307190226565)
            ·
              refine ⟨2384726481982745098167481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12718541237241307190226565 2384726481982745098167481)
              ·
                refine ⟨1788544861487058823625611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384726481982745098167481 1788544861487058823625611)
                ·
                  refine ⟨2682817292230588235438417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788544861487058823625611 2682817292230588235438417)
                  ·
                    refine ⟨2012112969172941176578813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682817292230588235438417 2012112969172941176578813)
                    ·
                      refine ⟨754542363439852941217055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012112969172941176578813 754542363439852941217055)
                      ·
                        rfl

theorem cell23_1469466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_1469466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469466 prefixEnd_1469466 := by exact prefixLift 1469466
  have htrace : WordTrace (prefixWord ++ tailWord_1469466) baseStart_1469466 baseEnd_1469466 := by
    simpa [prefixWord, tailWord_1469466, baseEnd_1469466] using wordTrace_append hprefix tailTrace_1469466
  have hstable : (prefixWord ++ tailWord_1469466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469466).length < 2 ^ (prefixWord ++ tailWord_1469466).sum := by decide
  have hdescent : baseEnd_1469466 < baseStart_1469466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469469 : List Nat := [1, 4, 2, 2, 3, 1, 1, 9]
def baseStart_1469469 : Nat := 118140960795 + 1469469 * 2 ^ 59
def prefixEnd_1469469 : Nat := 4983230072969 + 3 ^ 40 * 1469469 * 2
def baseEnd_1469469 : Nat := 27946070514141349239983

theorem tailTrace_1469469 : CollatzResearch.WordTrace tailWord_1469469 prefixEnd_1469469 27946070514141349239983 := by
  unfold tailWord_1469469
  simp only [CollatzResearch.WordTrace]
  refine ⟨53595937513372253169939461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35730625008914835446626307 53595937513372253169939461)
  ·
    refine ⟨10049238283757297469363649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53595937513372253169939461 10049238283757297469363649)
    ·
      refine ⟨7536928712817973102022737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10049238283757297469363649 7536928712817973102022737)
      ·
        refine ⟨5652696534613479826517053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7536928712817973102022737 5652696534613479826517053)
        ·
          refine ⟨2119761200480054934943895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5652696534613479826517053 2119761200480054934943895)
          ·
            refine ⟨3179641800720082402415843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119761200480054934943895 3179641800720082402415843)
            ·
              refine ⟨4769462701080123603623765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179641800720082402415843 4769462701080123603623765)
              ·
                refine ⟨27946070514141349239983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4769462701080123603623765 27946070514141349239983)
                ·
                  rfl

theorem cell23_1469469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 9].length) (baseStart_1469469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469469 prefixEnd_1469469 := by exact prefixLift 1469469
  have htrace : WordTrace (prefixWord ++ tailWord_1469469) baseStart_1469469 baseEnd_1469469 := by
    simpa [prefixWord, tailWord_1469469, baseEnd_1469469] using wordTrace_append hprefix tailTrace_1469469
  have hstable : (prefixWord ++ tailWord_1469469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469469).length < 2 ^ (prefixWord ++ tailWord_1469469).sum := by decide
  have hdescent : baseEnd_1469469 < baseStart_1469469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469496 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_1469496 : Nat := 118140960795 + 1469496 * 2 ^ 59
def prefixEnd_1469496 : Nat := 4983230072969 + 3 ^ 40 * 1469496 * 2
def baseEnd_1469496 : Nat := 754557767859487823841917

theorem tailTrace_1469496 : CollatzResearch.WordTrace tailWord_1469496 prefixEnd_1469496 754557767859487823841917 := by
  unfold tailWord_1469496
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798461142137218390586171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35731281522849624520781561 26798461142137218390586171)
  ·
    refine ⟨40197691713205827585879257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26798461142137218390586171 40197691713205827585879257)
    ·
      refine ⟨30148268784904370689409443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40197691713205827585879257 30148268784904370689409443)
      ·
        refine ⟨45222403177356556034114165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30148268784904370689409443 45222403177356556034114165)
        ·
          refine ⟨4239600297877177128198203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45222403177356556034114165 4239600297877177128198203)
          ·
            refine ⟨6359400446815765692297305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239600297877177128198203 6359400446815765692297305)
            ·
              refine ⟨4769550335111824269222979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359400446815765692297305 4769550335111824269222979)
              ·
                refine ⟨7154325502667736403834469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769550335111824269222979 7154325502667736403834469)
                ·
                  refine ⟨1341436031750200575718963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7154325502667736403834469 1341436031750200575718963)
                  ·
                    refine ⟨2012154047625300863578445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1341436031750200575718963 2012154047625300863578445)
                    ·
                      refine ⟨754557767859487823841917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012154047625300863578445 754557767859487823841917)
                      ·
                        rfl

theorem cell23_1469496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_1469496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469496 prefixEnd_1469496 := by exact prefixLift 1469496
  have htrace : WordTrace (prefixWord ++ tailWord_1469496) baseStart_1469496 baseEnd_1469496 := by
    simpa [prefixWord, tailWord_1469496, baseEnd_1469496] using wordTrace_append hprefix tailTrace_1469496
  have hstable : (prefixWord ++ tailWord_1469496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469496).length < 2 ^ (prefixWord ++ tailWord_1469496).sum := by decide
  have hdescent : baseEnd_1469496 < baseStart_1469496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469497 : List Nat := [1, 2, 1, 5, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1469497 : Nat := 118140960795 + 1469497 * 2 ^ 59
def prefixEnd_1469497 : Nat := 4983230072969 + 3 ^ 40 * 1469497 * 2
def baseEnd_1469497 : Nat := 754558281340142319929413

theorem tailTrace_1469497 : CollatzResearch.WordTrace tailWord_1469497 prefixEnd_1469497 754558281340142319929413 := by
  unfold tailWord_1469497
  simp only [CollatzResearch.WordTrace]
  refine ⟨53596958757270813951958745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35731305838180542634639163 53596958757270813951958745)
  ·
    refine ⟨40197719067953110463969059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53596958757270813951958745 40197719067953110463969059)
    ·
      refine ⟨60296578601929665695953589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40197719067953110463969059 60296578601929665695953589)
      ·
        refine ⟨5652804243930906158995649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60296578601929665695953589 5652804243930906158995649)
        ·
          refine ⟨4239603182948179619246737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5652804243930906158995649 4239603182948179619246737)
          ·
            refine ⟨3179702387211134714435053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4239603182948179619246737 3179702387211134714435053)
            ·
              refine ⟨1192388395204175517913145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3179702387211134714435053 1192388395204175517913145)
              ·
                refine ⟨894291296403131638434859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192388395204175517913145 894291296403131638434859)
                ·
                  refine ⟨1341436944604697457652289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894291296403131638434859 1341436944604697457652289)
                  ·
                    refine ⟨1006077708453523093239217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341436944604697457652289 1006077708453523093239217)
                    ·
                      refine ⟨754558281340142319929413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006077708453523093239217 754558281340142319929413)
                      ·
                        rfl

theorem cell23_1469497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1469497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469497 prefixEnd_1469497 := by exact prefixLift 1469497
  have htrace : WordTrace (prefixWord ++ tailWord_1469497) baseStart_1469497 baseEnd_1469497 := by
    simpa [prefixWord, tailWord_1469497, baseEnd_1469497] using wordTrace_append hprefix tailTrace_1469497
  have hstable : (prefixWord ++ tailWord_1469497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469497).length < 2 ^ (prefixWord ++ tailWord_1469497).sum := by decide
  have hdescent : baseEnd_1469497 < baseStart_1469497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469512 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1469512 : Nat := 118140960795 + 1469512 * 2 ^ 59
def prefixEnd_1469512 : Nat := 4983230072969 + 3 ^ 40 * 1469512 * 2
def baseEnd_1469512 : Nat := 251521994516653253747281

theorem tailTrace_1469512 : CollatzResearch.WordTrace tailWord_1469512 prefixEnd_1469512 251521994516653253747281 := by
  unfold tailWord_1469512
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798752926108235756877395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35731670568144314342503193 26798752926108235756877395)
  ·
    refine ⟨40198129389162353635316093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26798752926108235756877395 40198129389162353635316093)
    ·
      refine ⟨15074298520935882613243535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40198129389162353635316093 15074298520935882613243535)
      ·
        refine ⟨22611447781403823919865303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15074298520935882613243535 22611447781403823919865303)
        ·
          refine ⟨33917171672105735879797955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22611447781403823919865303 33917171672105735879797955)
          ·
            refine ⟨50875757508158603819696933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33917171672105735879797955 50875757508158603819696933)
            ·
              refine ⟨9539204532779738216193175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50875757508158603819696933 9539204532779738216193175)
              ·
                refine ⟨14308806799169607324289763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9539204532779738216193175 14308806799169607324289763)
                ·
                  refine ⟨21463210198754410986434645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14308806799169607324289763 21463210198754410986434645)
                  ·
                    refine ⟨251521994516653253747281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21463210198754410986434645 251521994516653253747281)
                    ·
                      rfl

theorem cell23_1469512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1469512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469512 prefixEnd_1469512 := by exact prefixLift 1469512
  have htrace : WordTrace (prefixWord ++ tailWord_1469512) baseStart_1469512 baseEnd_1469512 := by
    simpa [prefixWord, tailWord_1469512, baseEnd_1469512] using wordTrace_append hprefix tailTrace_1469512
  have hstable : (prefixWord ++ tailWord_1469512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469512).length < 2 ^ (prefixWord ++ tailWord_1469512).sum := by decide
  have hdescent : baseEnd_1469512 < baseStart_1469512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469536 : List Nat := [2, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2]
def baseStart_1469536 : Nat := 118140960795 + 1469536 * 2 ^ 59
def prefixEnd_1469536 : Nat := 4983230072969 + 3 ^ 40 * 1469536 * 2
def baseEnd_1469536 : Nat := 754578307085667667341733

theorem tailTrace_1469536 : CollatzResearch.WordTrace tailWord_1469536 prefixEnd_1469536 754578307085667667341733 := by
  unfold tailWord_1469536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799190602064761806314231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35732254136086349075085641 26799190602064761806314231)
  ·
    refine ⟨40198785903097142709471347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799190602064761806314231 40198785903097142709471347)
    ·
      refine ⟨60298178854645714064207021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40198785903097142709471347 60298178854645714064207021)
      ·
        refine ⟨22611817070492142774077633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60298178854645714064207021 22611817070492142774077633)
        ·
          refine ⟨16958862802869107080558225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22611817070492142774077633 16958862802869107080558225)
          ·
            refine ⟨12719147102151830310418669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16958862802869107080558225 12719147102151830310418669)
            ·
              refine ⟨4769680163306936366407001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12719147102151830310418669 4769680163306936366407001)
              ·
                refine ⟨3577260122480202274805251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769680163306936366407001 3577260122480202274805251)
                ·
                  refine ⟨5365890183720303412207877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577260122480202274805251 5365890183720303412207877)
                  ·
                    refine ⟨1006104409447556889788977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5365890183720303412207877 1006104409447556889788977)
                    ·
                      refine ⟨754578307085667667341733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006104409447556889788977 754578307085667667341733)
                      ·
                        rfl

theorem cell23_1469536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_1469536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469536 prefixEnd_1469536 := by exact prefixLift 1469536
  have htrace : WordTrace (prefixWord ++ tailWord_1469536) baseStart_1469536 baseEnd_1469536 := by
    simpa [prefixWord, tailWord_1469536, baseEnd_1469536] using wordTrace_append hprefix tailTrace_1469536
  have hstable : (prefixWord ++ tailWord_1469536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469536).length < 2 ^ (prefixWord ++ tailWord_1469536).sum := by decide
  have hdescent : baseEnd_1469536 < baseStart_1469536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469576 : List Nat := [2, 1, 3, 4, 2, 1, 1, 2, 7]
def baseStart_1469576 : Nat := 118140960795 + 1469576 * 2 ^ 59
def prefixEnd_1469576 : Nat := 4983230072969 + 3 ^ 40 * 1469576 * 2
def baseEnd_1469576 : Nat := 83844316256871945649061

theorem tailTrace_1469576 : CollatzResearch.WordTrace tailWord_1469576 prefixEnd_1469576 83844316256871945649061 := by
  unfold tailWord_1469576
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799920061992305222042291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35733226749323073629389721 26799920061992305222042291)
  ·
    refine ⟨40199880092988457833063437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26799920061992305222042291 40199880092988457833063437)
    ·
      refine ⟨15074955034870671687398789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40199880092988457833063437 15074955034870671687398789)
      ·
        refine ⟨2826554069038250941387273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15074955034870671687398789 2826554069038250941387273)
        ·
          refine ⟨2119915551778688206040455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2826554069038250941387273 2119915551778688206040455)
          ·
            refine ⟨3179873327668032309060683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119915551778688206040455 3179873327668032309060683)
            ·
              refine ⟨4769809991502048463591025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179873327668032309060683 4769809991502048463591025)
              ·
                refine ⟨3577357493626536347693269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769809991502048463591025 3577357493626536347693269)
                ·
                  refine ⟨83844316256871945649061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3577357493626536347693269 83844316256871945649061)
                  ·
                    rfl

theorem cell23_1469576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_1469576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469576 prefixEnd_1469576 := by exact prefixLift 1469576
  have htrace : WordTrace (prefixWord ++ tailWord_1469576) baseStart_1469576 baseEnd_1469576 := by
    simpa [prefixWord, tailWord_1469576, baseEnd_1469576] using wordTrace_append hprefix tailTrace_1469576
  have hstable : (prefixWord ++ tailWord_1469576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469576).length < 2 ^ (prefixWord ++ tailWord_1469576).sum := by decide
  have hdescent : baseEnd_1469576 < baseStart_1469576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469589 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1469589 : Nat := 118140960795 + 1469589 * 2 ^ 59
def prefixEnd_1469589 : Nat := 4983230072969 + 3 ^ 40 * 1469589 * 2
def baseEnd_1469589 : Nat := 251535173853451986659663

theorem tailTrace_1469589 : CollatzResearch.WordTrace tailWord_1469589 prefixEnd_1469589 251535173853451986659663 := by
  unfold tailWord_1469589
  simp only [CollatzResearch.WordTrace]
  refine ⟨53600314272937513664307821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35733542848625009109538547 53600314272937513664307821)
  ·
    refine ⟨20100117852351567624115433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53600314272937513664307821 20100117852351567624115433)
    ·
      refine ⟨15075088389263675718086575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20100117852351567624115433 15075088389263675718086575)
      ·
        refine ⟨22612632583895513577129863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15075088389263675718086575 22612632583895513577129863)
        ·
          refine ⟨33918948875843270365694795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22612632583895513577129863 33918948875843270365694795)
          ·
            refine ⟨50878423313764905548542193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33918948875843270365694795 50878423313764905548542193)
            ·
              refine ⟨38158817485323679161406645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50878423313764905548542193 38158817485323679161406645)
              ·
                refine ⟨3577389139249094921381873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38158817485323679161406645 3577389139249094921381873)
                ·
                  refine ⟨2683041854436821191036405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577389139249094921381873 2683041854436821191036405)
                  ·
                    refine ⟨251535173853451986659663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2683041854436821191036405 251535173853451986659663)
                    ·
                      rfl

theorem cell23_1469589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1469589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469589 prefixEnd_1469589 := by exact prefixLift 1469589
  have htrace : WordTrace (prefixWord ++ tailWord_1469589) baseStart_1469589 baseEnd_1469589 := by
    simpa [prefixWord, tailWord_1469589, baseEnd_1469589] using wordTrace_append hprefix tailTrace_1469589
  have hstable : (prefixWord ++ tailWord_1469589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469589).length < 2 ^ (prefixWord ++ tailWord_1469589).sum := by decide
  have hdescent : baseEnd_1469589 < baseStart_1469589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469659 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3]
def baseStart_1469659 : Nat := 118140960795 + 1469659 * 2 ^ 59
def prefixEnd_1469659 : Nat := 4983230072969 + 3 ^ 40 * 1469659 * 2
def baseEnd_1469659 : Nat := 754641465206170686103667

theorem tailTrace_1469659 : CollatzResearch.WordTrace tailWord_1469659 prefixEnd_1469659 754641465206170686103667 := by
  unfold tailWord_1469659
  simp only [CollatzResearch.WordTrace]
  refine ⟨53602867382683915619356031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35735244921789277079570687 53602867382683915619356031)
  ·
    refine ⟨80404301074025873429034047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53602867382683915619356031 80404301074025873429034047)
    ·
      refine ⟨120606451611038810143551071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80404301074025873429034047 120606451611038810143551071)
      ·
        refine ⟨180909677416558215215326607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120606451611038810143551071 180909677416558215215326607)
        ·
          refine ⟨271364516124837322822989911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180909677416558215215326607 271364516124837322822989911)
          ·
            refine ⟨407046774187255984234484867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271364516124837322822989911 407046774187255984234484867)
            ·
              refine ⟨610570161280883976351727301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 407046774187255984234484867 610570161280883976351727301)
              ·
                refine ⟨114481905240165745565948869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 610570161280883976351727301 114481905240165745565948869)
                ·
                  refine ⟨21465357232531077293615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114481905240165745565948869 21465357232531077293615413)
                  ·
                    refine ⟨2012377240549788496276445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21465357232531077293615413 2012377240549788496276445)
                    ·
                      refine ⟨754641465206170686103667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012377240549788496276445 754641465206170686103667)
                      ·
                        rfl

theorem cell23_1469659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 5, 3].length) (baseStart_1469659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469659 prefixEnd_1469659 := by exact prefixLift 1469659
  have htrace : WordTrace (prefixWord ++ tailWord_1469659) baseStart_1469659 baseEnd_1469659 := by
    simpa [prefixWord, tailWord_1469659, baseEnd_1469659] using wordTrace_append hprefix tailTrace_1469659
  have hstable : (prefixWord ++ tailWord_1469659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469659).length < 2 ^ (prefixWord ++ tailWord_1469659).sum := by decide
  have hdescent : baseEnd_1469659 < baseStart_1469659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469683 : List Nat := [1, 1, 1, 2, 2, 7, 2, 1, 6]
def baseStart_1469683 : Nat := 118140960795 + 1469683 * 2 ^ 59
def prefixEnd_1469683 : Nat := 4983230072969 + 3 ^ 40 * 1469683 * 2
def baseEnd_1469683 : Nat := 83850420971319843578173

theorem tailTrace_1469683 : CollatzResearch.WordTrace tailWord_1469683 prefixEnd_1469683 83850420971319843578173 := by
  unfold tailWord_1469683
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603742734596967718229703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35735828489731311812153135 53603742734596967718229703)
  ·
    refine ⟨80405614101895451577344555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53603742734596967718229703 80405614101895451577344555)
    ·
      refine ⟨120608421152843177366016833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80405614101895451577344555 120608421152843177366016833)
      ·
        refine ⟨90456315864632383024512625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120608421152843177366016833 90456315864632383024512625)
        ·
          refine ⟨67842236898474287268384469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90456315864632383024512625 67842236898474287268384469)
          ·
            refine ⟨1590052427307991107852761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 67842236898474287268384469 1590052427307991107852761)
            ·
              refine ⟨1192539320480993330889571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590052427307991107852761 1192539320480993330889571)
              ·
                refine ⟨1788808980721489996334357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192539320480993330889571 1788808980721489996334357)
                ·
                  refine ⟨83850420971319843578173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1788808980721489996334357 83850420971319843578173)
                  ·
                    rfl

theorem cell23_1469683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 6].length) (baseStart_1469683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469683 prefixEnd_1469683 := by exact prefixLift 1469683
  have htrace : WordTrace (prefixWord ++ tailWord_1469683) baseStart_1469683 baseEnd_1469683 := by
    simpa [prefixWord, tailWord_1469683, baseEnd_1469683] using wordTrace_append hprefix tailTrace_1469683
  have hstable : (prefixWord ++ tailWord_1469683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469683).length < 2 ^ (prefixWord ++ tailWord_1469683).sum := by decide
  have hdescent : baseEnd_1469683 < baseStart_1469683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469713 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 1, 5]
def baseStart_1469713 : Nat := 118140960795 + 1469713 * 2 ^ 59
def prefixEnd_1469713 : Nat := 4983230072969 + 3 ^ 40 * 1469713 * 2
def baseEnd_1469713 : Nat := 251556397720504491609473

theorem tailTrace_1469713 : CollatzResearch.WordTrace tailWord_1469713 prefixEnd_1469713 251556397720504491609473 := by
  unfold tailWord_1469713
  simp only [CollatzResearch.WordTrace]
  refine ⟨53604836924488282841821793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35736557949658855227881195 53604836924488282841821793)
  ·
    refine ⟨40203627693366212131366345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53604836924488282841821793 40203627693366212131366345)
    ·
      refine ⟨30152720770024659098524759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40203627693366212131366345 30152720770024659098524759)
      ·
        refine ⟨45229081155036988647787139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30152720770024659098524759 45229081155036988647787139)
        ·
          refine ⟨67843621732555482971680709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45229081155036988647787139 67843621732555482971680709)
          ·
            refine ⟨12720679074854153057190133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67843621732555482971680709 12720679074854153057190133)
            ·
              refine ⟨1192563663267576849111575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12720679074854153057190133 1192563663267576849111575)
              ·
                refine ⟨1788845494901365273667363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192563663267576849111575 1788845494901365273667363)
                ·
                  refine ⟨2683268242352047910501045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788845494901365273667363 2683268242352047910501045)
                  ·
                    refine ⟨251556397720504491609473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2683268242352047910501045 251556397720504491609473)
                    ·
                      rfl

theorem cell23_1469713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_1469713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469713 prefixEnd_1469713 := by exact prefixLift 1469713
  have htrace : WordTrace (prefixWord ++ tailWord_1469713) baseStart_1469713 baseEnd_1469713 := by
    simpa [prefixWord, tailWord_1469713, baseEnd_1469713] using wordTrace_append hprefix tailTrace_1469713
  have hstable : (prefixWord ++ tailWord_1469713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469713).length < 2 ^ (prefixWord ++ tailWord_1469713).sum := by decide
  have hdescent : baseEnd_1469713 < baseStart_1469713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469727 : List Nat := [1, 1, 2, 4, 4, 1, 1, 4, 1, 1, 3]
def baseStart_1469727 : Nat := 118140960795 + 1469727 * 2 ^ 59
def prefixEnd_1469727 : Nat := 4983230072969 + 3 ^ 40 * 1469727 * 2
def baseEnd_1469727 : Nat := 754676381890676420053355

theorem tailTrace_1469727 : CollatzResearch.WordTrace tailWord_1469727 prefixEnd_1469727 754676381890676420053355 := by
  unfold tailWord_1469727
  simp only [CollatzResearch.WordTrace]
  refine ⟨53605347546437563232831435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35736898364291708821887623 53605347546437563232831435)
  ·
    refine ⟨80408021319656344849247153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53605347546437563232831435 80408021319656344849247153)
    ·
      refine ⟨60306015989742258636935365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80408021319656344849247153 60306015989742258636935365)
      ·
        refine ⟨11307377998076673494425381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60306015989742258636935365 11307377998076673494425381)
        ·
          refine ⟨2120133374639376280204759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11307377998076673494425381 2120133374639376280204759)
          ·
            refine ⟨3180200061959064420307139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120133374639376280204759 3180200061959064420307139)
            ·
              refine ⟨4770300092938596630460709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180200061959064420307139 4770300092938596630460709)
              ·
                refine ⟨894431267425986868211383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4770300092938596630460709 894431267425986868211383)
                ·
                  refine ⟨1341646901138980302317075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894431267425986868211383 1341646901138980302317075)
                  ·
                    refine ⟨2012470351708470453475613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1341646901138980302317075 2012470351708470453475613)
                    ·
                      refine ⟨754676381890676420053355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012470351708470453475613 754676381890676420053355)
                      ·
                        rfl

theorem cell23_1469727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_1469727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469727 prefixEnd_1469727 := by exact prefixLift 1469727
  have htrace : WordTrace (prefixWord ++ tailWord_1469727) baseStart_1469727 baseEnd_1469727 := by
    simpa [prefixWord, tailWord_1469727, baseEnd_1469727] using wordTrace_append hprefix tailTrace_1469727
  have hstable : (prefixWord ++ tailWord_1469727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469727).length < 2 ^ (prefixWord ++ tailWord_1469727).sum := by decide
  have hdescent : baseEnd_1469727 < baseStart_1469727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469767 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_1469767 : Nat := 118140960795 + 1469767 * 2 ^ 59
def prefixEnd_1469767 : Nat := 4983230072969 + 3 ^ 40 * 1469767 * 2
def baseEnd_1469767 : Nat := 754696921116856263553171

theorem tailTrace_1469767 : CollatzResearch.WordTrace tailWord_1469767 prefixEnd_1469767 754696921116856263553171 := by
  unfold tailWord_1469767
  simp only [CollatzResearch.WordTrace]
  refine ⟨53606806466292650064287555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35737870977528433376191703 53606806466292650064287555)
  ·
    refine ⟨80410209699438975096431333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53606806466292650064287555 80410209699438975096431333)
    ·
      refine ⟨15076914318644807830580875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80410209699438975096431333 15076914318644807830580875)
      ·
        refine ⟨22615371477967211745871313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15076914318644807830580875 22615371477967211745871313)
        ·
          refine ⟨16961528608475408809403485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22615371477967211745871313 16961528608475408809403485)
          ·
            refine ⟨6360573228178278303526307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16961528608475408809403485 6360573228178278303526307)
            ·
              refine ⟨9540859842267417455289461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6360573228178278303526307 9540859842267417455289461)
              ·
                refine ⟨894455610212570386433387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9540859842267417455289461 894455610212570386433387)
                ·
                  refine ⟨1341683415318855579650081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894455610212570386433387 1341683415318855579650081)
                  ·
                    refine ⟨1006262561489141684737561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341683415318855579650081 1006262561489141684737561)
                    ·
                      refine ⟨754696921116856263553171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006262561489141684737561 754696921116856263553171)
                      ·
                        rfl

theorem cell23_1469767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_1469767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469767 prefixEnd_1469767 := by exact prefixLift 1469767
  have htrace : WordTrace (prefixWord ++ tailWord_1469767) baseStart_1469767 baseEnd_1469767 := by
    simpa [prefixWord, tailWord_1469767, baseEnd_1469767] using wordTrace_append hprefix tailTrace_1469767
  have hstable : (prefixWord ++ tailWord_1469767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469767).length < 2 ^ (prefixWord ++ tailWord_1469767).sum := by decide
  have hdescent : baseEnd_1469767 < baseStart_1469767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469793 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_1469793 : Nat := 118140960795 + 1469793 * 2 ^ 59
def prefixEnd_1469793 : Nat := 4983230072969 + 3 ^ 40 * 1469793 * 2
def baseEnd_1469793 : Nat := 754710271613873161828051

theorem tailTrace_1469793 : CollatzResearch.WordTrace tailWord_1469793 prefixEnd_1469793 754710271613873161828051 := by
  unfold tailWord_1469793
  simp only [CollatzResearch.WordTrace]
  refine ⟨53607754764198456504734033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35738503176132304336489355 53607754764198456504734033)
  ·
    refine ⟨40205816073148842378550525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53607754764198456504734033 40205816073148842378550525)
    ·
      refine ⟨15077181027430815891956447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40205816073148842378550525 15077181027430815891956447)
      ·
        refine ⟨22615771541146223837934671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15077181027430815891956447 22615771541146223837934671)
        ·
          refine ⟨33923657311719335756902007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22615771541146223837934671 33923657311719335756902007)
          ·
            refine ⟨50885485967579003635353011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33923657311719335756902007 50885485967579003635353011)
            ·
              refine ⟨76328228951368505453029517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50885485967579003635353011 76328228951368505453029517)
              ·
                refine ⟨28623085856763189544886069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76328228951368505453029517 28623085856763189544886069)
                ·
                  refine ⟨2683414299071549019833069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28623085856763189544886069 2683414299071549019833069)
                  ·
                    refine ⟨1006280362151830882437401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683414299071549019833069 1006280362151830882437401)
                    ·
                      refine ⟨754710271613873161828051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006280362151830882437401 754710271613873161828051)
                      ·
                        rfl

theorem cell23_1469793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_1469793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469793 prefixEnd_1469793 := by exact prefixLift 1469793
  have htrace : WordTrace (prefixWord ++ tailWord_1469793) baseStart_1469793 baseEnd_1469793 := by
    simpa [prefixWord, tailWord_1469793, baseEnd_1469793] using wordTrace_append hprefix tailTrace_1469793
  have hstable : (prefixWord ++ tailWord_1469793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469793).length < 2 ^ (prefixWord ++ tailWord_1469793).sum := by decide
  have hdescent : baseEnd_1469793 < baseStart_1469793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469900 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1469900 : Nat := 118140960795 + 1469900 * 2 ^ 59
def prefixEnd_1469900 : Nat := 4983230072969 + 3 ^ 40 * 1469900 * 2
def baseEnd_1469900 : Nat := 754765214043904243190059

theorem tailTrace_1469900 : CollatzResearch.WordTrace tailWord_1469900 prefixEnd_1469900 754765214043904243190059 := by
  unfold tailWord_1469900
  simp only [CollatzResearch.WordTrace]
  refine ⟨26805828687405406889439577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35741104916540542519252769 26805828687405406889439577)
  ·
    refine ⟨20104371515554055167079683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26805828687405406889439577 20104371515554055167079683)
    ·
      refine ⟨30156557273331082750619525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20104371515554055167079683 30156557273331082750619525)
      ·
        refine ⟨5654354488749578015741161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30156557273331082750619525 5654354488749578015741161)
        ·
          refine ⟨4240765866562183511805871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5654354488749578015741161 4240765866562183511805871)
          ·
            refine ⟨6361148799843275267708807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240765866562183511805871 6361148799843275267708807)
            ·
              refine ⟨9541723199764912901563211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6361148799843275267708807 9541723199764912901563211)
              ·
                refine ⟨14312584799647369352344817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9541723199764912901563211 14312584799647369352344817)
                ·
                  refine ⟨10734438599735527014258613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14312584799647369352344817 10734438599735527014258613)
                  ·
                    refine ⟨1006353618725205657586745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10734438599735527014258613 1006353618725205657586745)
                    ·
                      refine ⟨754765214043904243190059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006353618725205657586745 754765214043904243190059)
                      ·
                        rfl

theorem cell23_1469900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1469900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469900 prefixEnd_1469900 := by exact prefixLift 1469900
  have htrace : WordTrace (prefixWord ++ tailWord_1469900) baseStart_1469900 baseEnd_1469900 := by
    simpa [prefixWord, tailWord_1469900, baseEnd_1469900] using wordTrace_append hprefix tailTrace_1469900
  have hstable : (prefixWord ++ tailWord_1469900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469900).length < 2 ^ (prefixWord ++ tailWord_1469900).sum := by decide
  have hdescent : baseEnd_1469900 < baseStart_1469900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469930 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1469930 : Nat := 118140960795 + 1469930 * 2 ^ 59
def prefixEnd_1469930 : Nat := 4983230072969 + 3 ^ 40 * 1469930 * 2
def baseEnd_1469930 : Nat := 754780618463539125814921

theorem tailTrace_1469930 : CollatzResearch.WordTrace tailWord_1469930 prefixEnd_1469930 754780618463539125814921 := by
  unfold tailWord_1469930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13403187891175532225617811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35741834376468085934980829 13403187891175532225617811)
  ·
    refine ⟨20104781836763298338426717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13403187891175532225617811 20104781836763298338426717)
    ·
      refine ⟨7539293188786236876910019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20104781836763298338426717 7539293188786236876910019)
      ·
        refine ⟨11308939783179355315365029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7539293188786236876910019 11308939783179355315365029)
        ·
          refine ⟨2120426209346129121630943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11308939783179355315365029 2120426209346129121630943)
          ·
            refine ⟨3180639314019193682446415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2120426209346129121630943 3180639314019193682446415)
            ·
              refine ⟨4770958971028790523669623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180639314019193682446415 4770958971028790523669623)
              ·
                refine ⟨7156438456543185785504435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770958971028790523669623 7156438456543185785504435)
                ·
                  refine ⟨10734657684814778678256653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7156438456543185785504435 10734657684814778678256653)
                  ·
                    refine ⟨4025496631805542004346245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10734657684814778678256653 4025496631805542004346245)
                    ·
                      refine ⟨754780618463539125814921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4025496631805542004346245 754780618463539125814921)
                      ·
                        rfl

theorem cell23_1469930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1469930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469930 prefixEnd_1469930 := by exact prefixLift 1469930
  have htrace : WordTrace (prefixWord ++ tailWord_1469930) baseStart_1469930 baseEnd_1469930 := by
    simpa [prefixWord, tailWord_1469930, baseEnd_1469930] using wordTrace_append hprefix tailTrace_1469930
  have hstable : (prefixWord ++ tailWord_1469930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469930).length < 2 ^ (prefixWord ++ tailWord_1469930).sum := by decide
  have hdescent : baseEnd_1469930 < baseStart_1469930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1469983 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 3, 5]
def baseStart_1469983 : Nat := 118140960795 + 1469983 * 2 ^ 59
def prefixEnd_1469983 : Nat := 4983230072969 + 3 ^ 40 * 1469983 * 2
def baseEnd_1469983 : Nat := 251602610979409139484059

theorem tailTrace_1469983 : CollatzResearch.WordTrace tailWord_1469983 prefixEnd_1469983 251602610979409139484059 := by
  unfold tailWord_1469983
  simp only [CollatzResearch.WordTrace]
  refine ⟨53614684633510118954150603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35743123089006745969433735 53614684633510118954150603)
  ·
    refine ⟨80422026950265178431225905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53614684633510118954150603 80422026950265178431225905)
    ·
      refine ⟨60316520212698883823419429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80422026950265178431225905 60316520212698883823419429)
      ·
        refine ⟨11309347539881040716891143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60316520212698883823419429 11309347539881040716891143)
        ·
          refine ⟨16964021309821561075336715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309347539881040716891143 16964021309821561075336715)
          ·
            refine ⟨25446031964732341613005073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16964021309821561075336715 25446031964732341613005073)
            ·
              refine ⟨19084523973549256209753805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25446031964732341613005073 19084523973549256209753805)
              ·
                refine ⟨7156696490080971078657677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19084523973549256209753805 7156696490080971078657677)
                ·
                  refine ⟨2683761183780364154496629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7156696490080971078657677 2683761183780364154496629)
                  ·
                    refine ⟨251602610979409139484059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2683761183780364154496629 251602610979409139484059)
                    ·
                      rfl

theorem cell23_1469983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 5].length) (baseStart_1469983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1469983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1469983 prefixEnd_1469983 := by exact prefixLift 1469983
  have htrace : WordTrace (prefixWord ++ tailWord_1469983) baseStart_1469983 baseEnd_1469983 := by
    simpa [prefixWord, tailWord_1469983, baseEnd_1469983] using wordTrace_append hprefix tailTrace_1469983
  have hstable : (prefixWord ++ tailWord_1469983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1469983).length < 2 ^ (prefixWord ++ tailWord_1469983).sum := by decide
  have hdescent : baseEnd_1469983 < baseStart_1469983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1469983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470007 : List Nat := [1, 1, 3, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_1470007 : Nat := 118140960795 + 1470007 * 2 ^ 59
def prefixEnd_1470007 : Nat := 4983230072969 + 3 ^ 40 * 1470007 * 2
def baseEnd_1470007 : Nat := 754820156473935324552067

theorem tailTrace_1470007 : CollatzResearch.WordTrace tailWord_1470007 prefixEnd_1470007 754820156473935324552067 := by
  unfold tailWord_1470007
  simp only [CollatzResearch.WordTrace]
  refine ⟨53615559985423171053024275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35743706656948780702016183 53615559985423171053024275)
  ·
    refine ⟨80423339978134756579536413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53615559985423171053024275 80423339978134756579536413)
    ·
      refine ⟨30158752491800533717326155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80423339978134756579536413 30158752491800533717326155)
      ·
        refine ⟨45238128737700800575989233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30158752491800533717326155 45238128737700800575989233)
        ·
          refine ⟨33928596553275600431991925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45238128737700800575989233 33928596553275600431991925)
          ·
            refine ⟨3180805926869587540499243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33928596553275600431991925 3180805926869587540499243)
            ·
              refine ⟨4771208890304381310748865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180805926869587540499243 4771208890304381310748865)
              ·
                refine ⟨3578406667728285983061649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4771208890304381310748865 3578406667728285983061649)
                ·
                  refine ⟨2683805000796214487296237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3578406667728285983061649 2683805000796214487296237)
                  ·
                    refine ⟨1006426875298580432736089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2683805000796214487296237 1006426875298580432736089)
                    ·
                      refine ⟨754820156473935324552067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006426875298580432736089 754820156473935324552067)
                      ·
                        rfl

theorem cell23_1470007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_1470007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470007 prefixEnd_1470007 := by exact prefixLift 1470007
  have htrace : WordTrace (prefixWord ++ tailWord_1470007) baseStart_1470007 baseEnd_1470007 := by
    simpa [prefixWord, tailWord_1470007, baseEnd_1470007] using wordTrace_append hprefix tailTrace_1470007
  have hstable : (prefixWord ++ tailWord_1470007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470007).length < 2 ^ (prefixWord ++ tailWord_1470007).sum := by decide
  have hdescent : baseEnd_1470007 < baseStart_1470007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470033 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1470033 : Nat := 118140960795 + 1470033 * 2 ^ 59
def prefixEnd_1470033 : Nat := 4983230072969 + 3 ^ 40 * 1470033 * 2
def baseEnd_1470033 : Nat := 754833506970952222826947

theorem tailTrace_1470033 : CollatzResearch.WordTrace tailWord_1470033 prefixEnd_1470033 754833506970952222826947 := by
  unfold tailWord_1470033
  simp only [CollatzResearch.WordTrace]
  refine ⟨53616508283328977493470753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35744338855552651662313835 53616508283328977493470753)
  ·
    refine ⟨40212381212496733120103065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53616508283328977493470753 40212381212496733120103065)
    ·
      refine ⟨30159285909372549840077299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40212381212496733120103065 30159285909372549840077299)
      ·
        refine ⟨45238928864058824760115949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30159285909372549840077299 45238928864058824760115949)
        ·
          refine ⟨16964598324022059285043481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45238928864058824760115949 16964598324022059285043481)
          ·
            refine ⟨12723448743016544463782611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16964598324022059285043481 12723448743016544463782611)
            ·
              refine ⟨19085173114524816695673917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723448743016544463782611 19085173114524816695673917)
              ·
                refine ⟨7156939917946806260877719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19085173114524816695673917 7156939917946806260877719)
                ·
                  refine ⟨10735409876920209391316579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7156939917946806260877719 10735409876920209391316579)
                  ·
                    refine ⟨16103114815380314086974869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10735409876920209391316579 16103114815380314086974869)
                    ·
                      refine ⟨754833506970952222826947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16103114815380314086974869 754833506970952222826947)
                      ·
                        rfl

theorem cell23_1470033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1470033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470033 prefixEnd_1470033 := by exact prefixLift 1470033
  have htrace : WordTrace (prefixWord ++ tailWord_1470033) baseStart_1470033 baseEnd_1470033 := by
    simpa [prefixWord, tailWord_1470033, baseEnd_1470033] using wordTrace_append hprefix tailTrace_1470033
  have hstable : (prefixWord ++ tailWord_1470033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470033).length < 2 ^ (prefixWord ++ tailWord_1470033).sum := by decide
  have hdescent : baseEnd_1470033 < baseStart_1470033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470037 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_1470037 : Nat := 118140960795 + 1470037 * 2 ^ 59
def prefixEnd_1470037 : Nat := 4983230072969 + 3 ^ 40 * 1470037 * 2
def baseEnd_1470037 : Nat := 754835560893570207176929

theorem tailTrace_1470037 : CollatzResearch.WordTrace tailWord_1470037 prefixEnd_1470037 754835560893570207176929 := by
  unfold tailWord_1470037
  simp only [CollatzResearch.WordTrace]
  refine ⟨53616654175314486176616365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35744436116876324117744243 53616654175314486176616365)
  ·
    refine ⟨20106245315742932316231137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53616654175314486176616365 20106245315742932316231137)
    ·
      refine ⟨15079683986807199237173353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20106245315742932316231137 15079683986807199237173353)
      ·
        refine ⟨11309762990105399427880015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15079683986807199237173353 11309762990105399427880015)
        ·
          refine ⟨16964644485158099141820023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11309762990105399427880015 16964644485158099141820023)
          ·
            refine ⟨25446966727737148712730035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16964644485158099141820023 25446966727737148712730035)
            ·
              refine ⟨38170450091605723069095053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25446966727737148712730035 38170450091605723069095053)
              ·
                refine ⟨14313918784352146150910645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38170450091605723069095053 14313918784352146150910645)
                ·
                  refine ⟨1341929886033013701647873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14313918784352146150910645 1341929886033013701647873)
                  ·
                    refine ⟨1006447414524760276235905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1341929886033013701647873 1006447414524760276235905)
                    ·
                      refine ⟨754835560893570207176929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006447414524760276235905 754835560893570207176929)
                      ·
                        rfl

theorem cell23_1470037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_1470037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470037 prefixEnd_1470037 := by exact prefixLift 1470037
  have htrace : WordTrace (prefixWord ++ tailWord_1470037) baseStart_1470037 baseEnd_1470037 := by
    simpa [prefixWord, tailWord_1470037, baseEnd_1470037] using wordTrace_append hprefix tailTrace_1470037
  have hstable : (prefixWord ++ tailWord_1470037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470037).length < 2 ^ (prefixWord ++ tailWord_1470037).sum := by decide
  have hdescent : baseEnd_1470037 < baseStart_1470037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470073 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 9]
def baseStart_1470073 : Nat := 118140960795 + 1470073 * 2 ^ 59
def prefixEnd_1470073 : Nat := 4983230072969 + 3 ^ 40 * 1470073 * 2
def baseEnd_1470073 : Nat := 251618015399044022108921

theorem tailTrace_1470073 : CollatzResearch.WordTrace tailWord_1470073 prefixEnd_1470073 251618015399044022108921 := by
  unfold tailWord_1470073
  simp only [CollatzResearch.WordTrace]
  refine ⟨53617967203184064324926873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35745311468789376216617915 53617967203184064324926873)
  ·
    refine ⟨40213475402388048243695155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53617967203184064324926873 40213475402388048243695155)
    ·
      refine ⟨60320213103582072365542733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40213475402388048243695155 60320213103582072365542733)
      ·
        refine ⟨22620079913843277137078525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60320213103582072365542733 22620079913843277137078525)
        ·
          refine ⟨8482529967691228926404447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22620079913843277137078525 8482529967691228926404447)
          ·
            refine ⟨12723794951536843389606671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8482529967691228926404447 12723794951536843389606671)
            ·
              refine ⟨19085692427305265084410007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12723794951536843389606671 19085692427305265084410007)
              ·
                refine ⟨28628538640957897626615011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19085692427305265084410007 28628538640957897626615011)
                ·
                  refine ⟨42942807961436846439922517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28628538640957897626615011 42942807961436846439922517)
                  ·
                    refine ⟨251618015399044022108921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42942807961436846439922517 251618015399044022108921)
                    ·
                      rfl

theorem cell23_1470073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_1470073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470073 prefixEnd_1470073 := by exact prefixLift 1470073
  have htrace : WordTrace (prefixWord ++ tailWord_1470073) baseStart_1470073 baseEnd_1470073 := by
    simpa [prefixWord, tailWord_1470073, baseEnd_1470073] using wordTrace_append hprefix tailTrace_1470073
  have hstable : (prefixWord ++ tailWord_1470073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470073).length < 2 ^ (prefixWord ++ tailWord_1470073).sum := by decide
  have hdescent : baseEnd_1470073 < baseStart_1470073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470083 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1470083 : Nat := 118140960795 + 1470083 * 2 ^ 59
def prefixEnd_1470083 : Nat := 4983230072969 + 3 ^ 40 * 1470083 * 2
def baseEnd_1470083 : Nat := 754859181003677027201717

theorem tailTrace_1470083 : CollatzResearch.WordTrace tailWord_1470083 prefixEnd_1470083 754859181003677027201717 := by
  unfold tailWord_1470083
  simp only [CollatzResearch.WordTrace]
  refine ⟨53618331933147836032790903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35745554622098557355193935 53618331933147836032790903)
  ·
    refine ⟨80427497899721754049186355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53618331933147836032790903 80427497899721754049186355)
    ·
      refine ⟨120641246849582631073779533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80427497899721754049186355 120641246849582631073779533)
      ·
        refine ⟨45240467568593486652667325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120641246849582631073779533 45240467568593486652667325)
        ·
          refine ⟨16965175338222557494750247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45240467568593486652667325 16965175338222557494750247)
          ·
            refine ⟨25447763007333836242125371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16965175338222557494750247 25447763007333836242125371)
            ·
              refine ⟨38171644511000754363188057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25447763007333836242125371 38171644511000754363188057)
              ·
                refine ⟨28628733383250565772391043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38171644511000754363188057 28628733383250565772391043)
                ·
                  refine ⟨42943100074875848658586565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28628733383250565772391043 42943100074875848658586565)
                  ·
                    refine ⟨8051831264039221623484981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42943100074875848658586565 8051831264039221623484981)
                    ·
                      refine ⟨754859181003677027201717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8051831264039221623484981 754859181003677027201717)
                      ·
                        rfl

theorem cell23_1470083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1470083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470083 prefixEnd_1470083 := by exact prefixLift 1470083
  have htrace : WordTrace (prefixWord ++ tailWord_1470083) baseStart_1470083 baseEnd_1470083 := by
    simpa [prefixWord, tailWord_1470083, baseEnd_1470083] using wordTrace_append hprefix tailTrace_1470083
  have hstable : (prefixWord ++ tailWord_1470083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470083).length < 2 ^ (prefixWord ++ tailWord_1470083).sum := by decide
  have hdescent : baseEnd_1470083 < baseStart_1470083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470087 : List Nat := [1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_1470087 : Nat := 118140960795 + 1470087 * 2 ^ 59
def prefixEnd_1470087 : Nat := 4983230072969 + 3 ^ 40 * 1470087 * 2
def baseEnd_1470087 : Nat := 754861234926295011551699

theorem tailTrace_1470087 : CollatzResearch.WordTrace tailWord_1470087 prefixEnd_1470087 754861234926295011551699 := by
  unfold tailWord_1470087
  simp only [CollatzResearch.WordTrace]
  refine ⟨53618477825133344715936515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35745651883422229810624343 53618477825133344715936515)
  ·
    refine ⟨80427716737700017073904773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53618477825133344715936515 80427716737700017073904773)
    ·
      refine ⟨15080196888318753201357145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80427716737700017073904773 15080196888318753201357145)
      ·
        refine ⟨11310147666239064901017859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15080196888318753201357145 11310147666239064901017859)
        ·
          refine ⟨16965221499358597351526789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11310147666239064901017859 16965221499358597351526789)
          ·
            refine ⟨3180979031129737003411273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16965221499358597351526789 3180979031129737003411273)
            ·
              refine ⟨2385734273347302752558455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180979031129737003411273 2385734273347302752558455)
              ·
                refine ⟨3578601410020954128837683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385734273347302752558455 3578601410020954128837683)
                ·
                  refine ⟨5367902115031431193256525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3578601410020954128837683 5367902115031431193256525)
                  ·
                    refine ⟨2012963293136786697471197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5367902115031431193256525 2012963293136786697471197)
                    ·
                      refine ⟨754861234926295011551699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012963293136786697471197 754861234926295011551699)
                      ·
                        rfl

theorem cell23_1470087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_1470087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470087 prefixEnd_1470087 := by exact prefixLift 1470087
  have htrace : WordTrace (prefixWord ++ tailWord_1470087) baseStart_1470087 baseEnd_1470087 := by
    simpa [prefixWord, tailWord_1470087, baseEnd_1470087] using wordTrace_append hprefix tailTrace_1470087
  have hstable : (prefixWord ++ tailWord_1470087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470087).length < 2 ^ (prefixWord ++ tailWord_1470087).sum := by decide
  have hdescent : baseEnd_1470087 < baseStart_1470087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470108 : List Nat := [2, 2, 3, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1470108 : Nat := 118140960795 + 1470108 * 2 ^ 59
def prefixEnd_1470108 : Nat := 4983230072969 + 3 ^ 40 * 1470108 * 2
def baseEnd_1470108 : Nat := 754872018020039429389103

theorem tailTrace_1470108 : CollatzResearch.WordTrace tailWord_1470108 prefixEnd_1470108 754872018020039429389103 := by
  unfold tailWord_1470108
  simp only [CollatzResearch.WordTrace]
  refine ⟨26809621879028632651225489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35746162505371510201633985 26809621879028632651225489)
  ·
    refine ⟨20107216409271474488419117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26809621879028632651225489 20107216409271474488419117)
    ·
      refine ⟨7540206153476802933157169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20107216409271474488419117 7540206153476802933157169)
      ·
        refine ⟨5655154615107602199867877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7540206153476802933157169 5655154615107602199867877)
        ·
          refine ⟨1060341490332675412475227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5655154615107602199867877 1060341490332675412475227)
          ·
            refine ⟨1590512235499013118712841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1060341490332675412475227 1590512235499013118712841)
            ·
              refine ⟨1192884176624259839034631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1590512235499013118712841 1192884176624259839034631)
              ·
                refine ⟨1789326264936389758551947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1192884176624259839034631 1789326264936389758551947)
                ·
                  refine ⟨2683989397404584637827921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789326264936389758551947 2683989397404584637827921)
                  ·
                    refine ⟨2012992048053438478370941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2683989397404584637827921 2012992048053438478370941)
                    ·
                      refine ⟨754872018020039429389103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2012992048053438478370941 754872018020039429389103)
                      ·
                        rfl

theorem cell23_1470108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1470108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470108 prefixEnd_1470108 := by exact prefixLift 1470108
  have htrace : WordTrace (prefixWord ++ tailWord_1470108) baseStart_1470108 baseEnd_1470108 := by
    simpa [prefixWord, tailWord_1470108, baseEnd_1470108] using wordTrace_append hprefix tailTrace_1470108
  have hstable : (prefixWord ++ tailWord_1470108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470108).length < 2 ^ (prefixWord ++ tailWord_1470108).sum := by decide
  have hdescent : baseEnd_1470108 < baseStart_1470108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470130 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_1470130 : Nat := 118140960795 + 1470130 * 2 ^ 59
def prefixEnd_1470130 : Nat := 4983230072969 + 3 ^ 40 * 1470130 * 2
def baseEnd_1470130 : Nat := 754883314594438343314001

theorem tailTrace_1470130 : CollatzResearch.WordTrace tailWord_1470130 prefixEnd_1470130 754883314594438343314001 := by
  unfold tailWord_1470130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13405011540994390764937961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35746697442651708706501229 13405011540994390764937961)
  ·
    refine ⟨10053758655745793073703471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13405011540994390764937961 10053758655745793073703471)
    ·
      refine ⟨15080637983618689610555207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10053758655745793073703471 15080637983618689610555207)
      ·
        refine ⟨22620956975428034415832811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15080637983618689610555207 22620956975428034415832811)
        ·
          refine ⟨33931435463142051623749217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22620956975428034415832811 33931435463142051623749217)
          ·
            refine ⟨25448576597356538717811913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33931435463142051623749217 25448576597356538717811913)
            ·
              refine ⟨19086432448017404038358935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25448576597356538717811913 19086432448017404038358935)
              ·
                refine ⟨28629648672026106057538403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19086432448017404038358935 28629648672026106057538403)
                ·
                  refine ⟨42944473008039159086307605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28629648672026106057538403 42944473008039159086307605)
                  ·
                    refine ⟨2013022172251835582170669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 42944473008039159086307605 2013022172251835582170669)
                    ·
                      refine ⟨754883314594438343314001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2013022172251835582170669 754883314594438343314001)
                      ·
                        rfl

theorem cell23_1470130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_1470130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470130 prefixEnd_1470130 := by exact prefixLift 1470130
  have htrace : WordTrace (prefixWord ++ tailWord_1470130) baseStart_1470130 baseEnd_1470130 := by
    simpa [prefixWord, tailWord_1470130, baseEnd_1470130] using wordTrace_append hprefix tailTrace_1470130
  have hstable : (prefixWord ++ tailWord_1470130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470130).length < 2 ^ (prefixWord ++ tailWord_1470130).sum := by decide
  have hdescent : baseEnd_1470130 < baseStart_1470130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470160 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3]
def baseStart_1470160 : Nat := 118140960795 + 1470160 * 2 ^ 59
def prefixEnd_1470160 : Nat := 4983230072969 + 3 ^ 40 * 1470160 * 2
def baseEnd_1470160 : Nat := 754898719014073225938863

theorem tailTrace_1470160 : CollatzResearch.WordTrace tailWord_1470160 prefixEnd_1470160 754898719014073225938863 := by
  unfold tailWord_1470160
  simp only [CollatzResearch.WordTrace]
  refine ⟨26810570176934439091671967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35747426902579252122229289 26810570176934439091671967)
  ·
    refine ⟨40215855265401658637507951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26810570176934439091671967 40215855265401658637507951)
    ·
      refine ⟨60323782898102487956261927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40215855265401658637507951 60323782898102487956261927)
      ·
        refine ⟨90485674347153731934392891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60323782898102487956261927 90485674347153731934392891)
        ·
          refine ⟨135728511520730597901589337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90485674347153731934392891 135728511520730597901589337)
          ·
            refine ⟨101796383640547948426192003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135728511520730597901589337 101796383640547948426192003)
            ·
              refine ⟨152694575460821922639288005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101796383640547948426192003 152694575460821922639288005)
              ·
                refine ⟨28630232898904110494866501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152694575460821922639288005 28630232898904110494866501)
                ·
                  refine ⟨5368168668544520717787469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28630232898904110494866501 5368168668544520717787469)
                  ·
                    refine ⟨2013063250704195269170301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5368168668544520717787469 2013063250704195269170301)
                    ·
                      refine ⟨754898719014073225938863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2013063250704195269170301 754898719014073225938863)
                      ·
                        rfl

theorem cell23_1470160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 3].length) (baseStart_1470160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470160 prefixEnd_1470160 := by exact prefixLift 1470160
  have htrace : WordTrace (prefixWord ++ tailWord_1470160) baseStart_1470160 baseEnd_1470160 := by
    simpa [prefixWord, tailWord_1470160, baseEnd_1470160] using wordTrace_append hprefix tailTrace_1470160
  have hstable : (prefixWord ++ tailWord_1470160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470160).length < 2 ^ (prefixWord ++ tailWord_1470160).sum := by decide
  have hdescent : baseEnd_1470160 < baseStart_1470160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470200 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1470200 : Nat := 118140960795 + 1470200 * 2 ^ 59
def prefixEnd_1470200 : Nat := 4983230072969 + 3 ^ 40 * 1470200 * 2
def baseEnd_1470200 : Nat := 754919258240253069438679

theorem tailTrace_1470200 : CollatzResearch.WordTrace tailWord_1470200 prefixEnd_1470200 754919258240253069438679 := by
  unfold tailWord_1470200
  simp only [CollatzResearch.WordTrace]
  refine ⟨26811299636861982507400027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35748399515815976676533369 26811299636861982507400027)
  ·
    refine ⟨40216949455292973761100041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26811299636861982507400027 40216949455292973761100041)
    ·
      refine ⟨30162712091469730320825031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40216949455292973761100041 30162712091469730320825031)
      ·
        refine ⟨45244068137204595481237547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30162712091469730320825031 45244068137204595481237547)
        ·
          refine ⟨67866102205806893221856321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45244068137204595481237547 67866102205806893221856321)
          ·
            refine ⟨50899576654355169916392241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67866102205806893221856321 50899576654355169916392241)
            ·
              refine ⟨38174682490766377437294181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50899576654355169916392241 38174682490766377437294181)
              ·
                refine ⟨7157752967018695769492659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38174682490766377437294181 7157752967018695769492659)
                ·
                  refine ⟨10736629450528043654238989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7157752967018695769492659 10736629450528043654238989)
                  ·
                    refine ⟨4026236043948016370339621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10736629450528043654238989 4026236043948016370339621)
                    ·
                      refine ⟨754919258240253069438679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4026236043948016370339621 754919258240253069438679)
                      ·
                        rfl

theorem cell23_1470200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1470200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470200 prefixEnd_1470200 := by exact prefixLift 1470200
  have htrace : WordTrace (prefixWord ++ tailWord_1470200) baseStart_1470200 baseEnd_1470200 := by
    simpa [prefixWord, tailWord_1470200, baseEnd_1470200] using wordTrace_append hprefix tailTrace_1470200
  have hstable : (prefixWord ++ tailWord_1470200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470200).length < 2 ^ (prefixWord ++ tailWord_1470200).sum := by decide
  have hdescent : baseEnd_1470200 < baseStart_1470200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470217 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 4, 4, 2]
def baseStart_1470217 : Nat := 118140960795 + 1470217 * 2 ^ 59
def prefixEnd_1470217 : Nat := 4983230072969 + 3 ^ 40 * 1470217 * 2
def baseEnd_1470217 : Nat := 754927987411379502926101

theorem tailTrace_1470217 : CollatzResearch.WordTrace tailWord_1470217 prefixEnd_1470217 754927987411379502926101 := by
  unfold tailWord_1470217
  simp only [CollatzResearch.WordTrace]
  refine ⟨53623219314662376918168905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35748812876441584612112603 53623219314662376918168905)
  ·
    refine ⟨40217414485996782688626679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53623219314662376918168905 40217414485996782688626679)
    ·
      refine ⟨60326121728995174032940019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40217414485996782688626679 60326121728995174032940019)
      ·
        refine ⟨90489182593492761049410029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60326121728995174032940019 90489182593492761049410029)
        ·
          refine ⟨33933443472559785393528761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90489182593492761049410029 33933443472559785393528761)
          ·
            refine ⟨25450082604419839045146571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33933443472559785393528761 25450082604419839045146571)
            ·
              refine ⟨38175123906629758567719857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25450082604419839045146571 38175123906629758567719857)
              ·
                refine ⟨28631342929972318925789893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38175123906629758567719857 28631342929972318925789893)
                ·
                  refine ⟨5368376799369809798585605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28631342929972318925789893 5368376799369809798585605)
                  ·
                    refine ⟨1006570649881839337234801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5368376799369809798585605 1006570649881839337234801)
                    ·
                      refine ⟨754927987411379502926101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006570649881839337234801 754927987411379502926101)
                      ·
                        rfl

theorem cell23_1470217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 4, 4, 2].length) (baseStart_1470217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470217 prefixEnd_1470217 := by exact prefixLift 1470217
  have htrace : WordTrace (prefixWord ++ tailWord_1470217) baseStart_1470217 baseEnd_1470217 := by
    simpa [prefixWord, tailWord_1470217, baseEnd_1470217] using wordTrace_append hprefix tailTrace_1470217
  have hstable : (prefixWord ++ tailWord_1470217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470217).length < 2 ^ (prefixWord ++ tailWord_1470217).sum := by decide
  have hdescent : baseEnd_1470217 < baseStart_1470217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470257 : List Nat := [1, 2, 2, 3, 2, 2, 2, 3, 6]
def baseStart_1470257 : Nat := 118140960795 + 1470257 * 2 ^ 59
def prefixEnd_1470257 : Nat := 4983230072969 + 3 ^ 40 * 1470257 * 2
def baseEnd_1470257 : Nat := 83883169626395482936213

theorem tailTrace_1470257 : CollatzResearch.WordTrace tailWord_1470257 prefixEnd_1470257 83883169626395482936213 := by
  unfold tailWord_1470257
  simp only [CollatzResearch.WordTrace]
  refine ⟨53624678234517463749625025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35749785489678309166416683 53624678234517463749625025)
  ·
    refine ⟨40218508675888097812218769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53624678234517463749625025 40218508675888097812218769)
    ·
      refine ⟨30163881506916073359164077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40218508675888097812218769 30163881506916073359164077)
      ·
        refine ⟨11311455565093527509686529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30163881506916073359164077 11311455565093527509686529)
        ·
          refine ⟨8483591673820145632264897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11311455565093527509686529 8483591673820145632264897)
          ·
            refine ⟨6362693755365109224198673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8483591673820145632264897 6362693755365109224198673)
            ·
              refine ⟨4772020316523831918149005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6362693755365109224198673 4772020316523831918149005)
              ·
                refine ⟨1789507618696436969305877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4772020316523831918149005 1789507618696436969305877)
                ·
                  refine ⟨83883169626395482936213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1789507618696436969305877 83883169626395482936213)
                  ·
                    rfl

theorem cell23_1470257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 6].length) (baseStart_1470257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470257 prefixEnd_1470257 := by exact prefixLift 1470257
  have htrace : WordTrace (prefixWord ++ tailWord_1470257) baseStart_1470257 baseEnd_1470257 := by
    simpa [prefixWord, tailWord_1470257, baseEnd_1470257] using wordTrace_append hprefix tailTrace_1470257
  have hstable : (prefixWord ++ tailWord_1470257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470257).length < 2 ^ (prefixWord ++ tailWord_1470257).sum := by decide
  have hdescent : baseEnd_1470257 < baseStart_1470257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470271 : List Nat := [1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 3]
def baseStart_1470271 : Nat := 118140960795 + 1470271 * 2 ^ 59
def prefixEnd_1470271 : Nat := 4983230072969 + 3 ^ 40 * 1470271 * 2
def baseEnd_1470271 : Nat := 754955715366722291650853

theorem tailTrace_1470271 : CollatzResearch.WordTrace tailWord_1470271 prefixEnd_1470271 754955715366722291650853 := by
  unfold tailWord_1470271
  simp only [CollatzResearch.WordTrace]
  refine ⟨53625188856466744140634667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35750125904311162760423111 53625188856466744140634667)
  ·
    refine ⟨80437783284700116210952001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53625188856466744140634667 80437783284700116210952001)
    ·
      refine ⟨60328337463525087158214001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80437783284700116210952001 60328337463525087158214001)
      ·
        refine ⟨45246253097643815368660501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60328337463525087158214001 45246253097643815368660501)
        ·
          refine ⟨2120918113952053845405961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45246253097643815368660501 2120918113952053845405961)
          ·
            refine ⟨1590688585464040384054471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2120918113952053845405961 1590688585464040384054471)
            ·
              refine ⟨2386032878196060576081707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1590688585464040384054471 2386032878196060576081707)
              ·
                refine ⟨3579049317294090864122561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2386032878196060576081707 3579049317294090864122561)
                ·
                  refine ⟨2684286987970568148091921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3579049317294090864122561 2684286987970568148091921)
                  ·
                    refine ⟨2013215240977926111068941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2684286987970568148091921 2013215240977926111068941)
                    ·
                      refine ⟨754955715366722291650853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2013215240977926111068941 754955715366722291650853)
                      ·
                        rfl

theorem cell23_1470271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_1470271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470271 prefixEnd_1470271 := by exact prefixLift 1470271
  have htrace : WordTrace (prefixWord ++ tailWord_1470271) baseStart_1470271 baseEnd_1470271 := by
    simpa [prefixWord, tailWord_1470271, baseEnd_1470271] using wordTrace_append hprefix tailTrace_1470271
  have hstable : (prefixWord ++ tailWord_1470271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470271).length < 2 ^ (prefixWord ++ tailWord_1470271).sum := by decide
  have hdescent : baseEnd_1470271 < baseStart_1470271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470354 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1470354 : Nat := 118140960795 + 1470354 * 2 ^ 59
def prefixEnd_1470354 : Nat := 4983230072969 + 3 ^ 40 * 1470354 * 2
def baseEnd_1470354 : Nat := 754998334261045466912971

theorem tailTrace_1470354 : CollatzResearch.WordTrace tailWord_1470354 prefixEnd_1470354 754998334261045466912971 := by
  unfold tailWord_1470354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13407054028791512328976529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35752144076777366210604077 13407054028791512328976529)
  ·
    refine ⟨10055290521593634246732397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13407054028791512328976529 10055290521593634246732397)
    ·
      refine ⟨3770733945597612842524649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10055290521593634246732397 3770733945597612842524649)
      ·
        refine ⟨2828050459198209631893487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3770733945597612842524649 2828050459198209631893487)
        ·
          refine ⟨4242075688797314447840231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828050459198209631893487 4242075688797314447840231)
          ·
            refine ⟨6363113533195971671760347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242075688797314447840231 6363113533195971671760347)
            ·
              refine ⟨9544670299793957507640521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363113533195971671760347 9544670299793957507640521)
              ·
                refine ⟨7158502724845468130730391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9544670299793957507640521 7158502724845468130730391)
                ·
                  refine ⟨10737754087268202196095587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7158502724845468130730391 10737754087268202196095587)
                  ·
                    refine ⟨16106631130902303294143381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10737754087268202196095587 16106631130902303294143381)
                    ·
                      refine ⟨754998334261045466912971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16106631130902303294143381 754998334261045466912971)
                      ·
                        rfl

theorem cell23_1470354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1470354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470354 prefixEnd_1470354 := by exact prefixLift 1470354
  have htrace : WordTrace (prefixWord ++ tailWord_1470354) baseStart_1470354 baseEnd_1470354 := by
    simpa [prefixWord, tailWord_1470354, baseEnd_1470354] using wordTrace_append hprefix tailTrace_1470354
  have hstable : (prefixWord ++ tailWord_1470354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470354).length < 2 ^ (prefixWord ++ tailWord_1470354).sum := by decide
  have hdescent : baseEnd_1470354 < baseStart_1470354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470364 : List Nat := [2, 2, 3, 3, 1, 2, 2, 8]
def baseStart_1470364 : Nat := 118140960795 + 1470364 * 2 ^ 59
def prefixEnd_1470364 : Nat := 4983230072969 + 3 ^ 40 * 1470364 * 2
def baseEnd_1470364 : Nat := 27963091446947793621775

theorem tailTrace_1470364 : CollatzResearch.WordTrace tailWord_1470364 prefixEnd_1470364 27963091446947793621775 := by
  unfold tailWord_1470364
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814290422564910511885073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35752387230086547349180097 26814290422564910511885073)
  ·
    refine ⟨20110717816923682883913805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26814290422564910511885073 20110717816923682883913805)
    ·
      refine ⟨7541519181346381081467677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20110717816923682883913805 7541519181346381081467677)
      ·
        refine ⟨2828069693004892905550379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7541519181346381081467677 2828069693004892905550379)
        ·
          refine ⟨4242104539507339358325569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828069693004892905550379 4242104539507339358325569)
          ·
            refine ⟨3181578404630504518744177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242104539507339358325569 3181578404630504518744177)
            ·
              refine ⟨2386183803472878389058133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181578404630504518744177 2386183803472878389058133)
              ·
                refine ⟨27963091446947793621775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2386183803472878389058133 27963091446947793621775)
                ·
                  rfl

theorem cell23_1470364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 8].length) (baseStart_1470364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470364 prefixEnd_1470364 := by exact prefixLift 1470364
  have htrace : WordTrace (prefixWord ++ tailWord_1470364) baseStart_1470364 baseEnd_1470364 := by
    simpa [prefixWord, tailWord_1470364, baseEnd_1470364] using wordTrace_append hprefix tailTrace_1470364
  have hstable : (prefixWord ++ tailWord_1470364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470364).length < 2 ^ (prefixWord ++ tailWord_1470364).sum := by decide
  have hdescent : baseEnd_1470364 < baseStart_1470364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470388 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1470388 : Nat := 118140960795 + 1470388 * 2 ^ 59
def prefixEnd_1470388 : Nat := 4983230072969 + 3 ^ 40 * 1470388 * 2
def baseEnd_1470388 : Nat := 755015792603298333887815

theorem tailTrace_1470388 : CollatzResearch.WordTrace tailWord_1470388 prefixEnd_1470388 755015792603298333887815 := by
  unfold tailWord_1470388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26814728098521436561321909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35752970798028582081762545 26814728098521436561321909)
  ·
    refine ⟨2513880759236384677623929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26814728098521436561321909 2513880759236384677623929)
    ·
      refine ⟨1885410569427288508217947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2513880759236384677623929 1885410569427288508217947)
      ·
        refine ⟨2828115854140932762326921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1885410569427288508217947 2828115854140932762326921)
        ·
          refine ⟨2121086890605699571745191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2828115854140932762326921 2121086890605699571745191)
          ·
            refine ⟨3181630335908549357617787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121086890605699571745191 3181630335908549357617787)
            ·
              refine ⟨4772445503862824036426681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3181630335908549357617787 4772445503862824036426681)
              ·
                refine ⟨3579334127897118027320011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4772445503862824036426681 3579334127897118027320011)
                ·
                  refine ⟨5369001191845677040980017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579334127897118027320011 5369001191845677040980017)
                  ·
                    refine ⟨4026750893884257780735013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5369001191845677040980017 4026750893884257780735013)
                    ·
                      refine ⟨755015792603298333887815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4026750893884257780735013 755015792603298333887815)
                      ·
                        rfl

theorem cell23_1470388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1470388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470388 prefixEnd_1470388 := by exact prefixLift 1470388
  have htrace : WordTrace (prefixWord ++ tailWord_1470388) baseStart_1470388 baseEnd_1470388 := by
    simpa [prefixWord, tailWord_1470388, baseEnd_1470388] using wordTrace_append hprefix tailTrace_1470388
  have hstable : (prefixWord ++ tailWord_1470388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470388).length < 2 ^ (prefixWord ++ tailWord_1470388).sum := by decide
  have hdescent : baseEnd_1470388 < baseStart_1470388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470407 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 2, 6]
def baseStart_1470407 : Nat := 118140960795 + 1470407 * 2 ^ 59
def prefixEnd_1470407 : Nat := 4983230072969 + 3 ^ 40 * 1470407 * 2
def baseEnd_1470407 : Nat := 251675182911911253183409

theorem tailTrace_1470407 : CollatzResearch.WordTrace tailWord_1470407 prefixEnd_1470407 251675182911911253183409 := by
  unfold tailWord_1470407
  simp only [CollatzResearch.WordTrace]
  refine ⟨53630149183974039367585475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35753432789316026245056983 53630149183974039367585475)
  ·
    refine ⟨80445223775961059051378213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53630149183974039367585475 80445223775961059051378213)
    ·
      refine ⟨15083479457992698572133415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80445223775961059051378213 15083479457992698572133415)
      ·
        refine ⟨22625219186989047858200123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15083479457992698572133415 22625219186989047858200123)
        ·
          refine ⟨33937828780483571787300185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22625219186989047858200123 33937828780483571787300185)
          ·
            refine ⟨25453371585362678840475139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33937828780483571787300185 25453371585362678840475139)
            ·
              refine ⟨38180057378044018260712709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25453371585362678840475139 38180057378044018260712709)
              ·
                refine ⟨7158760758383253423883633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38180057378044018260712709 7158760758383253423883633)
                ·
                  refine ⟨5369070568787440067912725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7158760758383253423883633 5369070568787440067912725)
                  ·
                    refine ⟨251675182911911253183409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5369070568787440067912725 251675182911911253183409)
                    ·
                      rfl

theorem cell23_1470407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_1470407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470407 prefixEnd_1470407 := by exact prefixLift 1470407
  have htrace : WordTrace (prefixWord ++ tailWord_1470407) baseStart_1470407 baseEnd_1470407 := by
    simpa [prefixWord, tailWord_1470407, baseEnd_1470407] using wordTrace_append hprefix tailTrace_1470407
  have hstable : (prefixWord ++ tailWord_1470407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470407).length < 2 ^ (prefixWord ++ tailWord_1470407).sum := by decide
  have hdescent : baseEnd_1470407 < baseStart_1470407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470408 : List Nat := [2, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_1470408 : Nat := 118140960795 + 1470408 * 2 ^ 59
def prefixEnd_1470408 : Nat := 4983230072969 + 3 ^ 40 * 1470408 * 2
def baseEnd_1470408 : Nat := 755026062216388255637723

theorem tailTrace_1470408 : CollatzResearch.WordTrace tailWord_1470408 prefixEnd_1470408 755026062216388255637723 := by
  unfold tailWord_1470408
  simp only [CollatzResearch.WordTrace]
  refine ⟨26815092828485208269185939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35753457104646944358914585 26815092828485208269185939)
  ·
    refine ⟨40222639242727812403778909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26815092828485208269185939 40222639242727812403778909)
    ·
      refine ⟨15083489716022929651417091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40222639242727812403778909 15083489716022929651417091)
      ·
        refine ⟨22625234574034394477125637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15083489716022929651417091 22625234574034394477125637)
        ·
          refine ⟨4242231482631448964461057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22625234574034394477125637 4242231482631448964461057)
          ·
            refine ⟨3181673611973586723345793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4242231482631448964461057 3181673611973586723345793)
            ·
              refine ⟨2386255208980190042509345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3181673611973586723345793 2386255208980190042509345)
              ·
                refine ⟨1789691406735142531882009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2386255208980190042509345 1789691406735142531882009)
                ·
                  refine ⟨1342268555051356898911507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1789691406735142531882009 1342268555051356898911507)
                  ·
                    refine ⟨2013402832577035348367261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1342268555051356898911507 2013402832577035348367261)
                    ·
                      refine ⟨755026062216388255637723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2013402832577035348367261 755026062216388255637723)
                      ·
                        rfl

theorem cell23_1470408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_1470408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470408 prefixEnd_1470408 := by exact prefixLift 1470408
  have htrace : WordTrace (prefixWord ++ tailWord_1470408) baseStart_1470408 baseEnd_1470408 := by
    simpa [prefixWord, tailWord_1470408, baseEnd_1470408] using wordTrace_append hprefix tailTrace_1470408
  have hstable : (prefixWord ++ tailWord_1470408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470408).length < 2 ^ (prefixWord ++ tailWord_1470408).sum := by decide
  have hdescent : baseEnd_1470408 < baseStart_1470408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470417 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1470417 : Nat := 118140960795 + 1470417 * 2 ^ 59
def prefixEnd_1470417 : Nat := 4983230072969 + 3 ^ 40 * 1470417 * 2
def baseEnd_1470417 : Nat := 755030683542278720425181

theorem tailTrace_1470417 : CollatzResearch.WordTrace tailWord_1470417 prefixEnd_1470417 755030683542278720425181 := by
  unfold tailWord_1470417
  simp only [CollatzResearch.WordTrace]
  refine ⟨53630513913937811075449505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35753675942625207383633003 53630513913937811075449505)
  ·
    refine ⟨40222885435453358306587129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53630513913937811075449505 40222885435453358306587129)
    ·
      refine ⟨30167164076590018729940347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40222885435453358306587129 30167164076590018729940347)
      ·
        refine ⟨45250746114885028094910521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30167164076590018729940347 45250746114885028094910521)
        ·
          refine ⟨33938059586163771071182891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45250746114885028094910521 33938059586163771071182891)
          ·
            refine ⟨50907089379245656606774337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33938059586163771071182891 50907089379245656606774337)
            ·
              refine ⟨38180317034434242455080753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50907089379245656606774337 38180317034434242455080753)
              ·
                refine ⟨28635237775825681841310565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38180317034434242455080753 28635237775825681841310565)
                ·
                  refine ⟨5369107082967315345245731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28635237775825681841310565 5369107082967315345245731)
                  ·
                    refine ⟨8053660624450973017868597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5369107082967315345245731 8053660624450973017868597)
                    ·
                      refine ⟨755030683542278720425181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8053660624450973017868597 755030683542278720425181)
                      ·
                        rfl

theorem cell23_1470417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1470417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470417 prefixEnd_1470417 := by exact prefixLift 1470417
  have htrace : WordTrace (prefixWord ++ tailWord_1470417) baseStart_1470417 baseEnd_1470417 := by
    simpa [prefixWord, tailWord_1470417, baseEnd_1470417] using wordTrace_append hprefix tailTrace_1470417
  have hstable : (prefixWord ++ tailWord_1470417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470417).length < 2 ^ (prefixWord ++ tailWord_1470417).sum := by decide
  have hdescent : baseEnd_1470417 < baseStart_1470417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470431 : List Nat := [1, 1, 2, 3, 4, 1, 1, 3, 1, 4, 2]
def baseStart_1470431 : Nat := 118140960795 + 1470431 * 2 ^ 59
def prefixEnd_1470431 : Nat := 4983230072969 + 3 ^ 40 * 1470431 * 2
def baseEnd_1470431 : Nat := 755037872271441665650117

theorem tailTrace_1470431 : CollatzResearch.WordTrace tailWord_1470431 prefixEnd_1470431 755037872271441665650117 := by
  unfold tailWord_1470431
  simp only [CollatzResearch.WordTrace]
  refine ⟨53631024535887091466459147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35754016357258060977639431 53631024535887091466459147)
  ·
    refine ⟨80446536803830637199688721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53631024535887091466459147 80446536803830637199688721)
    ·
      refine ⟨60334902602872977899766541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80446536803830637199688721 60334902602872977899766541)
      ·
        refine ⟨22625588476077366712412453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60334902602872977899766541 22625588476077366712412453)
        ·
          refine ⟨4242297839264506258577335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22625588476077366712412453 4242297839264506258577335)
          ·
            refine ⟨6363446758896759387866003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4242297839264506258577335 6363446758896759387866003)
            ·
              refine ⟨9545170138345139081799005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6363446758896759387866003 9545170138345139081799005)
              ·
                refine ⟨3579438801879427155674627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9545170138345139081799005 3579438801879427155674627)
                ·
                  refine ⟨5369158202819140733511941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579438801879427155674627 5369158202819140733511941)
                  ·
                    refine ⟨1006717163028588887533489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5369158202819140733511941 1006717163028588887533489)
                    ·
                      refine ⟨755037872271441665650117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006717163028588887533489 755037872271441665650117)
                      ·
                        rfl

theorem cell23_1470431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_1470431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470431 prefixEnd_1470431 := by exact prefixLift 1470431
  have htrace : WordTrace (prefixWord ++ tailWord_1470431) baseStart_1470431 baseEnd_1470431 := by
    simpa [prefixWord, tailWord_1470431, baseEnd_1470431] using wordTrace_append hprefix tailTrace_1470431
  have hstable : (prefixWord ++ tailWord_1470431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470431).length < 2 ^ (prefixWord ++ tailWord_1470431).sum := by decide
  have hdescent : baseEnd_1470431 < baseStart_1470431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470471 : List Nat := [1, 1, 4, 3, 1, 2, 2, 4, 5]
def baseStart_1470471 : Nat := 118140960795 + 1470471 * 2 ^ 59
def prefixEnd_1470471 : Nat := 4983230072969 + 3 ^ 40 * 1470471 * 2
def baseEnd_1470471 : Nat := 83895379055291278794437

theorem tailTrace_1470471 : CollatzResearch.WordTrace tailWord_1470471 prefixEnd_1470471 83895379055291278794437 := by
  unfold tailWord_1470471
  simp only [CollatzResearch.WordTrace]
  refine ⟨53632483455742178297915267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35754988970494785531943511 53632483455742178297915267)
  ·
    refine ⟨80448725183613267446872901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53632483455742178297915267 80448725183613267446872901)
    ·
      refine ⟨15084135971927487646288669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80448725183613267446872901 15084135971927487646288669)
      ·
        refine ⟨5656550989472807867358251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15084135971927487646288669 5656550989472807867358251)
        ·
          refine ⟨8484826484209211801037377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656550989472807867358251 8484826484209211801037377)
          ·
            refine ⟨6363619863156908850778033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8484826484209211801037377 6363619863156908850778033)
            ·
              refine ⟨4772714897367681638083525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6363619863156908850778033 4772714897367681638083525)
              ·
                refine ⟨894884043256440307140661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4772714897367681638083525 894884043256440307140661)
                ·
                  refine ⟨83895379055291278794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 894884043256440307140661 83895379055291278794437)
                  ·
                    rfl

theorem cell23_1470471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 5].length) (baseStart_1470471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470471 prefixEnd_1470471 := by exact prefixLift 1470471
  have htrace : WordTrace (prefixWord ++ tailWord_1470471) baseStart_1470471 baseEnd_1470471 := by
    simpa [prefixWord, tailWord_1470471, baseEnd_1470471] using wordTrace_append hprefix tailTrace_1470471
  have hstable : (prefixWord ++ tailWord_1470471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470471).length < 2 ^ (prefixWord ++ tailWord_1470471).sum := by decide
  have hdescent : baseEnd_1470471 < baseStart_1470471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470582 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_1470582 : Nat := 118140960795 + 1470582 * 2 ^ 59
def prefixEnd_1470582 : Nat := 4983230072969 + 3 ^ 40 * 1470582 * 2
def baseEnd_1470582 : Nat := 251705135950090191620641

theorem tailTrace_1470582 : CollatzResearch.WordTrace tailWord_1470582 prefixEnd_1470582 251705135950090191620641 := by
  unfold tailWord_1470582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352283247396252765950375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35757687972226696170137333 3352283247396252765950375)
  ·
    refine ⟨5028424871094379148925563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352283247396252765950375 5028424871094379148925563)
    ·
      refine ⟨7542637306641568723388345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028424871094379148925563 7542637306641568723388345)
      ·
        refine ⟨5656977979981176542541259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542637306641568723388345 5656977979981176542541259)
        ·
          refine ⟨8485466969971764813811889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5656977979981176542541259 8485466969971764813811889)
          ·
            refine ⟨6364100227478823610358917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8485466969971764813811889 6364100227478823610358917)
            ·
              refine ⟨1193268792652279426942297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6364100227478823610358917 1193268792652279426942297)
              ·
                refine ⟨894951594489209570206723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1193268792652279426942297 894951594489209570206723)
                ·
                  refine ⟨1342427391733814355310085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894951594489209570206723 1342427391733814355310085)
                  ·
                    refine ⟨251705135950090191620641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1342427391733814355310085 251705135950090191620641)
                    ·
                      rfl

theorem cell23_1470582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_1470582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470582 prefixEnd_1470582 := by exact prefixLift 1470582
  have htrace : WordTrace (prefixWord ++ tailWord_1470582) baseStart_1470582 baseEnd_1470582 := by
    simpa [prefixWord, tailWord_1470582, baseEnd_1470582] using wordTrace_append hprefix tailTrace_1470582
  have hstable : (prefixWord ++ tailWord_1470582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470582).length < 2 ^ (prefixWord ++ tailWord_1470582).sum := by decide
  have hdescent : baseEnd_1470582 < baseStart_1470582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470611 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 4]
def baseStart_1470611 : Nat := 118140960795 + 1470611 * 2 ^ 59
def prefixEnd_1470611 : Nat := 4983230072969 + 3 ^ 40 * 1470611 * 2
def baseEnd_1470611 : Nat := 755130298789250961399289

theorem tailTrace_1470611 : CollatzResearch.WordTrace tailWord_1470611 prefixEnd_1470611 755130298789250961399289 := by
  unfold tailWord_1470611
  simp only [CollatzResearch.WordTrace]
  refine ⟨53637589675234982208011687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35758393116823321472007791 53637589675234982208011687)
  ·
    refine ⟨80456384512852473312017531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53637589675234982208011687 80456384512852473312017531)
    ·
      refine ⟨120684576769278709968026297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80456384512852473312017531 120684576769278709968026297)
      ·
        refine ⟨90513432576959032476019723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120684576769278709968026297 90513432576959032476019723)
        ·
          refine ⟨135770148865438548714029585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90513432576959032476019723 135770148865438548714029585)
          ·
            refine ⟨101827611649078911535522189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135770148865438548714029585 101827611649078911535522189)
            ·
              refine ⟨38185354368404591825820821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101827611649078911535522189 38185354368404591825820821)
              ·
                refine ⟨1789938486018965241835351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38185354368404591825820821 1789938486018965241835351)
                ·
                  refine ⟨2684907729028447862753027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789938486018965241835351 2684907729028447862753027)
                  ·
                    refine ⟨4027361593542671794129541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2684907729028447862753027 4027361593542671794129541)
                    ·
                      refine ⟨755130298789250961399289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4027361593542671794129541 755130298789250961399289)
                      ·
                        rfl

theorem cell23_1470611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 1, 4].length) (baseStart_1470611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470611 prefixEnd_1470611 := by exact prefixLift 1470611
  have htrace : WordTrace (prefixWord ++ tailWord_1470611) baseStart_1470611 baseEnd_1470611 := by
    simpa [prefixWord, tailWord_1470611, baseEnd_1470611] using wordTrace_append hprefix tailTrace_1470611
  have hstable : (prefixWord ++ tailWord_1470611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470611).length < 2 ^ (prefixWord ++ tailWord_1470611).sum := by decide
  have hdescent : baseEnd_1470611 < baseStart_1470611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470621 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1470621 : Nat := 118140960795 + 1470621 * 2 ^ 59
def prefixEnd_1470621 : Nat := 4983230072969 + 3 ^ 40 * 1470621 * 2
def baseEnd_1470621 : Nat := 251711811198598640758081

theorem tailTrace_1470621 : CollatzResearch.WordTrace tailWord_1470621 prefixEnd_1470621 251711811198598640758081 := by
  unfold tailWord_1470621
  simp only [CollatzResearch.WordTrace]
  refine ⟨53637954405198753915875717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35758636270132502610583811 53637954405198753915875717)
  ·
    refine ⟨10057116450974766359226697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53637954405198753915875717 10057116450974766359226697)
    ·
      refine ⟨7542837338231074769420023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10057116450974766359226697 7542837338231074769420023)
      ·
        refine ⟨11314256007346612154130035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7542837338231074769420023 11314256007346612154130035)
        ·
          refine ⟨16971384011019918231195053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11314256007346612154130035 16971384011019918231195053)
          ·
            refine ⟨6364269004132469336698145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16971384011019918231195053 6364269004132469336698145)
            ·
              refine ⟨4773201753099352002523609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364269004132469336698145 4773201753099352002523609)
              ·
                refine ⟨3579901314824514001892707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4773201753099352002523609 3579901314824514001892707)
                ·
                  refine ⟨5369851972236771002839061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3579901314824514001892707 5369851972236771002839061)
                  ·
                    refine ⟨251711811198598640758081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5369851972236771002839061 251711811198598640758081)
                    ·
                      rfl

theorem cell23_1470621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1470621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470621 prefixEnd_1470621 := by exact prefixLift 1470621
  have htrace : WordTrace (prefixWord ++ tailWord_1470621) baseStart_1470621 baseEnd_1470621 := by
    simpa [prefixWord, tailWord_1470621, baseEnd_1470621] using wordTrace_append hprefix tailTrace_1470621
  have hstable : (prefixWord ++ tailWord_1470621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470621).length < 2 ^ (prefixWord ++ tailWord_1470621).sum := by decide
  have hdescent : baseEnd_1470621 < baseStart_1470621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470625 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 1, 5]
def baseStart_1470625 : Nat := 118140960795 + 1470625 * 2 ^ 59
def prefixEnd_1470625 : Nat := 4983230072969 + 3 ^ 40 * 1470625 * 2
def baseEnd_1470625 : Nat := 251712495839471302208075

theorem tailTrace_1470625 : CollatzResearch.WordTrace tailWord_1470625 prefixEnd_1470625 251712495839471302208075 := by
  unfold tailWord_1470625
  simp only [CollatzResearch.WordTrace]
  refine ⟨53638100297184262599021329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35758733531456175066014219 53638100297184262599021329)
  ·
    refine ⟨40228575222888196949265997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53638100297184262599021329 40228575222888196949265997)
    ·
      refine ⟨15085715708583073855974749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40228575222888196949265997 15085715708583073855974749)
      ·
        refine ⟨5657143390718652695990531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15085715708583073855974749 5657143390718652695990531)
        ·
          refine ⟨8485715086077979043985797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5657143390718652695990531 8485715086077979043985797)
          ·
            refine ⟨1591071578639621070747337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8485715086077979043985797 1591071578639621070747337)
            ·
              refine ⟨1193303683979715803060503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591071578639621070747337 1193303683979715803060503)
              ·
                refine ⟨1789955525969573704590755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193303683979715803060503 1789955525969573704590755)
                ·
                  refine ⟨2684933288954360556886133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1789955525969573704590755 2684933288954360556886133)
                  ·
                    refine ⟨251712495839471302208075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2684933288954360556886133 251712495839471302208075)
                    ·
                      rfl

theorem cell23_1470625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_1470625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470625 prefixEnd_1470625 := by exact prefixLift 1470625
  have htrace : WordTrace (prefixWord ++ tailWord_1470625) baseStart_1470625 baseEnd_1470625 := by
    simpa [prefixWord, tailWord_1470625, baseEnd_1470625] using wordTrace_append hprefix tailTrace_1470625
  have hstable : (prefixWord ++ tailWord_1470625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470625).length < 2 ^ (prefixWord ++ tailWord_1470625).sum := by decide
  have hdescent : baseEnd_1470625 < baseStart_1470625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470668 : List Nat := [2, 2, 1, 6, 1, 1, 1, 9]
def baseStart_1470668 : Nat := 118140960795 + 1470668 * 2 ^ 59
def prefixEnd_1470668 : Nat := 4983230072969 + 3 ^ 40 * 1470668 * 2
def baseEnd_1470668 : Nat := 27968872858761379199501

theorem tailTrace_1470668 : CollatzResearch.WordTrace tailWord_1470668 prefixEnd_1470668 27968872858761379199501 := by
  unfold tailWord_1470668
  simp only [CollatzResearch.WordTrace]
  refine ⟨26819834318014240471418329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35759779090685653961891105 26819834318014240471418329)
  ·
    refine ⟨20114875738510680353563747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26819834318014240471418329 20114875738510680353563747)
    ·
      refine ⟨30172313607766020530345621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20114875738510680353563747 30172313607766020530345621)
      ·
        refine ⟨1414327200364032212359951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 30172313607766020530345621 1414327200364032212359951)
        ·
          refine ⟨2121490800546048318539927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1414327200364032212359951 2121490800546048318539927)
          ·
            refine ⟨3182236200819072477809891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2121490800546048318539927 3182236200819072477809891)
            ·
              refine ⟨4773354301228608716714837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182236200819072477809891 4773354301228608716714837)
              ·
                refine ⟨27968872858761379199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4773354301228608716714837 27968872858761379199501)
                ·
                  rfl

theorem cell23_1470668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 9].length) (baseStart_1470668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470668 prefixEnd_1470668 := by exact prefixLift 1470668
  have htrace : WordTrace (prefixWord ++ tailWord_1470668) baseStart_1470668 baseEnd_1470668 := by
    simpa [prefixWord, tailWord_1470668, baseEnd_1470668] using wordTrace_append hprefix tailTrace_1470668
  have hstable : (prefixWord ++ tailWord_1470668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470668).length < 2 ^ (prefixWord ++ tailWord_1470668).sum := by decide
  have hdescent : baseEnd_1470668 < baseStart_1470668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470695 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1470695 : Nat := 118140960795 + 1470695 * 2 ^ 59
def prefixEnd_1470695 : Nat := 4983230072969 + 3 ^ 40 * 1470695 * 2
def baseEnd_1470695 : Nat := 755173431164228632748903

theorem tailTrace_1470695 : CollatzResearch.WordTrace tailWord_1470695 prefixEnd_1470695 755173431164228632748903 := by
  unfold tailWord_1470695
  simp only [CollatzResearch.WordTrace]
  refine ⟨53640653406930664554069539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35760435604620443036046359 53640653406930664554069539)
  ·
    refine ⟨80460980110395996831104309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53640653406930664554069539 80460980110395996831104309)
    ·
      refine ⟨7543216885349624702916029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80460980110395996831104309 7543216885349624702916029)
      ·
        refine ⟨2828706332006109263593511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7543216885349624702916029 2828706332006109263593511)
        ·
          refine ⟨4243059498009163895390267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2828706332006109263593511 4243059498009163895390267)
          ·
            refine ⟨6364589247013745843085401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243059498009163895390267 6364589247013745843085401)
            ·
              refine ⟨4773441935260309382314051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6364589247013745843085401 4773441935260309382314051)
              ·
                refine ⟨7160162902890464073471077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773441935260309382314051 7160162902890464073471077)
                ·
                  refine ⟨1342530544291962013775827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7160162902890464073471077 1342530544291962013775827)
                  ·
                    refine ⟨2013795816437943020663741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1342530544291962013775827 2013795816437943020663741)
                    ·
                      refine ⟨755173431164228632748903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2013795816437943020663741 755173431164228632748903)
                      ·
                        rfl

theorem cell23_1470695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1470695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470695 prefixEnd_1470695 := by exact prefixLift 1470695
  have htrace : WordTrace (prefixWord ++ tailWord_1470695) baseStart_1470695 baseEnd_1470695 := by
    simpa [prefixWord, tailWord_1470695, baseEnd_1470695] using wordTrace_append hprefix tailTrace_1470695
  have hstable : (prefixWord ++ tailWord_1470695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470695).length < 2 ^ (prefixWord ++ tailWord_1470695).sum := by decide
  have hdescent : baseEnd_1470695 < baseStart_1470695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470721 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1470721 : Nat := 118140960795 + 1470721 * 2 ^ 59
def prefixEnd_1470721 : Nat := 4983230072969 + 3 ^ 40 * 1470721 * 2
def baseEnd_1470721 : Nat := 755186781661245531023783

theorem tailTrace_1470721 : CollatzResearch.WordTrace tailWord_1470721 prefixEnd_1470721 755186781661245531023783 := by
  unfold tailWord_1470721
  simp only [CollatzResearch.WordTrace]
  refine ⟨53641601704836470994516017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35761067803224313996344011 53641601704836470994516017)
  ·
    refine ⟨40231201278627353245887013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53641601704836470994516017 40231201278627353245887013)
    ·
      refine ⟨7543350239742628733603815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40231201278627353245887013 7543350239742628733603815)
      ·
        refine ⟨11315025359613943100405723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7543350239742628733603815 11315025359613943100405723)
        ·
          refine ⟨16972538039420914650608585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11315025359613943100405723 16972538039420914650608585)
          ·
            refine ⟨12729403529565685987956439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16972538039420914650608585 12729403529565685987956439)
            ·
              refine ⟨19094105294348528981934659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12729403529565685987956439 19094105294348528981934659)
              ·
                refine ⟨28641157941522793472901989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19094105294348528981934659 28641157941522793472901989)
                ·
                  refine ⟨5370217114035523776169123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28641157941522793472901989 5370217114035523776169123)
                  ·
                    refine ⟨8055325671053285664253685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5370217114035523776169123 8055325671053285664253685)
                    ·
                      refine ⟨755186781661245531023783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8055325671053285664253685 755186781661245531023783)
                      ·
                        rfl

theorem cell23_1470721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1470721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470721 prefixEnd_1470721 := by exact prefixLift 1470721
  have htrace : WordTrace (prefixWord ++ tailWord_1470721) baseStart_1470721 baseEnd_1470721 := by
    simpa [prefixWord, tailWord_1470721, baseEnd_1470721] using wordTrace_append hprefix tailTrace_1470721
  have hstable : (prefixWord ++ tailWord_1470721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470721).length < 2 ^ (prefixWord ++ tailWord_1470721).sum := by decide
  have hdescent : baseEnd_1470721 < baseStart_1470721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470722 : List Nat := [3, 4, 1, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_1470722 : Nat := 118140960795 + 1470722 * 2 ^ 59
def prefixEnd_1470722 : Nat := 4983230072969 + 3 ^ 40 * 1470722 * 2
def baseEnd_1470722 : Nat := 755187295141900027111279

theorem tailTrace_1470722 : CollatzResearch.WordTrace tailWord_1470722 prefixEnd_1470722 755187295141900027111279 := by
  unfold tailWord_1470722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13410409544458212041325605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35761092118555232110201613 13410409544458212041325605)
  ·
    refine ⟨2514451789585914757748551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13410409544458212041325605 2514451789585914757748551)
    ·
      refine ⟨3771677684378872136622827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2514451789585914757748551 3771677684378872136622827)
      ·
        refine ⟨5657516526568308204934241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3771677684378872136622827 5657516526568308204934241)
        ·
          refine ⟨4243137394926231153700681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5657516526568308204934241 4243137394926231153700681)
          ·
            refine ⟨3182353046194673365275511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243137394926231153700681 3182353046194673365275511)
            ·
              refine ⟨4773529569292010047913267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182353046194673365275511 4773529569292010047913267)
              ·
                refine ⟨7160294353938015071869901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4773529569292010047913267 7160294353938015071869901)
                ·
                  refine ⟨2685110382726755651951213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7160294353938015071869901 2685110382726755651951213)
                  ·
                    refine ⟨1006916393522533369481705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685110382726755651951213 1006916393522533369481705)
                    ·
                      refine ⟨755187295141900027111279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006916393522533369481705 755187295141900027111279)
                      ·
                        rfl

theorem cell23_1470722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_1470722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470722 prefixEnd_1470722 := by exact prefixLift 1470722
  have htrace : WordTrace (prefixWord ++ tailWord_1470722) baseStart_1470722 baseEnd_1470722 := by
    simpa [prefixWord, tailWord_1470722, baseEnd_1470722] using wordTrace_append hprefix tailTrace_1470722
  have hstable : (prefixWord ++ tailWord_1470722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470722).length < 2 ^ (prefixWord ++ tailWord_1470722).sum := by decide
  have hdescent : baseEnd_1470722 < baseStart_1470722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470752 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2]
def baseStart_1470752 : Nat := 118140960795 + 1470752 * 2 ^ 59
def prefixEnd_1470752 : Nat := 4983230072969 + 3 ^ 40 * 1470752 * 2
def baseEnd_1470752 : Nat := 755202699561534909736141

theorem tailTrace_1470752 : CollatzResearch.WordTrace tailWord_1470752 prefixEnd_1470752 755202699561534909736141 := by
  unfold tailWord_1470752
  simp only [CollatzResearch.WordTrace]
  refine ⟨26821366183862081644447255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35761821578482775525929673 26821366183862081644447255)
  ·
    refine ⟨40232049275793122466670883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26821366183862081644447255 40232049275793122466670883)
    ·
      refine ⟨60348073913689683700006325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40232049275793122466670883 60348073913689683700006325)
      ·
        refine ⟨5657631929408407846875593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60348073913689683700006325 5657631929408407846875593)
        ·
          refine ⟨4243223947056305885156695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5657631929408407846875593 4243223947056305885156695)
          ·
            refine ⟨6364835920584458827735043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4243223947056305885156695 6364835920584458827735043)
            ·
              refine ⟨9547253880876688241602565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6364835920584458827735043 9547253880876688241602565)
              ·
                refine ⟨1790110102664379045300481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9547253880876688241602565 1790110102664379045300481)
                ·
                  refine ⟨1342582576998284283975361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790110102664379045300481 1342582576998284283975361)
                  ·
                    refine ⟨1006936932748713212981521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1342582576998284283975361 1006936932748713212981521)
                    ·
                      refine ⟨755202699561534909736141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1006936932748713212981521 755202699561534909736141)
                      ·
                        rfl

theorem cell23_1470752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_1470752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470752 prefixEnd_1470752 := by exact prefixLift 1470752
  have htrace : WordTrace (prefixWord ++ tailWord_1470752) baseStart_1470752 baseEnd_1470752 := by
    simpa [prefixWord, tailWord_1470752, baseEnd_1470752] using wordTrace_append hprefix tailTrace_1470752
  have hstable : (prefixWord ++ tailWord_1470752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470752).length < 2 ^ (prefixWord ++ tailWord_1470752).sum := by decide
  have hdescent : baseEnd_1470752 < baseStart_1470752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470771 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 7]
def baseStart_1470771 : Nat := 118140960795 + 1470771 * 2 ^ 59
def prefixEnd_1470771 : Nat := 4983230072969 + 3 ^ 40 * 1470771 * 2
def baseEnd_1470771 : Nat := 251737485231323445132851

theorem tailTrace_1470771 : CollatzResearch.WordTrace tailWord_1470771 prefixEnd_1470771 251737485231323445132851 := by
  unfold tailWord_1470771
  simp only [CollatzResearch.WordTrace]
  refine ⟨53643425354655329533836167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35762283569770219689224111 53643425354655329533836167)
  ·
    refine ⟨80465138031982994300754251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53643425354655329533836167 80465138031982994300754251)
    ·
      refine ⟨120697707047974491451131377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80465138031982994300754251 120697707047974491451131377)
      ·
        refine ⟨90523280285980868588348533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120697707047974491451131377 90523280285980868588348533)
        ·
          refine ⟨8486557526810706430157675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90523280285980868588348533 8486557526810706430157675)
          ·
            refine ⟨12729836290216059645236513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8486557526810706430157675 12729836290216059645236513)
            ·
              refine ⟨9547377217662044733927385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12729836290216059645236513 9547377217662044733927385)
              ·
                refine ⟨7160532913246533550445539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9547377217662044733927385 7160532913246533550445539)
                ·
                  refine ⟨10740799369869800325668309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7160532913246533550445539 10740799369869800325668309)
                  ·
                    refine ⟨251737485231323445132851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10740799369869800325668309 251737485231323445132851)
                    ·
                      rfl

theorem cell23_1470771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 7].length) (baseStart_1470771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470771 prefixEnd_1470771 := by exact prefixLift 1470771
  have htrace : WordTrace (prefixWord ++ tailWord_1470771) baseStart_1470771 baseEnd_1470771 := by
    simpa [prefixWord, tailWord_1470771, baseEnd_1470771] using wordTrace_append hprefix tailTrace_1470771
  have hstable : (prefixWord ++ tailWord_1470771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470771).length < 2 ^ (prefixWord ++ tailWord_1470771).sum := by decide
  have hdescent : baseEnd_1470771 < baseStart_1470771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470862 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1470862 : Nat := 118140960795 + 1470862 * 2 ^ 59
def prefixEnd_1470862 : Nat := 4983230072969 + 3 ^ 40 * 1470862 * 2
def baseEnd_1470862 : Nat := 755259182433529479360635

theorem tailTrace_1470862 : CollatzResearch.WordTrace tailWord_1470862 prefixEnd_1470862 755259182433529479360635 := by
  unfold tailWord_1470862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6705843049665706509424855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35764496264883768050265893 6705843049665706509424855)
  ·
    refine ⟨10058764574498559764137283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6705843049665706509424855 10058764574498559764137283)
    ·
      refine ⟨15088146861747839646205925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10058764574498559764137283 15088146861747839646205925)
      ·
        refine ⟨2829027536577719933663611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15088146861747839646205925 2829027536577719933663611)
        ·
          refine ⟨4243541304866579900495417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2829027536577719933663611 4243541304866579900495417)
          ·
            refine ⟨3182655978649934925371563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4243541304866579900495417 3182655978649934925371563)
            ·
              refine ⟨4773983967974902388057345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3182655978649934925371563 4773983967974902388057345)
              ·
                refine ⟨3580487975981176791043009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4773983967974902388057345 3580487975981176791043009)
                ·
                  refine ⟨2685365981985882593282257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3580487975981176791043009 2685365981985882593282257)
                  ·
                    refine ⟨2014024486489411944961693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2685365981985882593282257 2014024486489411944961693)
                    ·
                      refine ⟨755259182433529479360635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2014024486489411944961693 755259182433529479360635)
                      ·
                        rfl

theorem cell23_1470862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1470862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470862 prefixEnd_1470862 := by exact prefixLift 1470862
  have htrace : WordTrace (prefixWord ++ tailWord_1470862) baseStart_1470862 baseEnd_1470862 := by
    simpa [prefixWord, tailWord_1470862, baseEnd_1470862] using wordTrace_append hprefix tailTrace_1470862
  have hstable : (prefixWord ++ tailWord_1470862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470862).length < 2 ^ (prefixWord ++ tailWord_1470862).sum := by decide
  have hdescent : baseEnd_1470862 < baseStart_1470862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470885 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_1470885 : Nat := 118140960795 + 1470885 * 2 ^ 59
def prefixEnd_1470885 : Nat := 4983230072969 + 3 ^ 40 * 1470885 * 2
def baseEnd_1470885 : Nat := 755270992488582889373029

theorem tailTrace_1470885 : CollatzResearch.WordTrace tailWord_1470885 prefixEnd_1470885 755270992488582889373029 := by
  unfold tailWord_1470885
  simp only [CollatzResearch.WordTrace]
  refine ⟨53647583276242327003486109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35765055517494884668990739 53647583276242327003486109)
  ·
    refine ⟨20117843728590872626307291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53647583276242327003486109 20117843728590872626307291)
    ·
      refine ⟨30176765592886308939460937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20117843728590872626307291 30176765592886308939460937)
      ·
        refine ⟨22632574194664731704595703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30176765592886308939460937 22632574194664731704595703)
        ·
          refine ⟨33948861291997097556893555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22632574194664731704595703 33948861291997097556893555)
          ·
            refine ⟨50923291937995646335340333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33948861291997097556893555 50923291937995646335340333)
            ·
              refine ⟨19096234476748367375752625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50923291937995646335340333 19096234476748367375752625)
              ·
                refine ⟨14322175857561275531814469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19096234476748367375752625 14322175857561275531814469)
                ·
                  refine ⟨2685407973292739162215213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14322175857561275531814469 2685407973292739162215213)
                  ·
                    refine ⟨1007027989984777185830705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685407973292739162215213 1007027989984777185830705)
                    ·
                      refine ⟨755270992488582889373029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007027989984777185830705 755270992488582889373029)
                      ·
                        rfl

theorem cell23_1470885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_1470885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470885 prefixEnd_1470885 := by exact prefixLift 1470885
  have htrace : WordTrace (prefixWord ++ tailWord_1470885) baseStart_1470885 baseEnd_1470885 := by
    simpa [prefixWord, tailWord_1470885, baseEnd_1470885] using wordTrace_append hprefix tailTrace_1470885
  have hstable : (prefixWord ++ tailWord_1470885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470885).length < 2 ^ (prefixWord ++ tailWord_1470885).sum := by decide
  have hdescent : baseEnd_1470885 < baseStart_1470885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470891 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 12]
def baseStart_1470891 : Nat := 118140960795 + 1470891 * 2 ^ 59
def prefixEnd_1470891 : Nat := 4983230072969 + 3 ^ 40 * 1470891 * 2
def baseEnd_1470891 : Nat := 251758024457503288632667

theorem tailTrace_1470891 : CollatzResearch.WordTrace tailWord_1470891 prefixEnd_1470891 251758024457503288632667 := by
  unfold tailWord_1470891
  simp only [CollatzResearch.WordTrace]
  refine ⟨53647802114220590028204527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35765201409480393352136351 53647802114220590028204527)
  ·
    refine ⟨80471703171330885042306791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53647802114220590028204527 80471703171330885042306791)
    ·
      refine ⟨120707554756996327563460187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80471703171330885042306791 120707554756996327563460187)
      ·
        refine ⟨181061332135494491345190281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120707554756996327563460187 181061332135494491345190281)
        ·
          refine ⟨135795999101620868508892711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181061332135494491345190281 135795999101620868508892711)
          ·
            refine ⟨203693998652431302763339067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135795999101620868508892711 203693998652431302763339067)
            ·
              refine ⟨305540997978646954145008601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203693998652431302763339067 305540997978646954145008601)
              ·
                refine ⟨229155748483985215608756451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305540997978646954145008601 229155748483985215608756451)
                ·
                  refine ⟨343733622725977823413134677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 229155748483985215608756451 343733622725977823413134677)
                  ·
                    refine ⟨251758024457503288632667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 343733622725977823413134677 251758024457503288632667)
                    ·
                      rfl

theorem cell23_1470891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 12].length) (baseStart_1470891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470891 prefixEnd_1470891 := by exact prefixLift 1470891
  have htrace : WordTrace (prefixWord ++ tailWord_1470891) baseStart_1470891 baseEnd_1470891 := by
    simpa [prefixWord, tailWord_1470891, baseEnd_1470891] using wordTrace_append hprefix tailTrace_1470891
  have hstable : (prefixWord ++ tailWord_1470891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470891).length < 2 ^ (prefixWord ++ tailWord_1470891).sum := by decide
  have hdescent : baseEnd_1470891 < baseStart_1470891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1470945 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_1470945 : Nat := 118140960795 + 1470945 * 2 ^ 59
def prefixEnd_1470945 : Nat := 4983230072969 + 3 ^ 40 * 1470945 * 2
def baseEnd_1470945 : Nat := 755301801327852654622753

theorem tailTrace_1470945 : CollatzResearch.WordTrace tailWord_1470945 prefixEnd_1470945 755301801327852654622753 := by
  unfold tailWord_1470945
  simp only [CollatzResearch.WordTrace]
  refine ⟨53649771656024957250670289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35766514437349971500446859 53649771656024957250670289)
  ·
    refine ⟨40237328742018717938002717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53649771656024957250670289 40237328742018717938002717)
    ·
      refine ⟨15088998278257019226751019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40237328742018717938002717 15088998278257019226751019)
      ·
        refine ⟨22633497417385528840126529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15088998278257019226751019 22633497417385528840126529)
        ·
          refine ⟨16975123063039146630094897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22633497417385528840126529 16975123063039146630094897)
          ·
            refine ⟨12731342297279359972571173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16975123063039146630094897 12731342297279359972571173)
            ·
              refine ⟨2387126680739879994857095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12731342297279359972571173 2387126680739879994857095)
              ·
                refine ⟨3580690021109819992285643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387126680739879994857095 3580690021109819992285643)
                ·
                  refine ⟨5371035031664729988428465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3580690021109819992285643 5371035031664729988428465)
                  ·
                    refine ⟨4028276273748547491321349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5371035031664729988428465 4028276273748547491321349)
                    ·
                      refine ⟨755301801327852654622753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4028276273748547491321349 755301801327852654622753)
                      ·
                        rfl

theorem cell23_1470945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_1470945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1470945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1470945 prefixEnd_1470945 := by exact prefixLift 1470945
  have htrace : WordTrace (prefixWord ++ tailWord_1470945) baseStart_1470945 baseEnd_1470945 := by
    simpa [prefixWord, tailWord_1470945, baseEnd_1470945] using wordTrace_append hprefix tailTrace_1470945
  have hstable : (prefixWord ++ tailWord_1470945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1470945).length < 2 ^ (prefixWord ++ tailWord_1470945).sum := by decide
  have hdescent : baseEnd_1470945 < baseStart_1470945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1470945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471009 : List Nat := [1, 2, 3, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1471009 : Nat := 118140960795 + 1471009 * 2 ^ 59
def prefixEnd_1471009 : Nat := 4983230072969 + 3 ^ 40 * 1471009 * 2
def baseEnd_1471009 : Nat := 755334664089740404222459

theorem tailTrace_1471009 : CollatzResearch.WordTrace tailWord_1471009 prefixEnd_1471009 755334664089740404222459 := by
  unfold tailWord_1471009
  simp only [CollatzResearch.WordTrace]
  refine ⟨53652105927793096181000081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35768070618528730787333387 53652105927793096181000081)
  ·
    refine ⟨40239079445844822135750061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53652105927793096181000081 40239079445844822135750061)
    ·
      refine ⟨15089654792191808300906273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40239079445844822135750061 15089654792191808300906273)
      ·
        refine ⟨11317241094143856225679705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15089654792191808300906273 11317241094143856225679705)
        ·
          refine ⟨8487930820607892169259779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11317241094143856225679705 8487930820607892169259779)
          ·
            refine ⟨12731896230911838253889669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8487930820607892169259779 12731896230911838253889669)
            ·
              refine ⟨2387230543295969672604313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12731896230911838253889669 2387230543295969672604313)
              ·
                refine ⟨1790422907471977254453235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2387230543295969672604313 1790422907471977254453235)
                ·
                  refine ⟨2685634361207965881679853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790422907471977254453235 2685634361207965881679853)
                  ·
                    refine ⟨1007112885452987205629945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2685634361207965881679853 1007112885452987205629945)
                    ·
                      refine ⟨755334664089740404222459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007112885452987205629945 755334664089740404222459)
                      ·
                        rfl

theorem cell23_1471009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1471009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471009 prefixEnd_1471009 := by exact prefixLift 1471009
  have htrace : WordTrace (prefixWord ++ tailWord_1471009) baseStart_1471009 baseEnd_1471009 := by
    simpa [prefixWord, tailWord_1471009, baseEnd_1471009] using wordTrace_append hprefix tailTrace_1471009
  have hstable : (prefixWord ++ tailWord_1471009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471009).length < 2 ^ (prefixWord ++ tailWord_1471009).sum := by decide
  have hdescent : baseEnd_1471009 < baseStart_1471009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471039 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 2, 2, 2]
def baseStart_1471039 : Nat := 118140960795 + 1471039 * 2 ^ 59
def prefixEnd_1471039 : Nat := 4983230072969 + 3 ^ 40 * 1471039 * 2
def baseEnd_1471039 : Nat := 755350068509375286847321

theorem tailTrace_1471039 : CollatzResearch.WordTrace tailWord_1471039 prefixEnd_1471039 755350068509375286847321 := by
  unfold tailWord_1471039
  simp only [CollatzResearch.WordTrace]
  refine ⟨53653200117684411304592171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35768800078456274203061447 53653200117684411304592171)
  ·
    refine ⟨80479800176526616956888257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53653200117684411304592171 80479800176526616956888257)
    ·
      refine ⟨60359850132394962717666193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80479800176526616956888257 60359850132394962717666193)
      ·
        refine ⟨45269887599296222038249645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60359850132394962717666193 45269887599296222038249645)
        ·
          refine ⟨16976207849736083264343617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45269887599296222038249645 16976207849736083264343617)
          ·
            refine ⟨12732155887302062448257713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16976207849736083264343617 12732155887302062448257713)
            ·
              refine ⟨9549116915476546836193285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12732155887302062448257713 9549116915476546836193285)
              ·
                refine ⟨1790459421651852531786241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9549116915476546836193285 1790459421651852531786241)
                ·
                  refine ⟨1342844566238889398839681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790459421651852531786241 1342844566238889398839681)
                  ·
                    refine ⟨1007133424679167049129761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1342844566238889398839681 1007133424679167049129761)
                    ·
                      refine ⟨755350068509375286847321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007133424679167049129761 755350068509375286847321)
                      ·
                        rfl

theorem cell23_1471039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 2, 2, 2].length) (baseStart_1471039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471039 prefixEnd_1471039 := by exact prefixLift 1471039
  have htrace : WordTrace (prefixWord ++ tailWord_1471039) baseStart_1471039 baseEnd_1471039 := by
    simpa [prefixWord, tailWord_1471039, baseEnd_1471039] using wordTrace_append hprefix tailTrace_1471039
  have hstable : (prefixWord ++ tailWord_1471039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471039).length < 2 ^ (prefixWord ++ tailWord_1471039).sum := by decide
  have hdescent : baseEnd_1471039 < baseStart_1471039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471045 : List Nat := [1, 3, 1, 1, 1, 5, 3, 1, 7]
def baseStart_1471045 : Nat := 118140960795 + 1471045 * 2 ^ 59
def prefixEnd_1471045 : Nat := 4983230072969 + 3 ^ 40 * 1471045 * 2
def baseEnd_1471045 : Nat := 83928127710366918152477

theorem tailTrace_1471045 : CollatzResearch.WordTrace tailWord_1471045 prefixEnd_1471045 83928127710366918152477 := by
  unfold tailWord_1471045
  simp only [CollatzResearch.WordTrace]
  refine ⟨53653418955662674329310589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35768945970441782886207059 53653418955662674329310589)
  ·
    refine ⟨20120032108373502873491471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53653418955662674329310589 20120032108373502873491471)
    ·
      refine ⟨30180048162560254310237207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20120032108373502873491471 30180048162560254310237207)
      ·
        refine ⟨45270072243840381465355811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30180048162560254310237207 45270072243840381465355811)
        ·
          refine ⟨67905108365760572198033717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45270072243840381465355811 67905108365760572198033717)
          ·
            refine ⟨6366103909290053643565661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67905108365760572198033717 6366103909290053643565661)
            ·
              refine ⟨2387288965983770116337123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6366103909290053643565661 2387288965983770116337123)
              ·
                refine ⟨3580933448975655174505685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387288965983770116337123 3580933448975655174505685)
                ·
                  refine ⟨83928127710366918152477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3580933448975655174505685 83928127710366918152477)
                  ·
                    rfl

theorem cell23_1471045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 7].length) (baseStart_1471045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471045 prefixEnd_1471045 := by exact prefixLift 1471045
  have htrace : WordTrace (prefixWord ++ tailWord_1471045) baseStart_1471045 baseEnd_1471045 := by
    simpa [prefixWord, tailWord_1471045, baseEnd_1471045] using wordTrace_append hprefix tailTrace_1471045
  have hstable : (prefixWord ++ tailWord_1471045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471045).length < 2 ^ (prefixWord ++ tailWord_1471045).sum := by decide
  have hdescent : baseEnd_1471045 < baseStart_1471045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471055 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3]
def baseStart_1471055 : Nat := 118140960795 + 1471055 * 2 ^ 59
def prefixEnd_1471055 : Nat := 4983230072969 + 3 ^ 40 * 1471055 * 2
def baseEnd_1471055 : Nat := 755358284199847224247247

theorem tailTrace_1471055 : CollatzResearch.WordTrace tailWord_1471055 prefixEnd_1471055 755358284199847224247247 := by
  unfold tailWord_1471055
  simp only [CollatzResearch.WordTrace]
  refine ⟨53653783685626446037174619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35769189123750964024783079 53653783685626446037174619)
  ·
    refine ⟨80480675528439669055761929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53653783685626446037174619 80480675528439669055761929)
    ·
      refine ⟨60360506646329751791821447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80480675528439669055761929 60360506646329751791821447)
      ·
        refine ⟨90540759969494627687732171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60360506646329751791821447 90540759969494627687732171)
        ·
          refine ⟨135811139954241941531598257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90540759969494627687732171 135811139954241941531598257)
          ·
            refine ⟨101858354965681456148698693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135811139954241941531598257 101858354965681456148698693)
            ·
              refine ⟨19098441556065273027881005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101858354965681456148698693 19098441556065273027881005)
              ·
                refine ⟨7161915583524477385455377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19098441556065273027881005 7161915583524477385455377)
                ·
                  refine ⟨5371436687643358039091533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7161915583524477385455377 5371436687643358039091533)
                  ·
                    refine ⟨2014288757866259264659325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5371436687643358039091533 2014288757866259264659325)
                    ·
                      refine ⟨755358284199847224247247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2014288757866259264659325 755358284199847224247247)
                      ·
                        rfl

theorem cell23_1471055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_1471055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471055 prefixEnd_1471055 := by exact prefixLift 1471055
  have htrace : WordTrace (prefixWord ++ tailWord_1471055) baseStart_1471055 baseEnd_1471055 := by
    simpa [prefixWord, tailWord_1471055, baseEnd_1471055] using wordTrace_append hprefix tailTrace_1471055
  have hstable : (prefixWord ++ tailWord_1471055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471055).length < 2 ^ (prefixWord ++ tailWord_1471055).sum := by decide
  have hdescent : baseEnd_1471055 < baseStart_1471055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471155 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6]
def baseStart_1471155 : Nat := 118140960795 + 1471155 * 2 ^ 59
def prefixEnd_1471155 : Nat := 4983230072969 + 3 ^ 40 * 1471155 * 2
def baseEnd_1471155 : Nat := 755409632265296832996787

theorem tailTrace_1471155 : CollatzResearch.WordTrace tailWord_1471155 prefixEnd_1471155 755409632265296832996787 := by
  unfold tailWord_1471155
  simp only [CollatzResearch.WordTrace]
  refine ⟨53657430985264163115814919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35771620656842775410543279 53657430985264163115814919)
  ·
    refine ⟨80486146477896244673722379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53657430985264163115814919 80486146477896244673722379)
    ·
      refine ⟨120729219716844367010583569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80486146477896244673722379 120729219716844367010583569)
      ·
        refine ⟨90546914787633275257937677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120729219716844367010583569 90546914787633275257937677)
        ·
          refine ⟨33955093045362478221726629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90546914787633275257937677 33955093045362478221726629)
          ·
            refine ⟨6366579946005464666573743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33955093045362478221726629 6366579946005464666573743)
            ·
              refine ⟨9549869919008196999860615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6366579946005464666573743 9549869919008196999860615)
              ·
                refine ⟨14324804878512295499790923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9549869919008196999860615 14324804878512295499790923)
                ·
                  refine ⟨21487207317768443249686385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14324804878512295499790923 21487207317768443249686385)
                  ·
                    refine ⟨16115405488326332437264789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21487207317768443249686385 16115405488326332437264789)
                    ·
                      refine ⟨755409632265296832996787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16115405488326332437264789 755409632265296832996787)
                      ·
                        rfl

theorem cell23_1471155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 6].length) (baseStart_1471155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471155 prefixEnd_1471155 := by exact prefixLift 1471155
  have htrace : WordTrace (prefixWord ++ tailWord_1471155) baseStart_1471155 baseEnd_1471155 := by
    simpa [prefixWord, tailWord_1471155, baseEnd_1471155] using wordTrace_append hprefix tailTrace_1471155
  have hstable : (prefixWord ++ tailWord_1471155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471155).length < 2 ^ (prefixWord ++ tailWord_1471155).sum := by decide
  have hdescent : baseEnd_1471155 < baseStart_1471155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471220 : List Nat := [2, 6, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1471220 : Nat := 118140960795 + 1471220 * 2 ^ 59
def prefixEnd_1471220 : Nat := 4983230072969 + 3 ^ 40 * 1471220 * 2
def baseEnd_1471220 : Nat := 83938112056426564298221

theorem tailTrace_1471220 : CollatzResearch.WordTrace tailWord_1471220 prefixEnd_1471220 83938112056426564298221 := by
  unfold tailWord_1471220
  simp only [CollatzResearch.WordTrace]
  refine ⟨26829900865014339608465557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35773201153352452811287409 26829900865014339608465557)
  ·
    refine ⟨1257651603047547169146823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26829900865014339608465557 1257651603047547169146823)
    ·
      refine ⟨1886477404571320753720235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1257651603047547169146823 1886477404571320753720235)
      ·
        refine ⟨2829716106856981130580353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886477404571320753720235 2829716106856981130580353)
        ·
          refine ⟨2122287080142735847935265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2829716106856981130580353 2122287080142735847935265)
          ·
            refine ⟨1591715310107051885951449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122287080142735847935265 1591715310107051885951449)
            ·
              refine ⟨1193786482580288914463587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1591715310107051885951449 1193786482580288914463587)
              ·
                refine ⟨1790679723870433371695381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193786482580288914463587 1790679723870433371695381)
                ·
                  refine ⟨83938112056426564298221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1790679723870433371695381 83938112056426564298221)
                  ·
                    rfl

theorem cell23_1471220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1471220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471220 prefixEnd_1471220 := by exact prefixLift 1471220
  have htrace : WordTrace (prefixWord ++ tailWord_1471220) baseStart_1471220 baseEnd_1471220 := by
    simpa [prefixWord, tailWord_1471220, baseEnd_1471220] using wordTrace_append hprefix tailTrace_1471220
  have hstable : (prefixWord ++ tailWord_1471220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471220).length < 2 ^ (prefixWord ++ tailWord_1471220).sum := by decide
  have hdescent : baseEnd_1471220 < baseStart_1471220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471229 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 2, 4]
def baseStart_1471229 : Nat := 118140960795 + 1471229 * 2 ^ 59
def prefixEnd_1471229 : Nat := 4983230072969 + 3 ^ 40 * 1471229 * 2
def baseEnd_1471229 : Nat := 251815876611243181157149

theorem tailTrace_1471229 : CollatzResearch.WordTrace tailWord_1471229 prefixEnd_1471229 251815876611243181157149 := by
  unfold tailWord_1471229
  simp only [CollatzResearch.WordTrace]
  refine ⟨53660129986996073754008741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35773419991330715836005827 53660129986996073754008741)
  ·
    refine ⟨10061274372561763828876639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53660129986996073754008741 10061274372561763828876639)
    ·
      refine ⟨15091911558842645743314959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10061274372561763828876639 15091911558842645743314959)
      ·
        refine ⟨22637867338263968614972439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15091911558842645743314959 22637867338263968614972439)
        ·
          refine ⟨33956801007395952922458659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22637867338263968614972439 33956801007395952922458659)
          ·
            refine ⟨50935201511093929383687989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33956801007395952922458659 50935201511093929383687989)
            ·
              refine ⟨4775175141665055879720749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50935201511093929383687989 4775175141665055879720749)
              ·
                refine ⟨1790690678124395954895281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4775175141665055879720749 1790690678124395954895281)
                ·
                  refine ⟨1343018008593296966171461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1790690678124395954895281 1343018008593296966171461)
                  ·
                    refine ⟨251815876611243181157149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1343018008593296966171461 251815876611243181157149)
                    ·
                      rfl

theorem cell23_1471229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 4].length) (baseStart_1471229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471229 prefixEnd_1471229 := by exact prefixLift 1471229
  have htrace : WordTrace (prefixWord ++ tailWord_1471229) baseStart_1471229 baseEnd_1471229 := by
    simpa [prefixWord, tailWord_1471229, baseEnd_1471229] using wordTrace_append hprefix tailTrace_1471229
  have hstable : (prefixWord ++ tailWord_1471229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471229).length < 2 ^ (prefixWord ++ tailWord_1471229).sum := by decide
  have hdescent : baseEnd_1471229 < baseStart_1471229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471236 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_1471236 : Nat := 118140960795 + 1471236 * 2 ^ 59
def prefixEnd_1471236 : Nat := 4983230072969 + 3 ^ 40 * 1471236 * 2
def baseEnd_1471236 : Nat := 755451224198311016083915

theorem tailTrace_1471236 : CollatzResearch.WordTrace tailWord_1471236 prefixEnd_1471236 755451224198311016083915 := by
  unfold tailWord_1471236
  simp only [CollatzResearch.WordTrace]
  refine ⟨26830192648985356974756781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35773590198647142633009041 26830192648985356974756781)
  ·
    refine ⟨10061322243369508865533793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26830192648985356974756781 10061322243369508865533793)
    ·
      refine ⟨7545991682527131649150345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10061322243369508865533793 7545991682527131649150345)
      ·
        refine ⟨5659493761895348736862759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7545991682527131649150345 5659493761895348736862759)
        ·
          refine ⟨8489240642843023105294139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659493761895348736862759 8489240642843023105294139)
          ·
            refine ⟨12733860964264534657941209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8489240642843023105294139 12733860964264534657941209)
            ·
              refine ⟨9550395723198400993455907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12733860964264534657941209 9550395723198400993455907)
              ·
                refine ⟨14325593584797601490183861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9550395723198400993455907 14325593584797601490183861)
                ·
                  refine ⟨1343024398574775139704737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14325593584797601490183861 1343024398574775139704737)
                  ·
                    refine ⟨1007268298931081354778553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343024398574775139704737 1007268298931081354778553)
                    ·
                      refine ⟨755451224198311016083915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007268298931081354778553 755451224198311016083915)
                      ·
                        rfl

theorem cell23_1471236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_1471236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471236 prefixEnd_1471236 := by exact prefixLift 1471236
  have htrace : WordTrace (prefixWord ++ tailWord_1471236) baseStart_1471236 baseEnd_1471236 := by
    simpa [prefixWord, tailWord_1471236, baseEnd_1471236] using wordTrace_append hprefix tailTrace_1471236
  have hstable : (prefixWord ++ tailWord_1471236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471236).length < 2 ^ (prefixWord ++ tailWord_1471236).sum := by decide
  have hdescent : baseEnd_1471236 < baseStart_1471236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471253 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_1471253 : Nat := 118140960795 + 1471253 * 2 ^ 59
def prefixEnd_1471253 : Nat := 4983230072969 + 3 ^ 40 * 1471253 * 2
def baseEnd_1471253 : Nat := 755459953369437449571337

theorem tailTrace_1471253 : CollatzResearch.WordTrace tailWord_1471253 prefixEnd_1471253 755459953369437449571337 := by
  unfold tailWord_1471253
  simp only [CollatzResearch.WordTrace]
  refine ⟨53661005338909125852882413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35774003559272750568588275 53661005338909125852882413)
  ·
    refine ⟨20122877002090922194830905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53661005338909125852882413 20122877002090922194830905)
    ·
      refine ⟨15092157751568191646123179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20122877002090922194830905 15092157751568191646123179)
      ·
        refine ⟨22638236627352287469184769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15092157751568191646123179 22638236627352287469184769)
        ·
          refine ⟨16978677470514215601888577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22638236627352287469184769 16978677470514215601888577)
          ·
            refine ⟨12734008102885661701416433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16978677470514215601888577 12734008102885661701416433)
            ·
              refine ⟨9550506077164246276062325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12734008102885661701416433 9550506077164246276062325)
              ·
                refine ⟨895359944734148088380843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9550506077164246276062325 895359944734148088380843)
                ·
                  refine ⟨1343039917101222132571265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895359944734148088380843 1343039917101222132571265)
                  ·
                    refine ⟨1007279937825916599428449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343039917101222132571265 1007279937825916599428449)
                    ·
                      refine ⟨755459953369437449571337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007279937825916599428449 755459953369437449571337)
                      ·
                        rfl

theorem cell23_1471253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_1471253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471253 prefixEnd_1471253 := by exact prefixLift 1471253
  have htrace : WordTrace (prefixWord ++ tailWord_1471253) baseStart_1471253 baseEnd_1471253 := by
    simpa [prefixWord, tailWord_1471253, baseEnd_1471253] using wordTrace_append hprefix tailTrace_1471253
  have hstable : (prefixWord ++ tailWord_1471253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471253).length < 2 ^ (prefixWord ++ tailWord_1471253).sum := by decide
  have hdescent : baseEnd_1471253 < baseStart_1471253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471272 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1471272 : Nat := 118140960795 + 1471272 * 2 ^ 59
def prefixEnd_1471272 : Nat := 4983230072969 + 3 ^ 40 * 1471272 * 2
def baseEnd_1471272 : Nat := 251823236500624291744583

theorem tailTrace_1471272 : CollatzResearch.WordTrace tailWord_1471272 prefixEnd_1471272 251823236500624291744583 := by
  unfold tailWord_1471272
  simp only [CollatzResearch.WordTrace]
  refine ⟨26830849162920146048912035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35774465550560194731882713 26830849162920146048912035)
  ·
    refine ⟨40246273744380219073368053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26830849162920146048912035 40246273744380219073368053)
    ·
      refine ⟨3773088163535645538128255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40246273744380219073368053 3773088163535645538128255)
      ·
        refine ⟨5659632245303468307192383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773088163535645538128255 5659632245303468307192383)
        ·
          refine ⟨8489448367955202460788575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659632245303468307192383 8489448367955202460788575)
          ·
            refine ⟨12734172551932803691182863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8489448367955202460788575 12734172551932803691182863)
            ·
              refine ⟨19101258827899205536774295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12734172551932803691182863 19101258827899205536774295)
              ·
                refine ⟨28651888241848808305161443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19101258827899205536774295 28651888241848808305161443)
                ·
                  refine ⟨42977832362773212457742165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28651888241848808305161443 42977832362773212457742165)
                  ·
                    refine ⟨251823236500624291744583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42977832362773212457742165 251823236500624291744583)
                    ·
                      rfl

theorem cell23_1471272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1471272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471272 prefixEnd_1471272 := by exact prefixLift 1471272
  have htrace : WordTrace (prefixWord ++ tailWord_1471272) baseStart_1471272 baseEnd_1471272 := by
    simpa [prefixWord, tailWord_1471272, baseEnd_1471272] using wordTrace_append hprefix tailTrace_1471272
  have hstable : (prefixWord ++ tailWord_1471272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471272).length < 2 ^ (prefixWord ++ tailWord_1471272).sum := by decide
  have hdescent : baseEnd_1471272 < baseStart_1471272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471292 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1471292 : Nat := 118140960795 + 1471292 * 2 ^ 59
def prefixEnd_1471292 : Nat := 4983230072969 + 3 ^ 40 * 1471292 * 2
def baseEnd_1471292 : Nat := 755479979114962796983657

theorem tailTrace_1471292 : CollatzResearch.WordTrace tailWord_1471292 prefixEnd_1471292 755479979114962796983657 := by
  unfold tailWord_1471292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26831213892883917756776065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35774951857178557009034753 26831213892883917756776065)
  ·
    refine ⟨20123410419662938317582049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26831213892883917756776065 20123410419662938317582049)
    ·
      refine ⟨15092557814747203738186537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20123410419662938317582049 15092557814747203738186537)
      ·
        refine ⟨11319418361060402803639903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15092557814747203738186537 11319418361060402803639903)
        ·
          refine ⟨16979127541590604205459855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11319418361060402803639903 16979127541590604205459855)
          ·
            refine ⟨25468691312385906308189783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16979127541590604205459855 25468691312385906308189783)
            ·
              refine ⟨38203036968578859462284675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25468691312385906308189783 38203036968578859462284675)
              ·
                refine ⟨57304555452868289193427013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38203036968578859462284675 57304555452868289193427013)
                ·
                  refine ⟨10744604147412804223767565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57304555452868289193427013 10744604147412804223767565)
                  ·
                    refine ⟨4029226555279801583912837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10744604147412804223767565 4029226555279801583912837)
                    ·
                      refine ⟨755479979114962796983657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4029226555279801583912837 755479979114962796983657)
                      ·
                        rfl

theorem cell23_1471292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1471292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471292 prefixEnd_1471292 := by exact prefixLift 1471292
  have htrace : WordTrace (prefixWord ++ tailWord_1471292) baseStart_1471292 baseEnd_1471292 := by
    simpa [prefixWord, tailWord_1471292, baseEnd_1471292] using wordTrace_append hprefix tailTrace_1471292
  have hstable : (prefixWord ++ tailWord_1471292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471292).length < 2 ^ (prefixWord ++ tailWord_1471292).sum := by decide
  have hdescent : baseEnd_1471292 < baseStart_1471292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471312 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5]
def baseStart_1471312 : Nat := 118140960795 + 1471312 * 2 ^ 59
def prefixEnd_1471312 : Nat := 4983230072969 + 3 ^ 40 * 1471312 * 2
def baseEnd_1471312 : Nat := 755490248728052718733565

theorem tailTrace_1471312 : CollatzResearch.WordTrace tailWord_1471312 prefixEnd_1471312 755490248728052718733565 := by
  unfold tailWord_1471312
  simp only [CollatzResearch.WordTrace]
  refine ⟨26831578622847689464640095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35775438163796919286186793 26831578622847689464640095)
  ·
    refine ⟨40247367934271534196960143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26831578622847689464640095 40247367934271534196960143)
    ·
      refine ⟨60371051901407301295440215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40247367934271534196960143 60371051901407301295440215)
      ·
        refine ⟨90556577852110951943160323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60371051901407301295440215 90556577852110951943160323)
        ·
          refine ⟨135834866778166427914740485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90556577852110951943160323 135834866778166427914740485)
          ·
            refine ⟨25469037520906205234013841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135834866778166427914740485 25469037520906205234013841)
            ·
              refine ⟨19101778140679653925510381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25469037520906205234013841 19101778140679653925510381)
              ·
                refine ⟨7163166802754870222066393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19101778140679653925510381 7163166802754870222066393)
                ·
                  refine ⟨5372375102066152666549795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7163166802754870222066393 5372375102066152666549795)
                  ·
                    refine ⟨8058562653099228999824693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5372375102066152666549795 8058562653099228999824693)
                    ·
                      refine ⟨755490248728052718733565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8058562653099228999824693 755490248728052718733565)
                      ·
                        rfl

theorem cell23_1471312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 5].length) (baseStart_1471312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471312 prefixEnd_1471312 := by exact prefixLift 1471312
  have htrace : WordTrace (prefixWord ++ tailWord_1471312) baseStart_1471312 baseEnd_1471312 := by
    simpa [prefixWord, tailWord_1471312, baseEnd_1471312] using wordTrace_append hprefix tailTrace_1471312
  have hstable : (prefixWord ++ tailWord_1471312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471312).length < 2 ^ (prefixWord ++ tailWord_1471312).sum := by decide
  have hdescent : baseEnd_1471312 < baseStart_1471312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471313 : List Nat := [1, 2, 2, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_1471313 : Nat := 118140960795 + 1471313 * 2 ^ 59
def prefixEnd_1471313 : Nat := 4983230072969 + 3 ^ 40 * 1471313 * 2
def baseEnd_1471313 : Nat := 755490762208707214821061

theorem tailTrace_1471313 : CollatzResearch.WordTrace tailWord_1471313 prefixEnd_1471313 755490762208707214821061 := by
  unfold tailWord_1471313
  simp only [CollatzResearch.WordTrace]
  refine ⟨53663193718691756100066593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35775462479127837400044395 53663193718691756100066593)
  ·
    refine ⟨40247395289018817075049945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53663193718691756100066593 40247395289018817075049945)
    ·
      refine ⟨30185546466764112806287459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40247395289018817075049945 30185546466764112806287459)
      ·
        refine ⟨45278319700146169209431189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30185546466764112806287459 45278319700146169209431189)
        ·
          refine ⟨2122421235944351681692087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45278319700146169209431189 2122421235944351681692087)
          ·
            refine ⟨3183631853916527522538131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122421235944351681692087 3183631853916527522538131)
            ·
              refine ⟨4775447780874791283807197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3183631853916527522538131 4775447780874791283807197)
              ·
                refine ⟨1790792917828046731427699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4775447780874791283807197 1790792917828046731427699)
                ·
                  refine ⟨2686189376742070097141549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1790792917828046731427699 2686189376742070097141549)
                  ·
                    refine ⟨1007321016278276286428081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686189376742070097141549 1007321016278276286428081)
                    ·
                      refine ⟨755490762208707214821061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007321016278276286428081 755490762208707214821061)
                      ·
                        rfl

theorem cell23_1471313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_1471313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471313 prefixEnd_1471313 := by exact prefixLift 1471313
  have htrace : WordTrace (prefixWord ++ tailWord_1471313) baseStart_1471313 baseEnd_1471313 := by
    simpa [prefixWord, tailWord_1471313, baseEnd_1471313] using wordTrace_append hprefix tailTrace_1471313
  have hstable : (prefixWord ++ tailWord_1471313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471313).length < 2 ^ (prefixWord ++ tailWord_1471313).sum := by decide
  have hdescent : baseEnd_1471313 < baseStart_1471313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471349 : List Nat := [1, 3, 4, 1, 1, 2, 2, 2, 7]
def baseStart_1471349 : Nat := 118140960795 + 1471349 * 2 ^ 59
def prefixEnd_1471349 : Nat := 4983230072969 + 3 ^ 40 * 1471349 * 2
def baseEnd_1471349 : Nat := 83945471945807674885655

theorem tailTrace_1471349 : CollatzResearch.WordTrace tailWord_1471349 prefixEnd_1471349 83945471945807674885655 := by
  unfold tailWord_1471349
  simp only [CollatzResearch.WordTrace]
  refine ⟨53664506746561334248377101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35776337831040889498918067 53664506746561334248377101)
  ·
    refine ⟨20124190029960500343141413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53664506746561334248377101 20124190029960500343141413)
    ·
      refine ⟨3773285630617593814339015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20124190029960500343141413 3773285630617593814339015)
      ·
        refine ⟨5659928445926390721508523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3773285630617593814339015 5659928445926390721508523)
        ·
          refine ⟨8489892668889586082262785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5659928445926390721508523 8489892668889586082262785)
          ·
            refine ⟨6367419501667189561697089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8489892668889586082262785 6367419501667189561697089)
            ·
              refine ⟨4775564626250392171272817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6367419501667189561697089 4775564626250392171272817)
              ·
                refine ⟨3581673469687794128454613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4775564626250392171272817 3581673469687794128454613)
                ·
                  refine ⟨83945471945807674885655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3581673469687794128454613 83945471945807674885655)
                  ·
                    rfl

theorem cell23_1471349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 7].length) (baseStart_1471349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471349 prefixEnd_1471349 := by exact prefixLift 1471349
  have htrace : WordTrace (prefixWord ++ tailWord_1471349) baseStart_1471349 baseEnd_1471349 := by
    simpa [prefixWord, tailWord_1471349, baseEnd_1471349] using wordTrace_append hprefix tailTrace_1471349
  have hstable : (prefixWord ++ tailWord_1471349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471349).length < 2 ^ (prefixWord ++ tailWord_1471349).sum := by decide
  have hdescent : baseEnd_1471349 < baseStart_1471349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471389 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1471389 : Nat := 118140960795 + 1471389 * 2 ^ 59
def prefixEnd_1471389 : Nat := 4983230072969 + 3 ^ 40 * 1471389 * 2
def baseEnd_1471389 : Nat := 755529786738448917470711

theorem tailTrace_1471389 : CollatzResearch.WordTrace tailWord_1471389 prefixEnd_1471389 755529786738448917470711 := by
  unfold tailWord_1471389
  simp only [CollatzResearch.WordTrace]
  refine ⟨53665965666416421079833221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35777310444277614053222147 53665965666416421079833221)
  ·
    refine ⟨10062368562453078952468729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53665965666416421079833221 10062368562453078952468729)
    ·
      refine ⟨7546776421839809214351547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10062368562453078952468729 7546776421839809214351547)
      ·
        refine ⟨11320164632759713821527321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7546776421839809214351547 11320164632759713821527321)
        ·
          refine ⟨8490123474569785366145491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11320164632759713821527321 8490123474569785366145491)
          ·
            refine ⟨12735185211854678049218237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490123474569785366145491 12735185211854678049218237)
            ·
              refine ⟨4775694454445504268456839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12735185211854678049218237 4775694454445504268456839)
              ·
                refine ⟨7163541681668256402685259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4775694454445504268456839 7163541681668256402685259)
                ·
                  refine ⟨10745312522502384604027889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7163541681668256402685259 10745312522502384604027889)
                  ·
                    refine ⟨8058984391876788453020917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10745312522502384604027889 8058984391876788453020917)
                    ·
                      refine ⟨755529786738448917470711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8058984391876788453020917 755529786738448917470711)
                      ·
                        rfl

theorem cell23_1471389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1471389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471389 prefixEnd_1471389 := by exact prefixLift 1471389
  have htrace : WordTrace (prefixWord ++ tailWord_1471389) baseStart_1471389 baseEnd_1471389 := by
    simpa [prefixWord, tailWord_1471389, baseEnd_1471389] using wordTrace_append hprefix tailTrace_1471389
  have hstable : (prefixWord ++ tailWord_1471389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471389).length < 2 ^ (prefixWord ++ tailWord_1471389).sum := by decide
  have hdescent : baseEnd_1471389 < baseStart_1471389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471416 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_1471416 : Nat := 118140960795 + 1471416 * 2 ^ 59
def prefixEnd_1471416 : Nat := 4983230072969 + 3 ^ 40 * 1471416 * 2
def baseEnd_1471416 : Nat := 755543650716120311833087

theorem tailTrace_1471416 : CollatzResearch.WordTrace tailWord_1471416 prefixEnd_1471416 755543650716120311833087 := by
  unfold tailWord_1471416
  simp only [CollatzResearch.WordTrace]
  refine ⟨26833475218659302345533051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35777966958212403127377401 26833475218659302345533051)
  ·
    refine ⟨40250212827988953518299577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26833475218659302345533051 40250212827988953518299577)
    ·
      refine ⟨30187659620991715138724683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40250212827988953518299577 30187659620991715138724683)
      ·
        refine ⟨45281489431487572708087025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30187659620991715138724683 45281489431487572708087025)
        ·
          refine ⟨33961117073615679531065269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45281489431487572708087025 33961117073615679531065269)
          ·
            refine ⟨3183854725651469956037369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33961117073615679531065269 3183854725651469956037369)
            ·
              refine ⟨2387891044238602467028027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3183854725651469956037369 2387891044238602467028027)
              ·
                refine ⟨3581836566357903700542041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387891044238602467028027 3581836566357903700542041)
                ·
                  refine ⟨2686377424768427775406531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581836566357903700542041 2686377424768427775406531)
                  ·
                    refine ⟨4029566137152641663109797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686377424768427775406531 4029566137152641663109797)
                    ·
                      refine ⟨755543650716120311833087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4029566137152641663109797 755543650716120311833087)
                      ·
                        rfl

theorem cell23_1471416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_1471416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471416 prefixEnd_1471416 := by exact prefixLift 1471416
  have htrace : WordTrace (prefixWord ++ tailWord_1471416) baseStart_1471416 baseEnd_1471416 := by
    simpa [prefixWord, tailWord_1471416, baseEnd_1471416] using wordTrace_append hprefix tailTrace_1471416
  have hstable : (prefixWord ++ tailWord_1471416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471416).length < 2 ^ (prefixWord ++ tailWord_1471416).sum := by decide
  have hdescent : baseEnd_1471416 < baseStart_1471416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471436 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1471436 : Nat := 118140960795 + 1471436 * 2 ^ 59
def prefixEnd_1471436 : Nat := 4983230072969 + 3 ^ 40 * 1471436 * 2
def baseEnd_1471436 : Nat := 755553920329210233582995

theorem tailTrace_1471436 : CollatzResearch.WordTrace tailWord_1471436 prefixEnd_1471436 755553920329210233582995 := by
  unfold tailWord_1471436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26833839948623074053397081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35778453264830765404529441 26833839948623074053397081)
  ·
    refine ⟨20125379961467305540047811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26833839948623074053397081 20125379961467305540047811)
    ·
      refine ⟨30188069942200958310071717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20125379961467305540047811 30188069942200958310071717)
      ·
        refine ⟨5660263114162679683138447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30188069942200958310071717 5660263114162679683138447)
        ·
          refine ⟨8490394671244019524707671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5660263114162679683138447 8490394671244019524707671)
          ·
            refine ⟨12735592006866029287061507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8490394671244019524707671 12735592006866029287061507)
            ·
              refine ⟨19103388010299043930592261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12735592006866029287061507 19103388010299043930592261)
              ·
                refine ⟨3581885251931070736986049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19103388010299043930592261 3581885251931070736986049)
                ·
                  refine ⟨2686413938948303052739537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581885251931070736986049 2686413938948303052739537)
                  ·
                    refine ⟨2014810454211227289554653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686413938948303052739537 2014810454211227289554653)
                    ·
                      refine ⟨755553920329210233582995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2014810454211227289554653 755553920329210233582995)
                      ·
                        rfl

theorem cell23_1471436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1471436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471436 prefixEnd_1471436 := by exact prefixLift 1471436
  have htrace : WordTrace (prefixWord ++ tailWord_1471436) baseStart_1471436 baseEnd_1471436 := by
    simpa [prefixWord, tailWord_1471436, baseEnd_1471436] using wordTrace_append hprefix tailTrace_1471436
  have hstable : (prefixWord ++ tailWord_1471436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471436).length < 2 ^ (prefixWord ++ tailWord_1471436).sum := by decide
  have hdescent : baseEnd_1471436 < baseStart_1471436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471439 : List Nat := [1, 1, 2, 1, 1, 6, 1, 4, 6]
def baseStart_1471439 : Nat := 118140960795 + 1471439 * 2 ^ 59
def prefixEnd_1471439 : Nat := 4983230072969 + 3 ^ 40 * 1471439 * 2
def baseEnd_1471439 : Nat := 83950606752352635760609

theorem tailTrace_1471439 : CollatzResearch.WordTrace tailWord_1471439 prefixEnd_1471439 83950606752352635760609 := by
  unfold tailWord_1471439
  simp only [CollatzResearch.WordTrace]
  refine ⟨53667789316235279619153371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35778526210823519746102247 53667789316235279619153371)
  ·
    refine ⟨80501683974352919428730057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53667789316235279619153371 80501683974352919428730057)
    ·
      refine ⟨60376262980764689571547543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80501683974352919428730057 60376262980764689571547543)
      ·
        refine ⟨90564394471147034357321315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60376262980764689571547543 90564394471147034357321315)
        ·
          refine ⟨135846591706720551535981973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90564394471147034357321315 135846591706720551535981973)
          ·
            refine ⟨6367808986252525853249155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135846591706720551535981973 6367808986252525853249155)
            ·
              refine ⟨9551713479378788779873733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6367808986252525853249155 9551713479378788779873733)
              ·
                refine ⟨1790946277383522896226325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9551713479378788779873733 1790946277383522896226325)
                ·
                  refine ⟨83950606752352635760609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1790946277383522896226325 83950606752352635760609)
                  ·
                    rfl

theorem cell23_1471439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 6].length) (baseStart_1471439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471439 prefixEnd_1471439 := by exact prefixLift 1471439
  have htrace : WordTrace (prefixWord ++ tailWord_1471439) baseStart_1471439 baseEnd_1471439 := by
    simpa [prefixWord, tailWord_1471439, baseEnd_1471439] using wordTrace_append hprefix tailTrace_1471439
  have hstable : (prefixWord ++ tailWord_1471439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471439).length < 2 ^ (prefixWord ++ tailWord_1471439).sum := by decide
  have hdescent : baseEnd_1471439 < baseStart_1471439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471470 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1471470 : Nat := 118140960795 + 1471470 * 2 ^ 59
def prefixEnd_1471470 : Nat := 4983230072969 + 3 ^ 40 * 1471470 * 2
def baseEnd_1471470 : Nat := 755571378671463100557839

theorem tailTrace_1471470 : CollatzResearch.WordTrace tailWord_1471470 prefixEnd_1471470 755571378671463100557839 := by
  unfold tailWord_1471470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6708614997390371489191483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35779279986081981275687909 6708614997390371489191483)
  ·
    refine ⟨10062922496085557233787225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6708614997390371489191483 10062922496085557233787225)
    ·
      refine ⟨7547191872064167925340419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10062922496085557233787225 7547191872064167925340419)
      ·
        refine ⟨11320787808096251888010629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7547191872064167925340419 11320787808096251888010629)
        ·
          refine ⟨2122647714018047229001993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11320787808096251888010629 2122647714018047229001993)
          ·
            refine ⟨1591985785513535421751495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122647714018047229001993 1591985785513535421751495)
            ·
              refine ⟨2387978678270303132627243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1591985785513535421751495 2387978678270303132627243)
              ·
                refine ⟨3581968017405454698940865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2387978678270303132627243 3581968017405454698940865)
                ·
                  refine ⟨2686476013054091024205649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3581968017405454698940865 2686476013054091024205649)
                  ·
                    refine ⟨2014857009790568268154237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686476013054091024205649 2014857009790568268154237)
                    ·
                      refine ⟨755571378671463100557839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2014857009790568268154237 755571378671463100557839)
                      ·
                        rfl

theorem cell23_1471470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1471470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471470 prefixEnd_1471470 := by exact prefixLift 1471470
  have htrace : WordTrace (prefixWord ++ tailWord_1471470) baseStart_1471470 baseEnd_1471470 := by
    simpa [prefixWord, tailWord_1471470, baseEnd_1471470] using wordTrace_append hprefix tailTrace_1471470
  have hstable : (prefixWord ++ tailWord_1471470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471470).length < 2 ^ (prefixWord ++ tailWord_1471470).sum := by decide
  have hdescent : baseEnd_1471470 < baseStart_1471470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471500 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 1, 1, 3]
def baseStart_1471500 : Nat := 118140960795 + 1471500 * 2 ^ 59
def prefixEnd_1471500 : Nat := 4983230072969 + 3 ^ 40 * 1471500 * 2
def baseEnd_1471500 : Nat := 755586783091097983182701

theorem tailTrace_1471500 : CollatzResearch.WordTrace tailWord_1471500 prefixEnd_1471500 755586783091097983182701 := by
  unfold tailWord_1471500
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835007084507143518561977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35780009446009524691415969 26835007084507143518561977)
  ·
    refine ⟨20126255313380357638921483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26835007084507143518561977 20126255313380357638921483)
    ·
      refine ⟨30189382970070536458382225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20126255313380357638921483 30189382970070536458382225)
      ·
        refine ⟨22642037227552902343786669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30189382970070536458382225 22642037227552902343786669)
        ·
          refine ⟨8490763960332338378920001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22642037227552902343786669 8490763960332338378920001)
          ·
            refine ⟨6368072970249253784190001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8490763960332338378920001 6368072970249253784190001)
            ·
              refine ⟨4776054727686940338142501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6368072970249253784190001 4776054727686940338142501)
              ·
                refine ⟨895510261441301313401719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4776054727686940338142501 895510261441301313401719)
                ·
                  refine ⟨1343265392161951970102579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895510261441301313401719 1343265392161951970102579)
                  ·
                    refine ⟨2014898088242927955153869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1343265392161951970102579 2014898088242927955153869)
                    ·
                      refine ⟨755586783091097983182701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2014898088242927955153869 755586783091097983182701)
                      ·
                        rfl

theorem cell23_1471500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_1471500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471500 prefixEnd_1471500 := by exact prefixLift 1471500
  have htrace : WordTrace (prefixWord ++ tailWord_1471500) baseStart_1471500 baseEnd_1471500 := by
    simpa [prefixWord, tailWord_1471500, baseEnd_1471500] using wordTrace_append hprefix tailTrace_1471500
  have hstable : (prefixWord ++ tailWord_1471500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471500).length < 2 ^ (prefixWord ++ tailWord_1471500).sum := by decide
  have hdescent : baseEnd_1471500 < baseStart_1471500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471520 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_1471520 : Nat := 118140960795 + 1471520 * 2 ^ 59
def prefixEnd_1471520 : Nat := 4983230072969 + 3 ^ 40 * 1471520 * 2
def baseEnd_1471520 : Nat := 251865684234729301644203

theorem tailTrace_1471520 : CollatzResearch.WordTrace tailWord_1471520 prefixEnd_1471520 251865684234729301644203 := by
  unfold tailWord_1471520
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835371814470915226426007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35780495752627886968568009 26835371814470915226426007)
  ·
    refine ⟨40253057721706372839639011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26835371814470915226426007 40253057721706372839639011)
    ·
      refine ⟨60379586582559559259458517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40253057721706372839639011 60379586582559559259458517)
      ·
        refine ⟨1415146560528739670143559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 60379586582559559259458517 1415146560528739670143559)
        ·
          refine ⟨2122719840793109505215339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415146560528739670143559 2122719840793109505215339)
          ·
            refine ⟨3184079761189664257823009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2122719840793109505215339 3184079761189664257823009)
            ·
              refine ⟨2388059820892248193367257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184079761189664257823009 2388059820892248193367257)
              ·
                refine ⟨1791044865669186145025443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388059820892248193367257 1791044865669186145025443)
                ·
                  refine ⟨2686567298503779217538165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791044865669186145025443 2686567298503779217538165)
                  ·
                    refine ⟨251865684234729301644203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2686567298503779217538165 251865684234729301644203)
                    ·
                      rfl

theorem cell23_1471520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_1471520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471520 prefixEnd_1471520 := by exact prefixLift 1471520
  have htrace : WordTrace (prefixWord ++ tailWord_1471520) baseStart_1471520 baseEnd_1471520 := by
    simpa [prefixWord, tailWord_1471520, baseEnd_1471520] using wordTrace_append hprefix tailTrace_1471520
  have hstable : (prefixWord ++ tailWord_1471520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471520).length < 2 ^ (prefixWord ++ tailWord_1471520).sum := by decide
  have hdescent : baseEnd_1471520 < baseStart_1471520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471523 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1471523 : Nat := 118140960795 + 1471523 * 2 ^ 59
def prefixEnd_1471523 : Nat := 4983230072969 + 3 ^ 40 * 1471523 * 2
def baseEnd_1471523 : Nat := 755598593146151393195095

theorem tailTrace_1471523 : CollatzResearch.WordTrace tailWord_1471523 prefixEnd_1471523 755598593146151393195095 := by
  unfold tailWord_1471523
  simp only [CollatzResearch.WordTrace]
  refine ⟨53670853047930961965211223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35780568698620641310140815 53670853047930961965211223)
  ·
    refine ⟨80506279571896442947816835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53670853047930961965211223 80506279571896442947816835)
    ·
      refine ⟨120759419357844664421725253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80506279571896442947816835 120759419357844664421725253)
      ·
        refine ⟨22642391129595874579073485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120759419357844664421725253 22642391129595874579073485)
        ·
          refine ⟨8490896673598452967152557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22642391129595874579073485 8490896673598452967152557)
          ·
            refine ⟨3184086252599419862682209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8490896673598452967152557 3184086252599419862682209)
            ·
              refine ⟨2388064689449564897011657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184086252599419862682209 2388064689449564897011657)
              ·
                refine ⟨1791048517087173672758743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388064689449564897011657 1791048517087173672758743)
                ·
                  refine ⟨2686572775630760509138115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791048517087173672758743 2686572775630760509138115)
                  ·
                    refine ⟨4029859163446140763707173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686572775630760509138115 4029859163446140763707173)
                    ·
                      refine ⟨755598593146151393195095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4029859163446140763707173 755598593146151393195095)
                      ·
                        rfl

theorem cell23_1471523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1471523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471523 prefixEnd_1471523 := by exact prefixLift 1471523
  have htrace : WordTrace (prefixWord ++ tailWord_1471523) baseStart_1471523 baseEnd_1471523 := by
    simpa [prefixWord, tailWord_1471523, baseEnd_1471523] using wordTrace_append hprefix tailTrace_1471523
  have hstable : (prefixWord ++ tailWord_1471523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471523).length < 2 ^ (prefixWord ++ tailWord_1471523).sum := by decide
  have hdescent : baseEnd_1471523 < baseStart_1471523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471540 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1471540 : Nat := 118140960795 + 1471540 * 2 ^ 59
def prefixEnd_1471540 : Nat := 4983230072969 + 3 ^ 40 * 1471540 * 2
def baseEnd_1471540 : Nat := 755607322317277826682517

theorem tailTrace_1471540 : CollatzResearch.WordTrace tailWord_1471540 prefixEnd_1471540 755607322317277826682517 := by
  unfold tailWord_1471540
  simp only [CollatzResearch.WordTrace]
  refine ⟨26835736544434686934290037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35780982059246249245720049 26835736544434686934290037)
  ·
    refine ⟨2515850301040751900089691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26835736544434686934290037 2515850301040751900089691)
    ·
      refine ⟨3773775451561127850134537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2515850301040751900089691 3773775451561127850134537)
      ·
        refine ⟨2830331588670845887600903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3773775451561127850134537 2830331588670845887600903)
        ·
          refine ⟨4245497383006268831401355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830331588670845887600903 4245497383006268831401355)
          ·
            refine ⟨6368246074509403247102033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245497383006268831401355 6368246074509403247102033)
            ·
              refine ⟨4776184555882052435326525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6368246074509403247102033 4776184555882052435326525)
              ·
                refine ⟨1791069208455769663247447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4776184555882052435326525 1791069208455769663247447)
                ·
                  refine ⟨2686603812683654494871171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791069208455769663247447 2686603812683654494871171)
                  ·
                    refine ⟨4029905719025481742306757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686603812683654494871171 4029905719025481742306757)
                    ·
                      refine ⟨755607322317277826682517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4029905719025481742306757 755607322317277826682517)
                      ·
                        rfl

theorem cell23_1471540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1471540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471540 prefixEnd_1471540 := by exact prefixLift 1471540
  have htrace : WordTrace (prefixWord ++ tailWord_1471540) baseStart_1471540 baseEnd_1471540 := by
    simpa [prefixWord, tailWord_1471540, baseEnd_1471540] using wordTrace_append hprefix tailTrace_1471540
  have hstable : (prefixWord ++ tailWord_1471540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471540).length < 2 ^ (prefixWord ++ tailWord_1471540).sum := by decide
  have hdescent : baseEnd_1471540 < baseStart_1471540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471574 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1471574 : Nat := 118140960795 + 1471574 * 2 ^ 59
def prefixEnd_1471574 : Nat := 4983230072969 + 3 ^ 40 * 1471574 * 2
def baseEnd_1471574 : Nat := 755624780659530693657361

theorem tailTrace_1471574 : CollatzResearch.WordTrace tailWord_1471574 prefixEnd_1471574 755624780659530693657361 := by
  unfold tailWord_1471574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354544573171637354707361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35781808780497465116878517 3354544573171637354707361)
  ·
    refine ⟨2515908429878728016030521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3354544573171637354707361 2515908429878728016030521)
    ·
      refine ⟨1886931322409046012022891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2515908429878728016030521 1886931322409046012022891)
      ·
        refine ⟨2830396983613569018034337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1886931322409046012022891 2830396983613569018034337)
        ·
          refine ⟨2122797737710176763525753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2830396983613569018034337 2122797737710176763525753)
          ·
            refine ⟨1592098303282632572644315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2122797737710176763525753 1592098303282632572644315)
            ·
              refine ⟨2388147454923948858966473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592098303282632572644315 2388147454923948858966473)
              ·
                refine ⟨1791110591192961644224855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2388147454923948858966473 1791110591192961644224855)
                ·
                  refine ⟨2686665886789442466337283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1791110591192961644224855 2686665886789442466337283)
                  ·
                    refine ⟨4029998830184163699505925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2686665886789442466337283 4029998830184163699505925)
                    ·
                      refine ⟨755624780659530693657361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4029998830184163699505925 755624780659530693657361)
                      ·
                        rfl

theorem cell23_1471574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1471574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471574 prefixEnd_1471574 := by exact prefixLift 1471574
  have htrace : WordTrace (prefixWord ++ tailWord_1471574) baseStart_1471574 baseEnd_1471574 := by
    simpa [prefixWord, tailWord_1471574, baseEnd_1471574] using wordTrace_append hprefix tailTrace_1471574
  have hstable : (prefixWord ++ tailWord_1471574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471574).length < 2 ^ (prefixWord ++ tailWord_1471574).sum := by decide
  have hdescent : baseEnd_1471574 < baseStart_1471574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471583 : List Nat := [1, 1, 2, 3, 1, 1, 5, 1, 3, 3, 2]
def baseStart_1471583 : Nat := 118140960795 + 1471583 * 2 ^ 59
def prefixEnd_1471583 : Nat := 4983230072969 + 3 ^ 40 * 1471583 * 2
def baseEnd_1471583 : Nat := 755629401985421158444819

theorem tailTrace_1471583 : CollatzResearch.WordTrace tailWord_1471583 prefixEnd_1471583 755629401985421158444819 := by
  unfold tailWord_1471583
  simp only [CollatzResearch.WordTrace]
  refine ⟨53673041427713592212395403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35782027618475728141596935 53673041427713592212395403)
  ·
    refine ⟨80509562141570388318593105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53673041427713592212395403 80509562141570388318593105)
    ·
      refine ⟨60382171606177791238944829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80509562141570388318593105 60382171606177791238944829)
      ·
        refine ⟨22643314352316671714604311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60382171606177791238944829 22643314352316671714604311)
        ·
          refine ⟨33964971528475007571906467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22643314352316671714604311 33964971528475007571906467)
          ·
            refine ⟨50947457292712511357859701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33964971528475007571906467 50947457292712511357859701)
            ·
              refine ⟨4776324121191797939799347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50947457292712511357859701 4776324121191797939799347)
              ·
                refine ⟨7164486181787696909699021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4776324121191797939799347 7164486181787696909699021)
                ·
                  refine ⟨2686682318170386341137133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7164486181787696909699021 2686682318170386341137133)
                  ·
                    refine ⟨1007505869313894877926425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2686682318170386341137133 1007505869313894877926425)
                    ·
                      refine ⟨755629401985421158444819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007505869313894877926425 755629401985421158444819)
                      ·
                        rfl

theorem cell23_1471583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_1471583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471583 prefixEnd_1471583 := by exact prefixLift 1471583
  have htrace : WordTrace (prefixWord ++ tailWord_1471583) baseStart_1471583 baseEnd_1471583 := by
    simpa [prefixWord, tailWord_1471583, baseEnd_1471583] using wordTrace_append hprefix tailTrace_1471583
  have hstable : (prefixWord ++ tailWord_1471583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471583).length < 2 ^ (prefixWord ++ tailWord_1471583).sum := by decide
  have hdescent : baseEnd_1471583 < baseStart_1471583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471613 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_1471613 : Nat := 118140960795 + 1471613 * 2 ^ 59
def prefixEnd_1471613 : Nat := 4983230072969 + 3 ^ 40 * 1471613 * 2
def baseEnd_1471613 : Nat := 755644806405056041069681

theorem tailTrace_1471613 : CollatzResearch.WordTrace tailWord_1471613 prefixEnd_1471613 755644806405056041069681 := by
  unfold tailWord_1471613
  simp only [CollatzResearch.WordTrace]
  refine ⟨53674135617604907335987493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35782757078403271557324995 53674135617604907335987493)
  ·
    refine ⟨10063900428300920125497655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53674135617604907335987493 10063900428300920125497655)
    ·
      refine ⟨15095850642451380188246483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10063900428300920125497655 15095850642451380188246483)
      ·
        refine ⟨22643775963677070282369725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15095850642451380188246483 22643775963677070282369725)
        ·
          refine ⟨8491415986378901355888647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22643775963677070282369725 8491415986378901355888647)
          ·
            refine ⟨12737123979568352033832971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8491415986378901355888647 12737123979568352033832971)
            ·
              refine ⟨19105685969352528050749457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12737123979568352033832971 19105685969352528050749457)
              ·
                refine ⟨14329264477014396038062093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19105685969352528050749457 14329264477014396038062093)
                ·
                  refine ⟨5373474178880398514273285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14329264477014396038062093 5373474178880398514273285)
                  ·
                    refine ⟨1007526408540074721426241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373474178880398514273285 1007526408540074721426241)
                    ·
                      refine ⟨755644806405056041069681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007526408540074721426241 755644806405056041069681)
                      ·
                        rfl

theorem cell23_1471613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_1471613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471613 prefixEnd_1471613 := by exact prefixLift 1471613
  have htrace : WordTrace (prefixWord ++ tailWord_1471613) baseStart_1471613 baseEnd_1471613 := by
    simpa [prefixWord, tailWord_1471613, baseEnd_1471613] using wordTrace_append hprefix tailTrace_1471613
  have hstable : (prefixWord ++ tailWord_1471613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471613).length < 2 ^ (prefixWord ++ tailWord_1471613).sum := by decide
  have hdescent : baseEnd_1471613 < baseStart_1471613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471614 : List Nat := [4, 2, 4, 1, 2, 1, 1, 8]
def baseStart_1471614 : Nat := 118140960795 + 1471614 * 2 ^ 59
def prefixEnd_1471614 : Nat := 4983230072969 + 3 ^ 40 * 1471614 * 2
def baseEnd_1471614 : Nat := 27986863699470760635451

theorem tailTrace_1471614 : CollatzResearch.WordTrace tailWord_1471614 prefixEnd_1471614 27986863699470760635451 := by
  unfold tailWord_1471614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709271511325160563346737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35782781393734189671182597 6709271511325160563346737)
  ·
    refine ⟨5031953633493870422510053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6709271511325160563346737 5031953633493870422510053)
    ·
      refine ⟨943491306280100704220635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5031953633493870422510053 943491306280100704220635)
      ·
        refine ⟨1415236959420151056330953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 943491306280100704220635 1415236959420151056330953)
        ·
          refine ⟨1061427719565113292248215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415236959420151056330953 1061427719565113292248215)
          ·
            refine ⟨1592141579347669938372323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061427719565113292248215 1592141579347669938372323)
            ·
              refine ⟨2388212369021504907558485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592141579347669938372323 2388212369021504907558485)
              ·
                refine ⟨27986863699470760635451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2388212369021504907558485 27986863699470760635451)
                ·
                  rfl

theorem cell23_1471614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_1471614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471614 prefixEnd_1471614 := by exact prefixLift 1471614
  have htrace : WordTrace (prefixWord ++ tailWord_1471614) baseStart_1471614 baseEnd_1471614 := by
    simpa [prefixWord, tailWord_1471614, baseEnd_1471614] using wordTrace_append hprefix tailTrace_1471614
  have hstable : (prefixWord ++ tailWord_1471614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471614).length < 2 ^ (prefixWord ++ tailWord_1471614).sum := by decide
  have hdescent : baseEnd_1471614 < baseStart_1471614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471616 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3]
def baseStart_1471616 : Nat := 118140960795 + 1471616 * 2 ^ 59
def prefixEnd_1471616 : Nat := 4983230072969 + 3 ^ 40 * 1471616 * 2
def baseEnd_1471616 : Nat := 755646346847019529332167

theorem tailTrace_1471616 : CollatzResearch.WordTrace tailWord_1471616 prefixEnd_1471616 755646346847019529332167 := by
  unfold tailWord_1471616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26837122518297019424173351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35782830024396025898897801 26837122518297019424173351)
  ·
    refine ⟨40255683777445529136260027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26837122518297019424173351 40255683777445529136260027)
    ·
      refine ⟨60383525666168293704390041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40255683777445529136260027 60383525666168293704390041)
      ·
        refine ⟨45287644249626220278292531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60383525666168293704390041 45287644249626220278292531)
        ·
          refine ⟨67931466374439330417438797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45287644249626220278292531 67931466374439330417438797)
          ·
            refine ⟨25474299890414748906539549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67931466374439330417438797 25474299890414748906539549)
            ·
              refine ⟨9552862458905530839952331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25474299890414748906539549 9552862458905530839952331)
              ·
                refine ⟨14329293688358296259928497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9552862458905530839952331 14329293688358296259928497)
                ·
                  refine ⟨10746970266268722194946373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14329293688358296259928497 10746970266268722194946373)
                  ·
                    refine ⟨2015056924925385411552445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10746970266268722194946373 2015056924925385411552445)
                    ·
                      refine ⟨755646346847019529332167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2015056924925385411552445 755646346847019529332167)
                      ·
                        rfl

theorem cell23_1471616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_1471616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471616 prefixEnd_1471616 := by exact prefixLift 1471616
  have htrace : WordTrace (prefixWord ++ tailWord_1471616) baseStart_1471616 baseEnd_1471616 := by
    simpa [prefixWord, tailWord_1471616, baseEnd_1471616] using wordTrace_append hprefix tailTrace_1471616
  have hstable : (prefixWord ++ tailWord_1471616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471616).length < 2 ^ (prefixWord ++ tailWord_1471616).sum := by decide
  have hdescent : baseEnd_1471616 < baseStart_1471616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471630 : List Nat := [4, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_1471630 : Nat := 118140960795 + 1471630 * 2 ^ 59
def prefixEnd_1471630 : Nat := 4983230072969 + 3 ^ 40 * 1471630 * 2
def baseEnd_1471630 : Nat := 755653535576182474557103

theorem tailTrace_1471630 : CollatzResearch.WordTrace tailWord_1471630 prefixEnd_1471630 755653535576182474557103 := by
  unfold tailWord_1471630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6709344457317914904919543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35783170439028879492904229 6709344457317914904919543)
  ·
    refine ⟨10064016685976872357379315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6709344457317914904919543 10064016685976872357379315)
    ·
      refine ⟨15096025028965308536068973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10064016685976872357379315 15096025028965308536068973)
      ·
        refine ⟨5661009385861990701025865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15096025028965308536068973 5661009385861990701025865)
        ·
          refine ⟨4245757039396493025769399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5661009385861990701025865 4245757039396493025769399)
          ·
            refine ⟨6368635559094739538654099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4245757039396493025769399 6368635559094739538654099)
            ·
              refine ⟨9552953338642109307981149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368635559094739538654099 9552953338642109307981149)
              ·
                refine ⟨3582357501990790990492931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9552953338642109307981149 3582357501990790990492931)
                ·
                  refine ⟨5373536252986186485739397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582357501990790990492931 5373536252986186485739397)
                  ·
                    refine ⟨1007538047434909966076137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5373536252986186485739397 1007538047434909966076137)
                    ·
                      refine ⟨755653535576182474557103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007538047434909966076137 755653535576182474557103)
                      ·
                        rfl

theorem cell23_1471630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_1471630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471630 prefixEnd_1471630 := by exact prefixLift 1471630
  have htrace : WordTrace (prefixWord ++ tailWord_1471630) baseStart_1471630 baseEnd_1471630 := by
    simpa [prefixWord, tailWord_1471630, baseEnd_1471630] using wordTrace_append hprefix tailTrace_1471630
  have hstable : (prefixWord ++ tailWord_1471630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471630).length < 2 ^ (prefixWord ++ tailWord_1471630).sum := by decide
  have hdescent : baseEnd_1471630 < baseStart_1471630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471653 : List Nat := [1, 3, 1, 2, 1, 4, 1, 5, 5]
def baseStart_1471653 : Nat := 118140960795 + 1471653 * 2 ^ 59
def prefixEnd_1471653 : Nat := 4983230072969 + 3 ^ 40 * 1471653 * 2
def baseEnd_1471653 : Nat := 83962816181248431618833

theorem tailTrace_1471653 : CollatzResearch.WordTrace tailWord_1471653 prefixEnd_1471653 83962816181248431618833 := by
  unfold tailWord_1471653
  simp only [CollatzResearch.WordTrace]
  refine ⟨53675594537459994167443613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35783729691639996111629075 53675594537459994167443613)
  ·
    refine ⟨20128347951547497812791355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53675594537459994167443613 20128347951547497812791355)
    ·
      refine ⟨30192521927321246719187033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20128347951547497812791355 30192521927321246719187033)
      ·
        refine ⟨22644391445490935039390275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30192521927321246719187033 22644391445490935039390275)
        ·
          refine ⟨33966587168236402559085413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22644391445490935039390275 33966587168236402559085413)
          ·
            refine ⟨6368735094044325479828515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33966587168236402559085413 6368735094044325479828515)
            ·
              refine ⟨9553102641066488219742773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6368735094044325479828515 9553102641066488219742773)
              ·
                refine ⟨895603372599983270600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9553102641066488219742773 895603372599983270600885)
                ·
                  refine ⟨83962816181248431618833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895603372599983270600885 83962816181248431618833)
                  ·
                    rfl

theorem cell23_1471653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_1471653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471653 prefixEnd_1471653 := by exact prefixLift 1471653
  have htrace : WordTrace (prefixWord ++ tailWord_1471653) baseStart_1471653 baseEnd_1471653 := by
    simpa [prefixWord, tailWord_1471653, baseEnd_1471653] using wordTrace_append hprefix tailTrace_1471653
  have hstable : (prefixWord ++ tailWord_1471653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471653).length < 2 ^ (prefixWord ++ tailWord_1471653).sum := by decide
  have hdescent : baseEnd_1471653 < baseStart_1471653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471681 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1471681 : Nat := 118140960795 + 1471681 * 2 ^ 59
def prefixEnd_1471681 : Nat := 4983230072969 + 3 ^ 40 * 1471681 * 2
def baseEnd_1471681 : Nat := 755679723089561775019369

theorem tailTrace_1471681 : CollatzResearch.WordTrace tailWord_1471681 prefixEnd_1471681 755679723089561775019369 := by
  unfold tailWord_1471681
  simp only [CollatzResearch.WordTrace]
  refine ⟨53676615781358554949462897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35784410520905703299641931 53676615781358554949462897)
  ·
    refine ⟨40257461836018916212097173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53676615781358554949462897 40257461836018916212097173)
    ·
      refine ⟨1887068523563386697442055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 40257461836018916212097173 1887068523563386697442055)
      ·
        refine ⟨2830602785345080046163083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887068523563386697442055 2830602785345080046163083)
        ·
          refine ⟨4245904178017620069244625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2830602785345080046163083 4245904178017620069244625)
          ·
            refine ⟨3184428133513215051933469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4245904178017620069244625 3184428133513215051933469)
            ·
              refine ⟨1194160550067455644475051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3184428133513215051933469 1194160550067455644475051)
              ·
                refine ⟨1791240825101183466712577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194160550067455644475051 1791240825101183466712577)
                ·
                  refine ⟨1343430618825887600034433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791240825101183466712577 1343430618825887600034433)
                  ·
                    refine ⟨1007572964119415700025825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343430618825887600034433 1007572964119415700025825)
                    ·
                      refine ⟨755679723089561775019369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007572964119415700025825 755679723089561775019369)
                      ·
                        rfl

theorem cell23_1471681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1471681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471681 prefixEnd_1471681 := by exact prefixLift 1471681
  have htrace : WordTrace (prefixWord ++ tailWord_1471681) baseStart_1471681 baseEnd_1471681 := by
    simpa [prefixWord, tailWord_1471681, baseEnd_1471681] using wordTrace_append hprefix tailTrace_1471681
  have hstable : (prefixWord ++ tailWord_1471681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471681).length < 2 ^ (prefixWord ++ tailWord_1471681).sum := by decide
  have hdescent : baseEnd_1471681 < baseStart_1471681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471703 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_1471703 : Nat := 118140960795 + 1471703 * 2 ^ 59
def prefixEnd_1471703 : Nat := 4983230072969 + 3 ^ 40 * 1471703 * 2
def baseEnd_1471703 : Nat := 755691019663960688944267

theorem tailTrace_1471703 : CollatzResearch.WordTrace tailWord_1471703 prefixEnd_1471703 755691019663960688944267 := by
  unfold tailWord_1471703
  simp only [CollatzResearch.WordTrace]
  refine ⟨53677418187278852706763763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35784945458185901804509175 53677418187278852706763763)
  ·
    refine ⟨80516127280918279060145645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53677418187278852706763763 80516127280918279060145645)
    ·
      refine ⟨30193547730344354647554617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80516127280918279060145645 30193547730344354647554617)
      ·
        refine ⟨22645160797758265985665963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30193547730344354647554617 22645160797758265985665963)
        ·
          refine ⟨33967741196637398978498945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22645160797758265985665963 33967741196637398978498945)
          ·
            refine ⟨25475805897478049233874209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33967741196637398978498945 25475805897478049233874209)
            ·
              refine ⟨19106854423108536925405657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25475805897478049233874209 19106854423108536925405657)
              ·
                refine ⟨14330140817331402694054243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19106854423108536925405657 14330140817331402694054243)
                ·
                  refine ⟨21495211225997104041081365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14330140817331402694054243 21495211225997104041081365)
                  ·
                    refine ⟨1007588026218614251925689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21495211225997104041081365 1007588026218614251925689)
                    ·
                      refine ⟨755691019663960688944267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007588026218614251925689 755691019663960688944267)
                      ·
                        rfl

theorem cell23_1471703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_1471703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471703 prefixEnd_1471703 := by exact prefixLift 1471703
  have htrace : WordTrace (prefixWord ++ tailWord_1471703) baseStart_1471703 baseEnd_1471703 := by
    simpa [prefixWord, tailWord_1471703, baseEnd_1471703] using wordTrace_append hprefix tailTrace_1471703
  have hstable : (prefixWord ++ tailWord_1471703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471703).length < 2 ^ (prefixWord ++ tailWord_1471703).sum := by decide
  have hdescent : baseEnd_1471703 < baseStart_1471703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471706 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1471706 : Nat := 118140960795 + 1471706 * 2 ^ 59
def prefixEnd_1471706 : Nat := 4983230072969 + 3 ^ 40 * 1471706 * 2
def baseEnd_1471706 : Nat := 755692560105924177206753

theorem tailTrace_1471706 : CollatzResearch.WordTrace tailWord_1471706 prefixEnd_1471706 755692560105924177206753 := by
  unfold tailWord_1471706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13419381901566996054780743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35785018404178656146081981 13419381901566996054780743)
  ·
    refine ⟨20129072852350494082171115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13419381901566996054780743 20129072852350494082171115)
    ·
      refine ⟨30193609278525741123256673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20129072852350494082171115 30193609278525741123256673)
      ·
        refine ⟨22645206958894305842442505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30193609278525741123256673 22645206958894305842442505)
        ·
          refine ⟨16983905219170729381831879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22645206958894305842442505 16983905219170729381831879)
          ·
            refine ⟨25475857828756094072747819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16983905219170729381831879 25475857828756094072747819)
            ·
              refine ⟨38213786743134141109121729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25475857828756094072747819 38213786743134141109121729)
              ·
                refine ⟨28660340057350605831841297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38213786743134141109121729 28660340057350605831841297)
                ·
                  refine ⟨21495255043012954373880973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28660340057350605831841297 21495255043012954373880973)
                  ·
                    refine ⟨8060720641129857890205365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21495255043012954373880973 8060720641129857890205365)
                    ·
                      refine ⟨755692560105924177206753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8060720641129857890205365 755692560105924177206753)
                      ·
                        rfl

theorem cell23_1471706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1471706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471706 prefixEnd_1471706 := by exact prefixLift 1471706
  have htrace : WordTrace (prefixWord ++ tailWord_1471706) baseStart_1471706 baseEnd_1471706 := by
    simpa [prefixWord, tailWord_1471706, baseEnd_1471706] using wordTrace_append hprefix tailTrace_1471706
  have hstable : (prefixWord ++ tailWord_1471706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471706).length < 2 ^ (prefixWord ++ tailWord_1471706).sum := by decide
  have hdescent : baseEnd_1471706 < baseStart_1471706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471716 : List Nat := [2, 3, 1, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_1471716 : Nat := 118140960795 + 1471716 * 2 ^ 59
def prefixEnd_1471716 : Nat := 4983230072969 + 3 ^ 40 * 1471716 * 2
def baseEnd_1471716 : Nat := 755697694912469138081707

theorem tailTrace_1471716 : CollatzResearch.WordTrace tailWord_1471716 prefixEnd_1471716 755697694912469138081707 := by
  unfold tailWord_1471716
  simp only [CollatzResearch.WordTrace]
  refine ⟨26838946168115877963493501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35785261557487837284658001 26838946168115877963493501)
  ·
    refine ⟨10064604813043454236310063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26838946168115877963493501 10064604813043454236310063)
    ·
      refine ⟨15096907219565181354465095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10064604813043454236310063 15096907219565181354465095)
      ·
        refine ⟨22645360829347772031697643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15096907219565181354465095 22645360829347772031697643)
        ·
          refine ⟨33968041244021658047546465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22645360829347772031697643 33968041244021658047546465)
          ·
            refine ⟨25476030933016243535659849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33968041244021658047546465 25476030933016243535659849)
            ·
              refine ⟨19107023199762182651744887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25476030933016243535659849 19107023199762182651744887)
              ·
                refine ⟨28660534799643273977617331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19107023199762182651744887 28660534799643273977617331)
                ·
                  refine ⟨42990802199464910966425997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28660534799643273977617331 42990802199464910966425997)
                  ·
                    refine ⟨16121550824799341612409749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42990802199464910966425997 16121550824799341612409749)
                    ·
                      refine ⟨755697694912469138081707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16121550824799341612409749 755697694912469138081707)
                      ·
                        rfl

theorem cell23_1471716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_1471716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471716 prefixEnd_1471716 := by exact prefixLift 1471716
  have htrace : WordTrace (prefixWord ++ tailWord_1471716) baseStart_1471716 baseEnd_1471716 := by
    simpa [prefixWord, tailWord_1471716, baseEnd_1471716] using wordTrace_append hprefix tailTrace_1471716
  have hstable : (prefixWord ++ tailWord_1471716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471716).length < 2 ^ (prefixWord ++ tailWord_1471716).sum := by decide
  have hdescent : baseEnd_1471716 < baseStart_1471716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471723 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3]
def baseStart_1471723 : Nat := 118140960795 + 1471723 * 2 ^ 59
def prefixEnd_1471723 : Nat := 4983230072969 + 3 ^ 40 * 1471723 * 2
def baseEnd_1471723 : Nat := 755701289277050610694175

theorem tailTrace_1471723 : CollatzResearch.WordTrace tailWord_1471723 prefixEnd_1471723 755701289277050610694175 := by
  unfold tailWord_1471723
  simp only [CollatzResearch.WordTrace]
  refine ⟨53678147647206396122491823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35785431764804264081661215 53678147647206396122491823)
  ·
    refine ⟨80517221470809594183737735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53678147647206396122491823 80517221470809594183737735)
    ·
      refine ⟨120775832206214391275606603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80517221470809594183737735 120775832206214391275606603)
      ·
        refine ⟨181163748309321586913409905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120775832206214391275606603 181163748309321586913409905)
        ·
          refine ⟨135872811231991190185057429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 181163748309321586913409905 135872811231991190185057429)
          ·
            refine ⟨6369038026499587039924567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135872811231991190185057429 6369038026499587039924567)
            ·
              refine ⟨9553557039749380559886851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6369038026499587039924567 9553557039749380559886851)
              ·
                refine ⟨14330335559624070839830277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9553557039749380559886851 14330335559624070839830277)
                ·
                  refine ⟨2686937917429513282468177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14330335559624070839830277 2686937917429513282468177)
                  ·
                    refine ⟨2015203438072134961851133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2686937917429513282468177 2015203438072134961851133)
                    ·
                      refine ⟨755701289277050610694175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2015203438072134961851133 755701289277050610694175)
                      ·
                        rfl

theorem cell23_1471723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 3].length) (baseStart_1471723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471723 prefixEnd_1471723 := by exact prefixLift 1471723
  have htrace : WordTrace (prefixWord ++ tailWord_1471723) baseStart_1471723 baseEnd_1471723 := by
    simpa [prefixWord, tailWord_1471723, baseEnd_1471723] using wordTrace_append hprefix tailTrace_1471723
  have hstable : (prefixWord ++ tailWord_1471723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471723).length < 2 ^ (prefixWord ++ tailWord_1471723).sum := by decide
  have hdescent : baseEnd_1471723 < baseStart_1471723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471732 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1471732 : Nat := 118140960795 + 1471732 * 2 ^ 59
def prefixEnd_1471732 : Nat := 4983230072969 + 3 ^ 40 * 1471732 * 2
def baseEnd_1471732 : Nat := 755705910602941075481635

theorem tailTrace_1471732 : CollatzResearch.WordTrace tailWord_1471732 prefixEnd_1471732 755705910602941075481635 := by
  unfold tailWord_1471732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26839237952086895329784725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35785650602782527106379633 26839237952086895329784725)
  ·
    refine ⟨1258089279004073218583659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26839237952086895329784725 1258089279004073218583659)
    ·
      refine ⟨1887133918506109827875489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258089279004073218583659 1887133918506109827875489)
      ·
        refine ⟨1415350438879582370906617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1887133918506109827875489 1415350438879582370906617)
        ·
          refine ⟨1061512829159686778179963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1415350438879582370906617 1061512829159686778179963)
          ·
            refine ⟨1592269243739530167269945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1061512829159686778179963 1592269243739530167269945)
            ·
              refine ⟨1194201932804647625452459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592269243739530167269945 1194201932804647625452459)
              ·
                refine ⟨1791302899206971438178689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1194201932804647625452459 1791302899206971438178689)
                ·
                  refine ⟨1343477174405228578634017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791302899206971438178689 1343477174405228578634017)
                  ·
                    refine ⟨1007607880803921433975513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343477174405228578634017 1007607880803921433975513)
                    ·
                      refine ⟨755705910602941075481635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007607880803921433975513 755705910602941075481635)
                      ·
                        rfl

theorem cell23_1471732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1471732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471732 prefixEnd_1471732 := by exact prefixLift 1471732
  have htrace : WordTrace (prefixWord ++ tailWord_1471732) baseStart_1471732 baseEnd_1471732 := by
    simpa [prefixWord, tailWord_1471732, baseEnd_1471732] using wordTrace_append hprefix tailTrace_1471732
  have hstable : (prefixWord ++ tailWord_1471732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471732).length < 2 ^ (prefixWord ++ tailWord_1471732).sum := by decide
  have hdescent : baseEnd_1471732 < baseStart_1471732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471743 : List Nat := [1, 1, 2, 2, 1, 6, 1, 3, 6]
def baseStart_1471743 : Nat := 118140960795 + 1471743 * 2 ^ 59
def prefixEnd_1471743 : Nat := 4983230072969 + 3 ^ 40 * 1471743 * 2
def baseEnd_1471743 : Nat := 83967950987793392493787

theorem tailTrace_1471743 : CollatzResearch.WordTrace tailWord_1471743 prefixEnd_1471743 83967950987793392493787 := by
  unfold tailWord_1471743
  simp only [CollatzResearch.WordTrace]
  refine ⟨53678877107133939538219883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35785918071422626358813255 53678877107133939538219883)
  ·
    refine ⟨80518315660700909307329825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53678877107133939538219883 80518315660700909307329825)
    ·
      refine ⟨60388736745525681980497369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80518315660700909307329825 60388736745525681980497369)
      ·
        refine ⟨45291552559144261485373027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60388736745525681980497369 45291552559144261485373027)
        ·
          refine ⟨67937328838716392228059541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45291552559144261485373027 67937328838716392228059541)
          ·
            refine ⟨3184562289314830885690291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67937328838716392228059541 3184562289314830885690291)
            ·
              refine ⟨4776843433972246328535437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3184562289314830885690291 4776843433972246328535437)
              ·
                refine ⟨1791316287739592373200789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4776843433972246328535437 1791316287739592373200789)
                ·
                  refine ⟨83967950987793392493787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1791316287739592373200789 83967950987793392493787)
                  ·
                    rfl

theorem cell23_1471743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 3, 6].length) (baseStart_1471743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471743 prefixEnd_1471743 := by exact prefixLift 1471743
  have htrace : WordTrace (prefixWord ++ tailWord_1471743) baseStart_1471743 baseEnd_1471743 := by
    simpa [prefixWord, tailWord_1471743, baseEnd_1471743] using wordTrace_append hprefix tailTrace_1471743
  have hstable : (prefixWord ++ tailWord_1471743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471743).length < 2 ^ (prefixWord ++ tailWord_1471743).sum := by decide
  have hdescent : baseEnd_1471743 < baseStart_1471743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471844 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_1471844 : Nat := 118140960795 + 1471844 * 2 ^ 59
def prefixEnd_1471844 : Nat := 4983230072969 + 3 ^ 40 * 1471844 * 2
def baseEnd_1471844 : Nat := 755763420436244637281119

theorem tailTrace_1471844 : CollatzResearch.WordTrace tailWord_1471844 prefixEnd_1471844 755763420436244637281119 := by
  unfold tailWord_1471844
  simp only [CollatzResearch.WordTrace]
  refine ⟨26841280439884016893823293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35788373919845355858431057 26841280439884016893823293)
  ·
    refine ⟨10065480164956506335183735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26841280439884016893823293 10065480164956506335183735)
    ·
      refine ⟨15098220247434759502775603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10065480164956506335183735 15098220247434759502775603)
      ·
        refine ⟨22647330371152139254163405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15098220247434759502775603 22647330371152139254163405)
        ·
          refine ⟨8492748889182052220311277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22647330371152139254163405 8492748889182052220311277)
          ·
            refine ⟨3184780833443269582616729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8492748889182052220311277 3184780833443269582616729)
            ·
              refine ⟨2388585625082452186962547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3184780833443269582616729 2388585625082452186962547)
              ·
                refine ⟨3582878437623678280443821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388585625082452186962547 3582878437623678280443821)
                ·
                  refine ⟨1343579414108879355166433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3582878437623678280443821 1343579414108879355166433)
                  ·
                    refine ⟨1007684560581659516374825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343579414108879355166433 1007684560581659516374825)
                    ·
                      refine ⟨755763420436244637281119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007684560581659516374825 755763420436244637281119)
                      ·
                        rfl

theorem cell23_1471844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_1471844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471844 prefixEnd_1471844 := by exact prefixLift 1471844
  have htrace : WordTrace (prefixWord ++ tailWord_1471844) baseStart_1471844 baseEnd_1471844 := by
    simpa [prefixWord, tailWord_1471844, baseEnd_1471844] using wordTrace_append hprefix tailTrace_1471844
  have hstable : (prefixWord ++ tailWord_1471844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471844).length < 2 ^ (prefixWord ++ tailWord_1471844).sum := by decide
  have hdescent : baseEnd_1471844 < baseStart_1471844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471854 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1471854 : Nat := 118140960795 + 1471854 * 2 ^ 59
def prefixEnd_1471854 : Nat := 4983230072969 + 3 ^ 40 * 1471854 * 2
def baseEnd_1471854 : Nat := 251922851747596532718691

theorem tailTrace_1471854 : CollatzResearch.WordTrace tailWord_1471854 prefixEnd_1471854 251922851747596532718691 := by
  unfold tailWord_1471854
  simp only [CollatzResearch.WordTrace]
  refine ⟨6710365701216475686938827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35788617073154536997007077 6710365701216475686938827)
  ·
    refine ⟨10065548551824713530408241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6710365701216475686938827 10065548551824713530408241)
    ·
      refine ⟨7549161413868535147806181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10065548551824713530408241 7549161413868535147806181)
      ·
        refine ⟨1415467765100350340213659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7549161413868535147806181 1415467765100350340213659)
        ·
          refine ⟨2123201647650525510320489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1415467765100350340213659 2123201647650525510320489)
          ·
            refine ⟨1592401235737894132740367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2123201647650525510320489 1592401235737894132740367)
            ·
              refine ⟨2388601853606841199110551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592401235737894132740367 2388601853606841199110551)
              ·
                refine ⟨3582902780410261798665827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388601853606841199110551 3582902780410261798665827)
                ·
                  refine ⟨5374354170615392697998741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3582902780410261798665827 5374354170615392697998741)
                  ·
                    refine ⟨251922851747596532718691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5374354170615392697998741 251922851747596532718691)
                    ·
                      rfl

theorem cell23_1471854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1471854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471854 prefixEnd_1471854 := by exact prefixLift 1471854
  have htrace : WordTrace (prefixWord ++ tailWord_1471854) baseStart_1471854 baseEnd_1471854 := by
    simpa [prefixWord, tailWord_1471854, baseEnd_1471854] using wordTrace_append hprefix tailTrace_1471854
  have hstable : (prefixWord ++ tailWord_1471854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471854).length < 2 ^ (prefixWord ++ tailWord_1471854).sum := by decide
  have hdescent : baseEnd_1471854 < baseStart_1471854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471893 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 4, 6]
def baseStart_1471893 : Nat := 118140960795 + 1471893 * 2 ^ 59
def prefixEnd_1471893 : Nat := 4983230072969 + 3 ^ 40 * 1471893 * 2
def baseEnd_1471893 : Nat := 251929526996104981856131

theorem tailTrace_1471893 : CollatzResearch.WordTrace tailWord_1471893 prefixEnd_1471893 251929526996104981856131 := by
  unfold tailWord_1471893
  simp only [CollatzResearch.WordTrace]
  refine ⟨53684348056590515156180333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35789565371060343437453555 53684348056590515156180333)
  ·
    refine ⟨20131630521221443183567625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53684348056590515156180333 20131630521221443183567625)
    ·
      refine ⟨15098722890916082387675719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20131630521221443183567625 15098722890916082387675719)
      ·
        refine ⟨22648084336374123581513579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15098722890916082387675719 22648084336374123581513579)
        ·
          refine ⟨33972126504561185372270369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22648084336374123581513579 33972126504561185372270369)
          ·
            refine ⟨25479094878420889029202777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33972126504561185372270369 25479094878420889029202777)
            ·
              refine ⟨19109321158815666771902083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25479094878420889029202777 19109321158815666771902083)
              ·
                refine ⟨28663981738223500157853125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19109321158815666771902083 28663981738223500157853125)
                ·
                  refine ⟨5374496575916906279597461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28663981738223500157853125 5374496575916906279597461)
                  ·
                    refine ⟨251929526996104981856131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5374496575916906279597461 251929526996104981856131)
                    ·
                      rfl

theorem cell23_1471893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 6].length) (baseStart_1471893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471893 prefixEnd_1471893 := by exact prefixLift 1471893
  have htrace : WordTrace (prefixWord ++ tailWord_1471893) baseStart_1471893 baseEnd_1471893 := by
    simpa [prefixWord, tailWord_1471893, baseEnd_1471893] using wordTrace_append hprefix tailTrace_1471893
  have hstable : (prefixWord ++ tailWord_1471893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471893).length < 2 ^ (prefixWord ++ tailWord_1471893).sum := by decide
  have hdescent : baseEnd_1471893 < baseStart_1471893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471923 : List Nat := [1, 1, 1, 2, 3, 1, 1, 6, 7]
def baseStart_1471923 : Nat := 118140960795 + 1471923 * 2 ^ 59
def prefixEnd_1471923 : Nat := 4983230072969 + 3 ^ 40 * 1471923 * 2
def baseEnd_1471923 : Nat := 83978220600883314243695

theorem tailTrace_1471923 : CollatzResearch.WordTrace tailWord_1471923 prefixEnd_1471923 83978220600883314243695 := by
  unfold tailWord_1471923
  simp only [CollatzResearch.WordTrace]
  refine ⟨53685442246481830279772423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35790294830987886853181615 53685442246481830279772423)
  ·
    refine ⟨80528163369722745419658635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53685442246481830279772423 80528163369722745419658635)
    ·
      refine ⟨120792245054584118129487953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80528163369722745419658635 120792245054584118129487953)
      ·
        refine ⟨90594183790938088597115965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120792245054584118129487953 90594183790938088597115965)
        ·
          refine ⟨33972818921601783223918487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90594183790938088597115965 33972818921601783223918487)
          ·
            refine ⟨50959228382402674835877731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33972818921601783223918487 50959228382402674835877731)
            ·
              refine ⟨76438842573604012253816597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50959228382402674835877731 76438842573604012253816597)
              ·
                refine ⟨3583070745637688074397653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76438842573604012253816597 3583070745637688074397653)
                ·
                  refine ⟨83978220600883314243695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3583070745637688074397653 83978220600883314243695)
                  ·
                    rfl

theorem cell23_1471923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 6, 7].length) (baseStart_1471923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471923 prefixEnd_1471923 := by exact prefixLift 1471923
  have htrace : WordTrace (prefixWord ++ tailWord_1471923) baseStart_1471923 baseEnd_1471923 := by
    simpa [prefixWord, tailWord_1471923, baseEnd_1471923] using wordTrace_append hprefix tailTrace_1471923
  have hstable : (prefixWord ++ tailWord_1471923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471923).length < 2 ^ (prefixWord ++ tailWord_1471923).sum := by decide
  have hdescent : baseEnd_1471923 < baseStart_1471923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471953 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 7]
def baseStart_1471953 : Nat := 118140960795 + 1471953 * 2 ^ 59
def prefixEnd_1471953 : Nat := 4983230072969 + 3 ^ 40 * 1471953 * 2
def baseEnd_1471953 : Nat := 251939796609194903606039

theorem tailTrace_1471953 : CollatzResearch.WordTrace tailWord_1471953 prefixEnd_1471953 251939796609194903606039 := by
  unfold tailWord_1471953
  simp only [CollatzResearch.WordTrace]
  refine ⟨53686536436373145403364513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35791024290915430268909675 53686536436373145403364513)
  ·
    refine ⟨40264902327279859052523385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53686536436373145403364513 40264902327279859052523385)
    ·
      refine ⟨30198676745459894289392539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40264902327279859052523385 30198676745459894289392539)
      ·
        refine ⟨45298015118189841434088809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30198676745459894289392539 45298015118189841434088809)
        ·
          refine ⟨33973511338642381075566607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45298015118189841434088809 33973511338642381075566607)
          ·
            refine ⟨50960267007963571613349911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33973511338642381075566607 50960267007963571613349911)
            ·
              refine ⟨76440400511945357420024867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50960267007963571613349911 76440400511945357420024867)
              ·
                refine ⟨114660600767918036130037301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76440400511945357420024867 114660600767918036130037301)
                ·
                  refine ⟨10749431321992315887190997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114660600767918036130037301 10749431321992315887190997)
                  ·
                    refine ⟨251939796609194903606039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10749431321992315887190997 251939796609194903606039)
                    ·
                      rfl

theorem cell23_1471953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_1471953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471953 prefixEnd_1471953 := by exact prefixLift 1471953
  have htrace : WordTrace (prefixWord ++ tailWord_1471953) baseStart_1471953 baseEnd_1471953 := by
    simpa [prefixWord, tailWord_1471953, baseEnd_1471953] using wordTrace_append hprefix tailTrace_1471953
  have hstable : (prefixWord ++ tailWord_1471953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471953).length < 2 ^ (prefixWord ++ tailWord_1471953).sum := by decide
  have hdescent : baseEnd_1471953 < baseStart_1471953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1471957 : List Nat := [1, 3, 2, 3, 1, 1, 3, 4, 5]
def baseStart_1471957 : Nat := 118140960795 + 1471957 * 2 ^ 59
def prefixEnd_1471957 : Nat := 4983230072969 + 3 ^ 40 * 1471957 * 2
def baseEnd_1471957 : Nat := 83980160416689188352011

theorem tailTrace_1471957 : CollatzResearch.WordTrace tailWord_1471957 prefixEnd_1471957 83980160416689188352011 := by
  unfold tailWord_1471957
  simp only [CollatzResearch.WordTrace]
  refine ⟨53686682328358654086510125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35791121552239102724340083 53686682328358654086510125)
  ·
    refine ⟨20132505873134495282441297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53686682328358654086510125 20132505873134495282441297)
    ·
      refine ⟨15099379404850871461830973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20132505873134495282441297 15099379404850871461830973)
      ·
        refine ⟨5662267276819076798186615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15099379404850871461830973 5662267276819076798186615)
        ·
          refine ⟨8493400915228615197279923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5662267276819076798186615 8493400915228615197279923)
          ·
            refine ⟨12740101372842922795919885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8493400915228615197279923 12740101372842922795919885)
            ·
              refine ⟨4777538014816096048469957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12740101372842922795919885 4777538014816096048469957)
              ·
                refine ⟨895788377778018009088117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4777538014816096048469957 895788377778018009088117)
                ·
                  refine ⟨83980160416689188352011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 895788377778018009088117 83980160416689188352011)
                  ·
                    rfl

theorem cell23_1471957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 5].length) (baseStart_1471957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1471957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1471957 prefixEnd_1471957 := by exact prefixLift 1471957
  have htrace : WordTrace (prefixWord ++ tailWord_1471957) baseStart_1471957 baseEnd_1471957 := by
    simpa [prefixWord, tailWord_1471957, baseEnd_1471957] using wordTrace_append hprefix tailTrace_1471957
  have hstable : (prefixWord ++ tailWord_1471957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1471957).length < 2 ^ (prefixWord ++ tailWord_1471957).sum := by decide
  have hdescent : baseEnd_1471957 < baseStart_1471957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1471957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472017 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 3, 4]
def baseStart_1472017 : Nat := 118140960795 + 1472017 * 2 ^ 59
def prefixEnd_1472017 : Nat := 4983230072969 + 3 ^ 40 * 1472017 * 2
def baseEnd_1472017 : Nat := 251950750863157486805941

theorem tailTrace_1472017 : CollatzResearch.WordTrace tailWord_1472017 prefixEnd_1472017 251950750863157486805941 := by
  unfold tailWord_1472017
  simp only [CollatzResearch.WordTrace]
  refine ⟨53688870708141284333694305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35792580472094189555796203 53688870708141284333694305)
  ·
    refine ⟨40266653031105963250270729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53688870708141284333694305 40266653031105963250270729)
    ·
      refine ⟨30199989773329472437703047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40266653031105963250270729 30199989773329472437703047)
      ·
        refine ⟨45299984659994208656554571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30199989773329472437703047 45299984659994208656554571)
        ·
          refine ⟨67949976989991312984831857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45299984659994208656554571 67949976989991312984831857)
          ·
            refine ⟨50962482742493484738623893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67949976989991312984831857 50962482742493484738623893)
            ·
              refine ⟨2388866378554382097122995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50962482742493484738623893 2388866378554382097122995)
              ·
                refine ⟨3583299567831573145684493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2388866378554382097122995 3583299567831573145684493)
                ·
                  refine ⟨1343737337936839929631685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3583299567831573145684493 1343737337936839929631685)
                  ·
                    refine ⟨251950750863157486805941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1343737337936839929631685 251950750863157486805941)
                    ·
                      rfl

theorem cell23_1472017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_1472017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472017 prefixEnd_1472017 := by exact prefixLift 1472017
  have htrace : WordTrace (prefixWord ++ tailWord_1472017) baseStart_1472017 baseEnd_1472017 := by
    simpa [prefixWord, tailWord_1472017, baseEnd_1472017] using wordTrace_append hprefix tailTrace_1472017
  have hstable : (prefixWord ++ tailWord_1472017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472017).length < 2 ^ (prefixWord ++ tailWord_1472017).sum := by decide
  have hdescent : baseEnd_1472017 < baseStart_1472017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472051 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 1, 4]
def baseStart_1472051 : Nat := 118140960795 + 1472051 * 2 ^ 59
def prefixEnd_1472051 : Nat := 4983230072969 + 3 ^ 40 * 1472051 * 2
def baseEnd_1472051 : Nat := 251956570310575109130889

theorem tailTrace_1472051 : CollatzResearch.WordTrace tailWord_1472051 prefixEnd_1472051 251956570310575109130889 := by
  unfold tailWord_1472051
  simp only [CollatzResearch.WordTrace]
  refine ⟨53690110790018108140432007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35793407193345405426954671 53690110790018108140432007)
  ·
    refine ⟨80535166185027162210648011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53690110790018108140432007 80535166185027162210648011)
    ·
      refine ⟨120802749277540743315972017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80535166185027162210648011 120802749277540743315972017)
      ·
        refine ⟨90602061958155557486979013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120802749277540743315972017 90602061958155557486979013)
        ·
          refine ⟨16987886617154167028808565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90602061958155557486979013 16987886617154167028808565)
          ·
            refine ⟨1592614370358203158950803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16987886617154167028808565 1592614370358203158950803)
            ·
              refine ⟨2388921555537304738426205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592614370358203158950803 2388921555537304738426205)
              ·
                refine ⟨895845583326489276909827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2388921555537304738426205 895845583326489276909827)
                ·
                  refine ⟨1343768374989733915364741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895845583326489276909827 1343768374989733915364741)
                  ·
                    refine ⟨251956570310575109130889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1343768374989733915364741 251956570310575109130889)
                    ·
                      rfl

theorem cell23_1472051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 4].length) (baseStart_1472051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472051 prefixEnd_1472051 := by exact prefixLift 1472051
  have htrace : WordTrace (prefixWord ++ tailWord_1472051) baseStart_1472051 baseEnd_1472051 := by
    simpa [prefixWord, tailWord_1472051, baseEnd_1472051] using wordTrace_append hprefix tailTrace_1472051
  have hstable : (prefixWord ++ tailWord_1472051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472051).length < 2 ^ (prefixWord ++ tailWord_1472051).sum := by decide
  have hdescent : baseEnd_1472051 < baseStart_1472051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472084 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 4, 3, 2]
def baseStart_1472084 : Nat := 118140960795 + 1472084 * 2 ^ 59
def prefixEnd_1472084 : Nat := 4983230072969 + 3 ^ 40 * 1472084 * 2
def baseEnd_1472084 : Nat := 755886655793323698280015

theorem tailTrace_1472084 : CollatzResearch.WordTrace tailWord_1472084 prefixEnd_1472084 755886655793323698280015 := by
  unfold tailWord_1472084
  simp only [CollatzResearch.WordTrace]
  refine ⟨26845657199449277388191653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35794209599265703184255537 26845657199449277388191653)
  ·
    refine ⟨5033560724896739510285935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26845657199449277388191653 5033560724896739510285935)
    ·
      refine ⟨7550341087345109265428903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5033560724896739510285935 7550341087345109265428903)
      ·
        refine ⟨11325511631017663898143355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7550341087345109265428903 11325511631017663898143355)
        ·
          refine ⟨16988267446526495847215033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11325511631017663898143355 16988267446526495847215033)
          ·
            refine ⟨12741200584894871885411275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16988267446526495847215033 12741200584894871885411275)
            ·
              refine ⟨19111800877342307828116913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12741200584894871885411275 19111800877342307828116913)
              ·
                refine ⟨14333850658006730871087685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19111800877342307828116913 14333850658006730871087685)
                ·
                  refine ⟨2687596998376262038328941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14333850658006730871087685 2687596998376262038328941)
                  ·
                    refine ⟨1007848874391098264373353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687596998376262038328941 1007848874391098264373353)
                    ·
                      refine ⟨755886655793323698280015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007848874391098264373353 755886655793323698280015)
                      ·
                        rfl

theorem cell23_1472084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_1472084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472084 prefixEnd_1472084 := by exact prefixLift 1472084
  have htrace : WordTrace (prefixWord ++ tailWord_1472084) baseStart_1472084 baseEnd_1472084 := by
    simpa [prefixWord, tailWord_1472084, baseEnd_1472084] using wordTrace_append hprefix tailTrace_1472084
  have hstable : (prefixWord ++ tailWord_1472084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472084).length < 2 ^ (prefixWord ++ tailWord_1472084).sum := by decide
  have hdescent : baseEnd_1472084 < baseStart_1472084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472090 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_1472090 : Nat := 118140960795 + 1472090 * 2 ^ 59
def prefixEnd_1472090 : Nat := 4983230072969 + 3 ^ 40 * 1472090 * 2
def baseEnd_1472090 : Nat := 251963245559083558268329

theorem tailTrace_1472090 : CollatzResearch.WordTrace tailWord_1472090 prefixEnd_1472090 251963245559083558268329 := by
  unfold tailWord_1472090
  simp only [CollatzResearch.WordTrace]
  refine ⟨13422883309219204450275431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35794355491251211867401149 13422883309219204450275431)
  ·
    refine ⟨20134324963828806675413147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13422883309219204450275431 20134324963828806675413147)
    ·
      refine ⟨30201487445743210013119721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20134324963828806675413147 30201487445743210013119721)
      ·
        refine ⟨22651115584307407509839791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30201487445743210013119721 22651115584307407509839791)
        ·
          refine ⟨33976673376461111264759687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22651115584307407509839791 33976673376461111264759687)
          ·
            refine ⟨50965010064691666897139531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33976673376461111264759687 50965010064691666897139531)
            ·
              refine ⟨76447515097037500345709297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50965010064691666897139531 76447515097037500345709297)
              ·
                refine ⟨57335636322778125259281973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76447515097037500345709297 57335636322778125259281973)
                ·
                  refine ⟨5375215905260449243057685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57335636322778125259281973 5375215905260449243057685)
                  ·
                    refine ⟨251963245559083558268329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5375215905260449243057685 251963245559083558268329)
                    ·
                      rfl

theorem cell23_1472090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_1472090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472090 prefixEnd_1472090 := by exact prefixLift 1472090
  have htrace : WordTrace (prefixWord ++ tailWord_1472090) baseStart_1472090 baseEnd_1472090 := by
    simpa [prefixWord, tailWord_1472090, baseEnd_1472090] using wordTrace_append hprefix tailTrace_1472090
  have hstable : (prefixWord ++ tailWord_1472090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472090).length < 2 ^ (prefixWord ++ tailWord_1472090).sum := by decide
  have hdescent : baseEnd_1472090 < baseStart_1472090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472097 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_1472097 : Nat := 118140960795 + 1472097 * 2 ^ 59
def prefixEnd_1472097 : Nat := 4983230072969 + 3 ^ 40 * 1472097 * 2
def baseEnd_1472097 : Nat := 755893331041832147417455

theorem tailTrace_1472097 : CollatzResearch.WordTrace tailWord_1472097 prefixEnd_1472097 755893331041832147417455 := by
  unfold tailWord_1472097
  simp only [CollatzResearch.WordTrace]
  refine ⟨53691788547851457996606545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35794525698567638664404363 53691788547851457996606545)
  ·
    refine ⟨40268841410888593497454909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53691788547851457996606545 40268841410888593497454909)
    ·
      refine ⟨15100815529083222561545591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40268841410888593497454909 15100815529083222561545591)
      ·
        refine ⟨22651223293624833842318387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15100815529083222561545591 22651223293624833842318387)
        ·
          refine ⟨33976834940437250763477581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22651223293624833842318387 33976834940437250763477581)
          ·
            refine ⟨12741313102663969036304093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33976834940437250763477581 12741313102663969036304093)
            ·
              refine ⟨4777992413498988388614035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12741313102663969036304093 4777992413498988388614035)
              ·
                refine ⟨7166988620248482582921053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4777992413498988388614035 7166988620248482582921053)
                ·
                  refine ⟨2687620732593180968595395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7166988620248482582921053 2687620732593180968595395)
                  ·
                    refine ⟨4031431098889771452893093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2687620732593180968595395 4031431098889771452893093)
                    ·
                      refine ⟨755893331041832147417455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4031431098889771452893093 755893331041832147417455)
                      ·
                        rfl

theorem cell23_1472097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_1472097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472097 prefixEnd_1472097 := by exact prefixLift 1472097
  have htrace : WordTrace (prefixWord ++ tailWord_1472097) baseStart_1472097 baseEnd_1472097 := by
    simpa [prefixWord, tailWord_1472097, baseEnd_1472097] using wordTrace_append hprefix tailTrace_1472097
  have hstable : (prefixWord ++ tailWord_1472097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472097).length < 2 ^ (prefixWord ++ tailWord_1472097).sum := by decide
  have hdescent : baseEnd_1472097 < baseStart_1472097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472101 : List Nat := [1, 3, 1, 3, 3, 2, 2, 1, 2, 3, 2]
def baseStart_1472101 : Nat := 118140960795 + 1472101 * 2 ^ 59
def prefixEnd_1472101 : Nat := 4983230072969 + 3 ^ 40 * 1472101 * 2
def baseEnd_1472101 : Nat := 755895384964450131767437

theorem tailTrace_1472101 : CollatzResearch.WordTrace tailWord_1472101 prefixEnd_1472101 755895384964450131767437 := by
  unfold tailWord_1472101
  simp only [CollatzResearch.WordTrace]
  refine ⟨53691934439836966679752157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35794622959891311119834771 53691934439836966679752157)
  ·
    refine ⟨20134475414938862504907059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53691934439836966679752157 20134475414938862504907059)
    ·
      refine ⟨30201713122408293757360589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20134475414938862504907059 30201713122408293757360589)
      ·
        refine ⟨11325642420903110159010221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30201713122408293757360589 11325642420903110159010221)
        ·
          refine ⟨4247115907838666309628833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11325642420903110159010221 4247115907838666309628833)
          ·
            refine ⟨3185336930878999732221625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4247115907838666309628833 3185336930878999732221625)
            ·
              refine ⟨2389002698159249799166219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3185336930878999732221625 2389002698159249799166219)
              ·
                refine ⟨3583504047238874698749329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2389002698159249799166219 3583504047238874698749329)
                ·
                  refine ⟨2687628035429156024061997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3583504047238874698749329 2687628035429156024061997)
                  ·
                    refine ⟨1007860513285933509023249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2687628035429156024061997 1007860513285933509023249)
                    ·
                      refine ⟨755895384964450131767437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007860513285933509023249 755895384964450131767437)
                      ·
                        rfl

theorem cell23_1472101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_1472101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472101 prefixEnd_1472101 := by exact prefixLift 1472101
  have htrace : WordTrace (prefixWord ++ tailWord_1472101) baseStart_1472101 baseEnd_1472101 := by
    simpa [prefixWord, tailWord_1472101, baseEnd_1472101] using wordTrace_append hprefix tailTrace_1472101
  have hstable : (prefixWord ++ tailWord_1472101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472101).length < 2 ^ (prefixWord ++ tailWord_1472101).sum := by decide
  have hdescent : baseEnd_1472101 < baseStart_1472101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472125 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_1472125 : Nat := 118140960795 + 1472125 * 2 ^ 59
def prefixEnd_1472125 : Nat := 4983230072969 + 3 ^ 40 * 1472125 * 2
def baseEnd_1472125 : Nat := 755907708500158037867327

theorem tailTrace_1472125 : CollatzResearch.WordTrace tailWord_1472125 prefixEnd_1472125 755907708500158037867327 := by
  unfold tailWord_1472125
  simp only [CollatzResearch.WordTrace]
  refine ⟨53692809791750018778625829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35795206527833345852417219 53692809791750018778625829)
  ·
    refine ⟨10067401835953128520992343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53692809791750018778625829 10067401835953128520992343)
    ·
      refine ⟨15101102753929692781488515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067401835953128520992343 15101102753929692781488515)
      ·
        refine ⟨22651654130894539172232773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15101102753929692781488515 22651654130894539172232773)
        ·
          refine ⟨4247185149542726094793645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22651654130894539172232773 4247185149542726094793645)
          ·
            refine ⟨1592694431078522285547617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4247185149542726094793645 1592694431078522285547617)
            ·
              refine ⟨1194520823308891714160713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1592694431078522285547617 1194520823308891714160713)
              ·
                refine ⟨895890617481668785620535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194520823308891714160713 895890617481668785620535)
                ·
                  refine ⟨1343835926222503178430803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895890617481668785620535 1343835926222503178430803)
                  ·
                    refine ⟨2015753889333754767646205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1343835926222503178430803 2015753889333754767646205)
                    ·
                      refine ⟨755907708500158037867327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2015753889333754767646205 755907708500158037867327)
                      ·
                        rfl

theorem cell23_1472125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_1472125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472125 prefixEnd_1472125 := by exact prefixLift 1472125
  have htrace : WordTrace (prefixWord ++ tailWord_1472125) baseStart_1472125 baseEnd_1472125 := by
    simpa [prefixWord, tailWord_1472125, baseEnd_1472125] using wordTrace_append hprefix tailTrace_1472125
  have hstable : (prefixWord ++ tailWord_1472125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472125).length < 2 ^ (prefixWord ++ tailWord_1472125).sum := by decide
  have hdescent : baseEnd_1472125 < baseStart_1472125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472164 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_1472164 : Nat := 118140960795 + 1472164 * 2 ^ 59
def prefixEnd_1472164 : Nat := 4983230072969 + 3 ^ 40 * 1472164 * 2
def baseEnd_1472164 : Nat := 755927734245683385279647

theorem tailTrace_1472164 : CollatzResearch.WordTrace tailWord_1472164 prefixEnd_1472164 755927734245683385279647 := by
  unfold tailWord_1472164
  simp only [CollatzResearch.WordTrace]
  refine ⟨26847116119304364219647773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35796154825739152292863697 26847116119304364219647773)
  ·
    refine ⟨10067668544739136582367915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26847116119304364219647773 10067668544739136582367915)
    ·
      refine ⟨15101502817108704873551873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10067668544739136582367915 15101502817108704873551873)
      ·
        refine ⟨11326127112831528655163905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15101502817108704873551873 11326127112831528655163905)
        ·
          refine ⟨8494595334623646491372929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11326127112831528655163905 8494595334623646491372929)
          ·
            refine ⟨6370946500967734868529697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8494595334623646491372929 6370946500967734868529697)
            ·
              refine ⟨4778209875725801151397273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6370946500967734868529697 4778209875725801151397273)
              ·
                refine ⟨3583657406794350863547955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4778209875725801151397273 3583657406794350863547955)
                ·
                  refine ⟨5375486110191526295321933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3583657406794350863547955 5375486110191526295321933)
                  ·
                    refine ⟨2015807291321822360745725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5375486110191526295321933 2015807291321822360745725)
                    ·
                      refine ⟨755927734245683385279647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2015807291321822360745725 755927734245683385279647)
                      ·
                        rfl

theorem cell23_1472164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_1472164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472164 prefixEnd_1472164 := by exact prefixLift 1472164
  have htrace : WordTrace (prefixWord ++ tailWord_1472164) baseStart_1472164 baseEnd_1472164 := by
    simpa [prefixWord, tailWord_1472164, baseEnd_1472164] using wordTrace_append hprefix tailTrace_1472164
  have hstable : (prefixWord ++ tailWord_1472164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472164).length < 2 ^ (prefixWord ++ tailWord_1472164).sum := by decide
  have hdescent : baseEnd_1472164 < baseStart_1472164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472182 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1472182 : Nat := 118140960795 + 1472182 * 2 ^ 59
def prefixEnd_1472182 : Nat := 4983230072969 + 3 ^ 40 * 1472182 * 2
def baseEnd_1472182 : Nat := 755936976897464314854565

theorem tailTrace_1472182 : CollatzResearch.WordTrace tailWord_1472182 prefixEnd_1472182 755936976897464314854565 := by
  unfold tailWord_1472182
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355930547033969844590675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35796592501695678342300533 3355930547033969844590675)
  ·
    refine ⟨5033895820550954766886013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3355930547033969844590675 5033895820550954766886013)
    ·
      refine ⟨1887710932706608037582255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5033895820550954766886013 1887710932706608037582255)
      ·
        refine ⟨2831566399059912056373383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887710932706608037582255 2831566399059912056373383)
        ·
          refine ⟨4247349598589868084560075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2831566399059912056373383 4247349598589868084560075)
          ·
            refine ⟨6371024397884802126840113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4247349598589868084560075 6371024397884802126840113)
            ·
              refine ⟨4778268298413601595130085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6371024397884802126840113 4778268298413601595130085)
              ·
                refine ⟨895925305952550299086891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4778268298413601595130085 895925305952550299086891)
                ·
                  refine ⟨1343887958928825448630337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 895925305952550299086891 1343887958928825448630337)
                  ·
                    refine ⟨1007915969196619086472753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343887958928825448630337 1007915969196619086472753)
                    ·
                      refine ⟨755936976897464314854565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007915969196619086472753 755936976897464314854565)
                      ·
                        rfl

theorem cell23_1472182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1472182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472182 prefixEnd_1472182 := by exact prefixLift 1472182
  have htrace : WordTrace (prefixWord ++ tailWord_1472182) baseStart_1472182 baseEnd_1472182 := by
    simpa [prefixWord, tailWord_1472182, baseEnd_1472182] using wordTrace_append hprefix tailTrace_1472182
  have hstable : (prefixWord ++ tailWord_1472182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472182).length < 2 ^ (prefixWord ++ tailWord_1472182).sum := by decide
  have hdescent : baseEnd_1472182 < baseStart_1472182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472207 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3]
def baseStart_1472207 : Nat := 118140960795 + 1472207 * 2 ^ 59
def prefixEnd_1472207 : Nat := 4983230072969 + 3 ^ 40 * 1472207 * 2
def baseEnd_1472207 : Nat := 755949813913826717041949

theorem tailTrace_1472207 : CollatzResearch.WordTrace tailWord_1472207 prefixEnd_1472207 755949813913826717041949 := by
  unfold tailWord_1472207
  simp only [CollatzResearch.WordTrace]
  refine ⟨53695800577452946783110875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35797200384968631188740583 53695800577452946783110875)
  ·
    refine ⟨80543700866179420174666313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53695800577452946783110875 80543700866179420174666313)
    ·
      refine ⟨60407775649634565130999735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80543700866179420174666313 60407775649634565130999735)
      ·
        refine ⟨90611663474451847696499603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60407775649634565130999735 90611663474451847696499603)
        ·
          refine ⟨135917495211677771544749405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90611663474451847696499603 135917495211677771544749405)
          ·
            refine ⟨50969060704379164329281027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135917495211677771544749405 50969060704379164329281027)
            ·
              refine ⟨76453591056568746493921541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50969060704379164329281027 76453591056568746493921541)
              ·
                refine ⟨14335048323106639967610289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76453591056568746493921541 14335048323106639967610289)
                ·
                  refine ⟨10751286242329979975707717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14335048323106639967610289 10751286242329979975707717)
                  ·
                    refine ⟨2015866170436871245445197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10751286242329979975707717 2015866170436871245445197)
                    ·
                      refine ⟨755949813913826717041949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2015866170436871245445197 755949813913826717041949)
                      ·
                        rfl

theorem cell23_1472207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_1472207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472207 prefixEnd_1472207 := by exact prefixLift 1472207
  have htrace : WordTrace (prefixWord ++ tailWord_1472207) baseStart_1472207 baseEnd_1472207 := by
    simpa [prefixWord, tailWord_1472207, baseEnd_1472207] using wordTrace_append hprefix tailTrace_1472207
  have hstable : (prefixWord ++ tailWord_1472207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472207).length < 2 ^ (prefixWord ++ tailWord_1472207).sum := by decide
  have hdescent : baseEnd_1472207 < baseStart_1472207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472238 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_1472238 : Nat := 118140960795 + 1472238 * 2 ^ 59
def prefixEnd_1472238 : Nat := 4983230072969 + 3 ^ 40 * 1472238 * 2
def baseEnd_1472238 : Nat := 755965731814116095754307

theorem tailTrace_1472238 : CollatzResearch.WordTrace tailWord_1472238 prefixEnd_1472238 755965731814116095754307 := by
  unfold tailWord_1472238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6712116405042579884686171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35797954160227092718326245 6712116405042579884686171)
  ·
    refine ⟨10068174607563869827029257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6712116405042579884686171 10068174607563869827029257)
    ·
      refine ⟨7551130955672902370271943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10068174607563869827029257 7551130955672902370271943)
      ·
        refine ⟨11326696433509353555407915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551130955672902370271943 11326696433509353555407915)
        ·
          refine ⟨16990044650264030333111873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11326696433509353555407915 16990044650264030333111873)
          ·
            refine ⟨12742533487698022749833905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16990044650264030333111873 12742533487698022749833905)
            ·
              refine ⟨9556900115773517062375429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12742533487698022749833905 9556900115773517062375429)
              ·
                refine ⟨1791918771707534449195393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9556900115773517062375429 1791918771707534449195393)
                ·
                  refine ⟨1343939078780650836896545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1791918771707534449195393 1343939078780650836896545)
                  ·
                    refine ⟨1007954309085488127672409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1343939078780650836896545 1007954309085488127672409)
                    ·
                      refine ⟨755965731814116095754307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1007954309085488127672409 755965731814116095754307)
                      ·
                        rfl

theorem cell23_1472238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_1472238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472238 prefixEnd_1472238 := by exact prefixLift 1472238
  have htrace : WordTrace (prefixWord ++ tailWord_1472238) baseStart_1472238 baseEnd_1472238 := by
    simpa [prefixWord, tailWord_1472238, baseEnd_1472238] using wordTrace_append hprefix tailTrace_1472238
  have hstable : (prefixWord ++ tailWord_1472238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472238).length < 2 ^ (prefixWord ++ tailWord_1472238).sum := by decide
  have hdescent : baseEnd_1472238 < baseStart_1472238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472257 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1472257 : Nat := 118140960795 + 1472257 * 2 ^ 59
def prefixEnd_1472257 : Nat := 4983230072969 + 3 ^ 40 * 1472257 * 2
def baseEnd_1472257 : Nat := 251991829315517173805573

theorem tailTrace_1472257 : CollatzResearch.WordTrace tailWord_1472257 prefixEnd_1472257 251991829315517173805573 := by
  unfold tailWord_1472257
  simp only [CollatzResearch.WordTrace]
  refine ⟨53697624227271805322431025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35798416151514536881620683 53697624227271805322431025)
  ·
    refine ⟨40273218170453853991823269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53697624227271805322431025 40273218170453853991823269)
    ·
      refine ⟨7551228406960097623466863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40273218170453853991823269 7551228406960097623466863)
      ·
        refine ⟨11326842610440146435200295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551228406960097623466863 11326842610440146435200295)
        ·
          refine ⟨16990263915660219652800443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11326842610440146435200295 16990263915660219652800443)
          ·
            refine ⟨25485395873490329479200665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16990263915660219652800443 25485395873490329479200665)
            ·
              refine ⟨19114046905117747109400499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25485395873490329479200665 19114046905117747109400499)
              ·
                refine ⟨28671070357676620664100749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19114046905117747109400499 28671070357676620664100749)
                ·
                  refine ⟨10751651384128732749037781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28671070357676620664100749 10751651384128732749037781)
                  ·
                    refine ⟨251991829315517173805573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10751651384128732749037781 251991829315517173805573)
                    ·
                      rfl

theorem cell23_1472257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1472257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472257 prefixEnd_1472257 := by exact prefixLift 1472257
  have htrace : WordTrace (prefixWord ++ tailWord_1472257) baseStart_1472257 baseEnd_1472257 := by
    simpa [prefixWord, tailWord_1472257, baseEnd_1472257] using wordTrace_append hprefix tailTrace_1472257
  have hstable : (prefixWord ++ tailWord_1472257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472257).length < 2 ^ (prefixWord ++ tailWord_1472257).sum := by decide
  have hdescent : baseEnd_1472257 < baseStart_1472257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472338 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1472338 : Nat := 118140960795 + 1472338 * 2 ^ 59
def prefixEnd_1472338 : Nat := 4983230072969 + 3 ^ 40 * 1472338 * 2
def baseEnd_1472338 : Nat := 252005693293188568167949

theorem tailTrace_1472338 : CollatzResearch.WordTrace tailWord_1472338 prefixEnd_1472338 252005693293188568167949 := by
  unfold tailWord_1472338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13425144634994589039032417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35800385693318904104086445 13425144634994589039032417)
  ·
    refine ⟨10068858476245941779274313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13425144634994589039032417 10068858476245941779274313)
    ·
      refine ⟨7551643857184456334455735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10068858476245941779274313 7551643857184456334455735)
      ·
        refine ⟨11327465785776684501683603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7551643857184456334455735 11327465785776684501683603)
        ·
          refine ⟨16991198678665026752525405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11327465785776684501683603 16991198678665026752525405)
          ·
            refine ⟨6371699504499385032197027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16991198678665026752525405 6371699504499385032197027)
            ·
              refine ⟨9557549256749077548295541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6371699504499385032197027 9557549256749077548295541)
              ·
                refine ⟨896020242820226020152707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9557549256749077548295541 896020242820226020152707)
                ·
                  refine ⟨1344030364230339030229061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896020242820226020152707 1344030364230339030229061)
                  ·
                    refine ⟨252005693293188568167949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344030364230339030229061 252005693293188568167949)
                    ·
                      rfl

theorem cell23_1472338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1472338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472338 prefixEnd_1472338 := by exact prefixLift 1472338
  have htrace : WordTrace (prefixWord ++ tailWord_1472338) baseStart_1472338 baseEnd_1472338 := by
    simpa [prefixWord, tailWord_1472338, baseEnd_1472338] using wordTrace_append hprefix tailTrace_1472338
  have hstable : (prefixWord ++ tailWord_1472338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472338).length < 2 ^ (prefixWord ++ tailWord_1472338).sum := by decide
  have hdescent : baseEnd_1472338 < baseStart_1472338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472351 : List Nat := [1, 1, 2, 3, 1, 6, 1, 2, 6]
def baseStart_1472351 : Nat := 118140960795 + 1472351 * 2 ^ 59
def prefixEnd_1472351 : Nat := 4983230072969 + 3 ^ 40 * 1472351 * 2
def baseEnd_1472351 : Nat := 84002639458674905960143

theorem tailTrace_1472351 : CollatzResearch.WordTrace tailWord_1472351 prefixEnd_1472351 84002639458674905960143 := by
  unfold tailWord_1472351
  simp only [CollatzResearch.WordTrace]
  refine ⟨53701052688931259376352907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35800701792620839584235271 53701052688931259376352907)
  ·
    refine ⟨80551579033396889064529361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53701052688931259376352907 80551579033396889064529361)
    ·
      refine ⟨60413684275047666798397021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80551579033396889064529361 60413684275047666798397021)
      ·
        refine ⟨22655131603142875049398883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60413684275047666798397021 22655131603142875049398883)
        ·
          refine ⟨33982697404714312574098325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22655131603142875049398883 33982697404714312574098325)
          ·
            refine ⟨1592938940845983401910859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33982697404714312574098325 1592938940845983401910859)
            ·
              refine ⟨2389408411268975102866289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1592938940845983401910859 2389408411268975102866289)
              ·
                refine ⟨1792056308451731327149717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2389408411268975102866289 1792056308451731327149717)
                ·
                  refine ⟨84002639458674905960143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1792056308451731327149717 84002639458674905960143)
                  ·
                    rfl

theorem cell23_1472351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 1, 2, 6].length) (baseStart_1472351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472351 prefixEnd_1472351 := by exact prefixLift 1472351
  have htrace : WordTrace (prefixWord ++ tailWord_1472351) baseStart_1472351 baseEnd_1472351 := by
    simpa [prefixWord, tailWord_1472351, baseEnd_1472351] using wordTrace_append hprefix tailTrace_1472351
  have hstable : (prefixWord ++ tailWord_1472351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472351).length < 2 ^ (prefixWord ++ tailWord_1472351).sum := by decide
  have hdescent : baseEnd_1472351 < baseStart_1472351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472401 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_1472401 : Nat := 118140960795 + 1472401 * 2 ^ 59
def prefixEnd_1472401 : Nat := 4983230072969 + 3 ^ 40 * 1472401 * 2
def baseEnd_1472401 : Nat := 756049429160798958016057

theorem tailTrace_1472401 : CollatzResearch.WordTrace tailWord_1472401 prefixEnd_1472401 756049429160798958016057 := by
  unfold tailWord_1472401
  simp only [CollatzResearch.WordTrace]
  refine ⟨53702876338750117915673057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35801917559166745277115371 53702876338750117915673057)
  ·
    refine ⟨40277157254062588436754793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53702876338750117915673057 40277157254062588436754793)
    ·
      refine ⟨30207867940546941327566095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40277157254062588436754793 30207867940546941327566095)
      ·
        refine ⟨45311801910820411991349143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30207867940546941327566095 45311801910820411991349143)
        ·
          refine ⟨67967702866230617987023715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45311801910820411991349143 67967702866230617987023715)
          ·
            refine ⟨101951554299345926980535573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67967702866230617987023715 101951554299345926980535573)
            ·
              refine ⟨4778979107781840327212605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101951554299345926980535573 4778979107781840327212605)
              ·
                refine ⟨1792117165418190122704727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4778979107781840327212605 1792117165418190122704727)
                ·
                  refine ⟨2688175748127285184057091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792117165418190122704727 2688175748127285184057091)
                  ·
                    refine ⟨4032263622190927776085637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2688175748127285184057091 4032263622190927776085637)
                    ·
                      refine ⟨756049429160798958016057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4032263622190927776085637 756049429160798958016057)
                      ·
                        rfl

theorem cell23_1472401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_1472401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472401 prefixEnd_1472401 := by exact prefixLift 1472401
  have htrace : WordTrace (prefixWord ++ tailWord_1472401) baseStart_1472401 baseEnd_1472401 := by
    simpa [prefixWord, tailWord_1472401, baseEnd_1472401] using wordTrace_append hprefix tailTrace_1472401
  have hstable : (prefixWord ++ tailWord_1472401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472401).length < 2 ^ (prefixWord ++ tailWord_1472401).sum := by decide
  have hdescent : baseEnd_1472401 < baseStart_1472401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472406 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1472406 : Nat := 118140960795 + 1472406 * 2 ^ 59
def prefixEnd_1472406 : Nat := 4983230072969 + 3 ^ 40 * 1472406 * 2
def baseEnd_1472406 : Nat := 252017332188023812817845

theorem tailTrace_1472406 : CollatzResearch.WordTrace tailWord_1472406 prefixEnd_1472406 252017332188023812817845 := by
  unfold tailWord_1472406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3356441168983250235600317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35802039135821335846403381 3356441168983250235600317)
  ·
    refine ⟨1258665438368718838350119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3356441168983250235600317 1258665438368718838350119)
    ·
      refine ⟨1887998157553078257525179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1258665438368718838350119 1887998157553078257525179)
      ·
        refine ⟨2831997236329617386287769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1887998157553078257525179 2831997236329617386287769)
        ·
          refine ⟨2123997927247213039715827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2831997236329617386287769 2123997927247213039715827)
          ·
            refine ⟨3185996890870819559573741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2123997927247213039715827 3185996890870819559573741)
            ·
              refine ⟨1194748834076557334840153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3185996890870819559573741 1194748834076557334840153)
              ·
                refine ⟨896061625557418001130115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194748834076557334840153 896061625557418001130115)
                ·
                  refine ⟨1344092438336127001695173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896061625557418001130115 1344092438336127001695173)
                  ·
                    refine ⟨252017332188023812817845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344092438336127001695173 252017332188023812817845)
                    ·
                      rfl

theorem cell23_1472406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1472406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472406 prefixEnd_1472406 := by exact prefixLift 1472406
  have htrace : WordTrace (prefixWord ++ tailWord_1472406) baseStart_1472406 baseEnd_1472406 := by
    simpa [prefixWord, tailWord_1472406, baseEnd_1472406] using wordTrace_append hprefix tailTrace_1472406
  have hstable : (prefixWord ++ tailWord_1472406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472406).length < 2 ^ (prefixWord ++ tailWord_1472406).sum := by decide
  have hdescent : baseEnd_1472406 < baseStart_1472406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472464 : List Nat := [2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_1472464 : Nat := 118140960795 + 1472464 * 2 ^ 59
def prefixEnd_1472464 : Nat := 4983230072969 + 3 ^ 40 * 1472464 * 2
def baseEnd_1472464 : Nat := 756081778442032211528267

theorem tailTrace_1472464 : CollatzResearch.WordTrace tailWord_1472464 prefixEnd_1472464 756081778442032211528267 := by
  unfold tailWord_1472464
  simp only [CollatzResearch.WordTrace]
  refine ⟨26852587068760939837608223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35803449425014586450144297 26852587068760939837608223)
  ·
    refine ⟨40278880603141409756412335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26852587068760939837608223 40278880603141409756412335)
    ·
      refine ⟨60418320904712114634618503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40278880603141409756412335 60418320904712114634618503)
      ·
        refine ⟨90627481357068171951927755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60418320904712114634618503 90627481357068171951927755)
        ·
          refine ⟨135941222035602257927891633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90627481357068171951927755 135941222035602257927891633)
          ·
            refine ⟨101955916526701693445918725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135941222035602257927891633 101955916526701693445918725)
            ·
              refine ⟨19116734348756567521109761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101955916526701693445918725 19116734348756567521109761)
              ·
                refine ⟨14337550761567425640832321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19116734348756567521109761 14337550761567425640832321)
                ·
                  refine ⟨10753163071175569230624241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14337550761567425640832321 10753163071175569230624241)
                  ·
                    refine ⟨8064872303381676922968181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10753163071175569230624241 8064872303381676922968181)
                    ·
                      refine ⟨756081778442032211528267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8064872303381676922968181 756081778442032211528267)
                      ·
                        rfl

theorem cell23_1472464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_1472464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472464 prefixEnd_1472464 := by exact prefixLift 1472464
  have htrace : WordTrace (prefixWord ++ tailWord_1472464) baseStart_1472464 baseEnd_1472464 := by
    simpa [prefixWord, tailWord_1472464, baseEnd_1472464] using wordTrace_append hprefix tailTrace_1472464
  have hstable : (prefixWord ++ tailWord_1472464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472464).length < 2 ^ (prefixWord ++ tailWord_1472464).sum := by decide
  have hdescent : baseEnd_1472464 < baseStart_1472464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472469 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 1, 2, 2]
def baseStart_1472469 : Nat := 118140960795 + 1472469 * 2 ^ 59
def prefixEnd_1472469 : Nat := 4983230072969 + 3 ^ 40 * 1472469 * 2
def baseEnd_1472469 : Nat := 756084345845304691965745

theorem tailTrace_1472469 : CollatzResearch.WordTrace tailWord_1472469 prefixEnd_1472469 756084345845304691965745 := by
  unfold tailWord_1472469
  simp only [CollatzResearch.WordTrace]
  refine ⟨53705356502503765529148461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35803571001669177019432307 53705356502503765529148461)
  ·
    refine ⟨20139508688438912073430673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53705356502503765529148461 20139508688438912073430673)
    ·
      refine ⟨15104631516329184055073005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20139508688438912073430673 15104631516329184055073005)
      ·
        refine ⟨5664236818623444020652377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15104631516329184055073005 5664236818623444020652377)
        ·
          refine ⟨4248177613967583015489283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5664236818623444020652377 4248177613967583015489283)
          ·
            refine ⟨6372266420951374523233925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4248177613967583015489283 6372266420951374523233925)
            ·
              refine ⟨1194799953928382723106361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6372266420951374523233925 1194799953928382723106361)
              ·
                refine ⟨896099965446287042329771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1194799953928382723106361 896099965446287042329771)
                ·
                  refine ⟨1344149948169430563494657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896099965446287042329771 1344149948169430563494657)
                  ·
                    refine ⟨1008112461127072922620993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344149948169430563494657 1008112461127072922620993)
                    ·
                      refine ⟨756084345845304691965745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008112461127072922620993 756084345845304691965745)
                      ·
                        rfl

theorem cell23_1472469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_1472469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472469 prefixEnd_1472469 := by exact prefixLift 1472469
  have htrace : WordTrace (prefixWord ++ tailWord_1472469) baseStart_1472469 baseEnd_1472469 := by
    simpa [prefixWord, tailWord_1472469, baseEnd_1472469] using wordTrace_append hprefix tailTrace_1472469
  have hstable : (prefixWord ++ tailWord_1472469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472469).length < 2 ^ (prefixWord ++ tailWord_1472469).sum := by decide
  have hdescent : baseEnd_1472469 < baseStart_1472469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472508 : List Nat := [2, 2, 2, 1, 2, 2, 1, 4, 1, 4, 2]
def baseStart_1472508 : Nat := 118140960795 + 1472508 * 2 ^ 59
def prefixEnd_1472508 : Nat := 4983230072969 + 3 ^ 40 * 1472508 * 2
def baseEnd_1472508 : Nat := 756104371590830039378065

theorem tailTrace_1472508 : CollatzResearch.WordTrace tailWord_1472508 prefixEnd_1472508 756104371590830039378065 := by
  unfold tailWord_1472508
  simp only [CollatzResearch.WordTrace]
  refine ⟨26853389474681237594909089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35804519299574983459878785 26853389474681237594909089)
  ·
    refine ⟨20140042106010928196181817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26853389474681237594909089 20140042106010928196181817)
    ·
      refine ⟨15105031579508196147136363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20140042106010928196181817 15105031579508196147136363)
      ·
        refine ⟨22657547369262294220704545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15105031579508196147136363 22657547369262294220704545)
        ·
          refine ⟨16993160526946720665528409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22657547369262294220704545 16993160526946720665528409)
          ·
            refine ⟨12744870395210040499146307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16993160526946720665528409 12744870395210040499146307)
            ·
              refine ⟨19117305592815060748719461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12744870395210040499146307 19117305592815060748719461)
              ·
                refine ⟨3584494798652823890384899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19117305592815060748719461 3584494798652823890384899)
                ·
                  refine ⟨5376742197979235835577349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3584494798652823890384899 5376742197979235835577349)
                  ·
                    refine ⟨1008139162121106719170753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5376742197979235835577349 1008139162121106719170753)
                    ·
                      refine ⟨756104371590830039378065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008139162121106719170753 756104371590830039378065)
                      ·
                        rfl

theorem cell23_1472508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_1472508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472508 prefixEnd_1472508 := by exact prefixLift 1472508
  have htrace : WordTrace (prefixWord ++ tailWord_1472508) baseStart_1472508 baseEnd_1472508 := by
    simpa [prefixWord, tailWord_1472508, baseEnd_1472508] using wordTrace_append hprefix tailTrace_1472508
  have hstable : (prefixWord ++ tailWord_1472508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472508).length < 2 ^ (prefixWord ++ tailWord_1472508).sum := by decide
  have hdescent : baseEnd_1472508 < baseStart_1472508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472561 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 7]
def baseStart_1472561 : Nat := 118140960795 + 1472561 * 2 ^ 59
def prefixEnd_1472561 : Nat := 4983230072969 + 3 ^ 40 * 1472561 * 2
def baseEnd_1472561 : Nat := 252043862021839444005107

theorem tailTrace_1472561 : CollatzResearch.WordTrace tailWord_1472561 prefixEnd_1472561 252043862021839444005107 := by
  unfold tailWord_1472561
  simp only [CollatzResearch.WordTrace]
  refine ⟨53708712018170465241497537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35805808012113643494331691 53708712018170465241497537)
  ·
    refine ⟨40281534013627848931123153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53708712018170465241497537 40281534013627848931123153)
    ·
      refine ⟨30211150510220886698342365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40281534013627848931123153 30211150510220886698342365)
      ·
        refine ⟨11329181441332832511878387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30211150510220886698342365 11329181441332832511878387)
        ·
          refine ⟨16993772161999248767817581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11329181441332832511878387 16993772161999248767817581)
          ·
            refine ⟨6372664560749718287931593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16993772161999248767817581 6372664560749718287931593)
            ·
              refine ⟨4779498420562288715948695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6372664560749718287931593 4779498420562288715948695)
              ·
                refine ⟨7169247630843433073923043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4779498420562288715948695 7169247630843433073923043)
                ·
                  refine ⟨10753871446265149610884565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7169247630843433073923043 10753871446265149610884565)
                  ·
                    refine ⟨252043862021839444005107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10753871446265149610884565 252043862021839444005107)
                    ·
                      rfl

theorem cell23_1472561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_1472561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472561 prefixEnd_1472561 := by exact prefixLift 1472561
  have htrace : WordTrace (prefixWord ++ tailWord_1472561) baseStart_1472561 baseEnd_1472561 := by
    simpa [prefixWord, tailWord_1472561, baseEnd_1472561] using wordTrace_append hprefix tailTrace_1472561
  have hstable : (prefixWord ++ tailWord_1472561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472561).length < 2 ^ (prefixWord ++ tailWord_1472561).sum := by decide
  have hdescent : baseEnd_1472561 < baseStart_1472561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472611 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1472611 : Nat := 118140960795 + 1472611 * 2 ^ 59
def prefixEnd_1472611 : Nat := 4983230072969 + 3 ^ 40 * 1472611 * 2
def baseEnd_1472611 : Nat := 756157260098243136390091

theorem tailTrace_1472611 : CollatzResearch.WordTrace tailWord_1472611 prefixEnd_1472611 756157260098243136390091 := by
  unfold tailWord_1472611
  simp only [CollatzResearch.WordTrace]
  refine ⟨53710535667989323780817687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35807023778659549187211791 53710535667989323780817687)
  ·
    refine ⟨80565803501983985671226531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53710535667989323780817687 80565803501983985671226531)
    ·
      refine ⟨120848705252975978506839797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80565803501983985671226531 120848705252975978506839797)
      ·
        refine ⟨11329566117466497985016231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120848705252975978506839797 11329566117466497985016231)
        ·
          refine ⟨16994349176199746977524347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11329566117466497985016231 16994349176199746977524347)
          ·
            refine ⟨25491523764299620466286521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16994349176199746977524347 25491523764299620466286521)
            ·
              refine ⟨19118642823224715349714891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25491523764299620466286521 19118642823224715349714891)
              ·
                refine ⟨28677964234837073024572337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19118642823224715349714891 28677964234837073024572337)
                ·
                  refine ⟨21508473176127804768429253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28677964234837073024572337 21508473176127804768429253)
                  ·
                    refine ⟨4032838720523963394080485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21508473176127804768429253 4032838720523963394080485)
                    ·
                      refine ⟨756157260098243136390091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4032838720523963394080485 756157260098243136390091)
                      ·
                        rfl

theorem cell23_1472611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1472611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472611 prefixEnd_1472611 := by exact prefixLift 1472611
  have htrace : WordTrace (prefixWord ++ tailWord_1472611) baseStart_1472611 baseEnd_1472611 := by
    simpa [prefixWord, tailWord_1472611, baseEnd_1472611] using wordTrace_append hprefix tailTrace_1472611
  have hstable : (prefixWord ++ tailWord_1472611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472611).length < 2 ^ (prefixWord ++ tailWord_1472611).sum := by decide
  have hdescent : baseEnd_1472611 < baseStart_1472611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472625 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 1, 4]
def baseStart_1472625 : Nat := 118140960795 + 1472625 * 2 ^ 59
def prefixEnd_1472625 : Nat := 4983230072969 + 3 ^ 40 * 1472625 * 2
def baseEnd_1472625 : Nat := 252054816275802027205009

theorem tailTrace_1472625 : CollatzResearch.WordTrace tailWord_1472625 prefixEnd_1472625 252054816275802027205009 := by
  unfold tailWord_1472625
  simp only [CollatzResearch.WordTrace]
  refine ⟨53711046289938604171827329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35807364193292402781218219 53711046289938604171827329)
  ·
    refine ⟨40283284717453953128870497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53711046289938604171827329 40283284717453953128870497)
    ·
      refine ⟨30212463538090464846652873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40283284717453953128870497 30212463538090464846652873)
      ·
        refine ⟨22659347653567848634989655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30212463538090464846652873 22659347653567848634989655)
        ·
          refine ⟨33989021480351772952484483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659347653567848634989655 33989021480351772952484483)
          ·
            refine ⟨50983532220527659428726725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33989021480351772952484483 50983532220527659428726725)
            ·
              refine ⟨9559412291348936142886261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50983532220527659428726725 9559412291348936142886261)
              ·
                refine ⟨896194902313962763395587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9559412291348936142886261 896194902313962763395587)
                ·
                  refine ⟨1344292353470944145093381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896194902313962763395587 1344292353470944145093381)
                  ·
                    refine ⟨252054816275802027205009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344292353470944145093381 252054816275802027205009)
                    ·
                      rfl

theorem cell23_1472625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_1472625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472625 prefixEnd_1472625 := by exact prefixLift 1472625
  have htrace : WordTrace (prefixWord ++ tailWord_1472625) baseStart_1472625 baseEnd_1472625 := by
    simpa [prefixWord, tailWord_1472625, baseEnd_1472625] using wordTrace_append hprefix tailTrace_1472625
  have hstable : (prefixWord ++ tailWord_1472625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472625).length < 2 ^ (prefixWord ++ tailWord_1472625).sum := by decide
  have hdescent : baseEnd_1472625 < baseStart_1472625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472661 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 7]
def baseStart_1472661 : Nat := 118140960795 + 1472661 * 2 ^ 59
def prefixEnd_1472661 : Nat := 4983230072969 + 3 ^ 40 * 1472661 * 2
def baseEnd_1472661 : Nat := 756182934130967940764861

theorem tailTrace_1472661 : CollatzResearch.WordTrace tailWord_1472661 prefixEnd_1472661 756182934130967940764861 := by
  unfold tailWord_1472661
  simp only [CollatzResearch.WordTrace]
  refine ⟨53712359317808182320137837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35808239545205454880091891 53712359317808182320137837)
  ·
    refine ⟨20142134744178068370051689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53712359317808182320137837 20142134744178068370051689)
    ·
      refine ⟨15106601058133551277538767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20142134744178068370051689 15106601058133551277538767)
      ·
        refine ⟨22659901587200326916308151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15106601058133551277538767 22659901587200326916308151)
        ·
          refine ⟨33989852380800490374462227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22659901587200326916308151 33989852380800490374462227)
          ·
            refine ⟨50984778571200735561693341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33989852380800490374462227 50984778571200735561693341)
            ·
              refine ⟨19119291964200275835635003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50984778571200735561693341 19119291964200275835635003)
              ·
                refine ⟨28678937946300413753452505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19119291964200275835635003 28678937946300413753452505)
                ·
                  refine ⟨21509203459725310315089379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28678937946300413753452505 21509203459725310315089379)
                  ·
                    refine ⟨32263805189587965472634069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21509203459725310315089379 32263805189587965472634069)
                    ·
                      refine ⟨756182934130967940764861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32263805189587965472634069 756182934130967940764861)
                      ·
                        rfl

theorem cell23_1472661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_1472661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472661 prefixEnd_1472661 := by exact prefixLift 1472661
  have htrace : WordTrace (prefixWord ++ tailWord_1472661) baseStart_1472661 baseEnd_1472661 := by
    simpa [prefixWord, tailWord_1472661, baseEnd_1472661] using wordTrace_append hprefix tailTrace_1472661
  have hstable : (prefixWord ++ tailWord_1472661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472661).length < 2 ^ (prefixWord ++ tailWord_1472661).sum := by decide
  have hdescent : baseEnd_1472661 < baseStart_1472661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472668 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_1472668 : Nat := 118140960795 + 1472668 * 2 ^ 59
def prefixEnd_1472668 : Nat := 4983230072969 + 3 ^ 40 * 1472668 * 2
def baseEnd_1472668 : Nat := 252062176165183137792443

theorem tailTrace_1472668 : CollatzResearch.WordTrace tailWord_1472668 prefixEnd_1472668 252062176165183137792443 := by
  unfold tailWord_1472668
  simp only [CollatzResearch.WordTrace]
  refine ⟨26856307314391411257821329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35808409752521881677095105 26856307314391411257821329)
  ·
    refine ⟨20142230485793558443365997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26856307314391411257821329 20142230485793558443365997)
    ·
      refine ⟨7553336432172584416262249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20142230485793558443365997 7553336432172584416262249)
      ·
        refine ⟨5665002324129438312196687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7553336432172584416262249 5665002324129438312196687)
        ·
          refine ⟨8497503486194157468295031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665002324129438312196687 8497503486194157468295031)
          ·
            refine ⟨12746255229291236202442547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8497503486194157468295031 12746255229291236202442547)
            ·
              refine ⟨19119382843936854303663821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12746255229291236202442547 19119382843936854303663821)
              ·
                refine ⟨7169768566476320363873933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19119382843936854303663821 7169768566476320363873933)
                ·
                  refine ⟨2688663212428620136452725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7169768566476320363873933 2688663212428620136452725)
                  ·
                    refine ⟨252062176165183137792443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2688663212428620136452725 252062176165183137792443)
                    ·
                      rfl

theorem cell23_1472668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_1472668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472668 prefixEnd_1472668 := by exact prefixLift 1472668
  have htrace : WordTrace (prefixWord ++ tailWord_1472668) baseStart_1472668 baseEnd_1472668 := by
    simpa [prefixWord, tailWord_1472668, baseEnd_1472668] using wordTrace_append hprefix tailTrace_1472668
  have hstable : (prefixWord ++ tailWord_1472668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472668).length < 2 ^ (prefixWord ++ tailWord_1472668).sum := by decide
  have hdescent : baseEnd_1472668 < baseStart_1472668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472722 : List Nat := [3, 2, 2, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_1472722 : Nat := 118140960795 + 1472722 * 2 ^ 59
def prefixEnd_1472722 : Nat := 4983230072969 + 3 ^ 40 * 1472722 * 2
def baseEnd_1472722 : Nat := 756214256450892202102081

theorem tailTrace_1472722 : CollatzResearch.WordTrace tailWord_1472722 prefixEnd_1472722 756214256450892202102081 := by
  unfold tailWord_1472722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13428646042646797434527105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35809722780391459825405613 13428646042646797434527105)
  ·
    refine ⟨10071484531985098075895329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13428646042646797434527105 10071484531985098075895329)
    ·
      refine ⟨7553613398988823556921497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10071484531985098075895329 7553613398988823556921497)
      ·
        refine ⟨5665210049241617667691123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7553613398988823556921497 5665210049241617667691123)
        ·
          refine ⟨8497815073862426501536685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665210049241617667691123 8497815073862426501536685)
          ·
            refine ⟨3186680652698409938076257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8497815073862426501536685 3186680652698409938076257)
            ·
              refine ⟨2390010489523807453557193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3186680652698409938076257 2390010489523807453557193)
              ·
                refine ⟨1792507867142855590167895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390010489523807453557193 1792507867142855590167895)
                ·
                  refine ⟨2688761800714283385251843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1792507867142855590167895 2688761800714283385251843)
                  ·
                    refine ⟨4033142701071425077877765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2688761800714283385251843 4033142701071425077877765)
                    ·
                      refine ⟨756214256450892202102081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4033142701071425077877765 756214256450892202102081)
                      ·
                        rfl

theorem cell23_1472722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_1472722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472722 prefixEnd_1472722 := by exact prefixLift 1472722
  have htrace : WordTrace (prefixWord ++ tailWord_1472722) baseStart_1472722 baseEnd_1472722 := by
    simpa [prefixWord, tailWord_1472722, baseEnd_1472722] using wordTrace_append hprefix tailTrace_1472722
  have hstable : (prefixWord ++ tailWord_1472722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472722).length < 2 ^ (prefixWord ++ tailWord_1472722).sum := by decide
  have hdescent : baseEnd_1472722 < baseStart_1472722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472728 : List Nat := [2, 1, 2, 2, 4, 2, 1, 9]
def baseStart_1472728 : Nat := 118140960795 + 1472728 * 2 ^ 59
def prefixEnd_1472728 : Nat := 4983230072969 + 3 ^ 40 * 1472728 * 2
def baseEnd_1472728 : Nat := 28008049530919228838039

theorem tailTrace_1472728 : CollatzResearch.WordTrace tailWord_1472728 prefixEnd_1472728 28008049530919228838039 := by
  unfold tailWord_1472728
  simp only [CollatzResearch.WordTrace]
  refine ⟨26857401504282726381413419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35809868672376968508551225 26857401504282726381413419)
  ·
    refine ⟨40286102256424089572120129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26857401504282726381413419 40286102256424089572120129)
    ·
      refine ⟨30214576692318067179090097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40286102256424089572120129 30214576692318067179090097)
      ·
        refine ⟨22660932519238550384317573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30214576692318067179090097 22660932519238550384317573)
        ·
          refine ⟨4248924847357228197059545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22660932519238550384317573 4248924847357228197059545)
          ·
            refine ⟨3186693635517921147794659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4248924847357228197059545 3186693635517921147794659)
            ·
              refine ⟨4780040453276881721691989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3186693635517921147794659 4780040453276881721691989)
              ·
                refine ⟨28008049530919228838039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4780040453276881721691989 28008049530919228838039)
                ·
                  rfl

theorem cell23_1472728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 9].length) (baseStart_1472728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472728 prefixEnd_1472728 := by exact prefixLift 1472728
  have htrace : WordTrace (prefixWord ++ tailWord_1472728) baseStart_1472728 baseEnd_1472728 := by
    simpa [prefixWord, tailWord_1472728, baseEnd_1472728] using wordTrace_append hprefix tailTrace_1472728
  have hstable : (prefixWord ++ tailWord_1472728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472728).length < 2 ^ (prefixWord ++ tailWord_1472728).sum := by decide
  have hdescent : baseEnd_1472728 < baseStart_1472728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472755 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 3]
def baseStart_1472755 : Nat := 118140960795 + 1472755 * 2 ^ 59
def prefixEnd_1472755 : Nat := 4983230072969 + 3 ^ 40 * 1472755 * 2
def baseEnd_1472755 : Nat := 756231201312490572989429

theorem tailTrace_1472755 : CollatzResearch.WordTrace tailWord_1472755 prefixEnd_1472755 756231201312490572989429 := by
  unfold tailWord_1472755
  simp only [CollatzResearch.WordTrace]
  refine ⟨53715787779467636374059719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35810525186311757582706479 53715787779467636374059719)
  ·
    refine ⟨80573681669201454561089579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53715787779467636374059719 80573681669201454561089579)
    ·
      refine ⟨120860522503802181841634369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80573681669201454561089579 120860522503802181841634369)
      ·
        refine ⟨90645391877851636381225777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120860522503802181841634369 90645391877851636381225777)
        ·
          refine ⟨67984043908388727285919333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90645391877851636381225777 67984043908388727285919333)
          ·
            refine ⟨12747008232822886366109875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67984043908388727285919333 12747008232822886366109875)
            ·
              refine ⟨19120512349234329549164813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12747008232822886366109875 19120512349234329549164813)
              ·
                refine ⟨7170192130962873580936805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19120512349234329549164813 7170192130962873580936805)
                ·
                  refine ⟨1344411024555538796425651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7170192130962873580936805 1344411024555538796425651)
                  ·
                    refine ⟨2016616536833308194638477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344411024555538796425651 2016616536833308194638477)
                    ·
                      refine ⟨756231201312490572989429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2016616536833308194638477 756231201312490572989429)
                      ·
                        rfl

theorem cell23_1472755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 1, 3].length) (baseStart_1472755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472755 prefixEnd_1472755 := by exact prefixLift 1472755
  have htrace : WordTrace (prefixWord ++ tailWord_1472755) baseStart_1472755 baseEnd_1472755 := by
    simpa [prefixWord, tailWord_1472755, baseEnd_1472755] using wordTrace_append hprefix tailTrace_1472755
  have hstable : (prefixWord ++ tailWord_1472755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472755).length < 2 ^ (prefixWord ++ tailWord_1472755).sum := by decide
  have hdescent : baseEnd_1472755 < baseStart_1472755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472782 : List Nat := [4, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_1472782 : Nat := 118140960795 + 1472782 * 2 ^ 59
def prefixEnd_1472782 : Nat := 4983230072969 + 3 ^ 40 * 1472782 * 2
def baseEnd_1472782 : Nat := 756245065290161967351805

theorem tailTrace_1472782 : CollatzResearch.WordTrace tailWord_1472782 prefixEnd_1472782 756245065290161967351805 := by
  unfold tailWord_1472782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6714596568796227498161575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35811181700246546656861733 6714596568796227498161575)
  ·
    refine ⟨10071894853194341247242363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6714596568796227498161575 10071894853194341247242363)
    ·
      refine ⟨15107842279791511870863545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10071894853194341247242363 15107842279791511870863545)
      ·
        refine ⟨11330881709843633903147659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15107842279791511870863545 11330881709843633903147659)
        ·
          refine ⟨16996322564765450854721489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11330881709843633903147659 16996322564765450854721489)
          ·
            refine ⟨12747241923574088141041117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16996322564765450854721489 12747241923574088141041117)
            ·
              refine ⟨4780215721340283052890419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12747241923574088141041117 4780215721340283052890419)
              ·
                refine ⟨7170323582010424579335629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4780215721340283052890419 7170323582010424579335629)
                ·
                  refine ⟨2688871343253909217250861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7170323582010424579335629 2688871343253909217250861)
                  ·
                    refine ⟨1008326753720215956469073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2688871343253909217250861 1008326753720215956469073)
                    ·
                      refine ⟨756245065290161967351805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008326753720215956469073 756245065290161967351805)
                      ·
                        rfl

theorem cell23_1472782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_1472782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472782 prefixEnd_1472782 := by exact prefixLift 1472782
  have htrace : WordTrace (prefixWord ++ tailWord_1472782) baseStart_1472782 baseEnd_1472782 := by
    simpa [prefixWord, tailWord_1472782, baseEnd_1472782] using wordTrace_append hprefix tailTrace_1472782
  have hstable : (prefixWord ++ tailWord_1472782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472782).length < 2 ^ (prefixWord ++ tailWord_1472782).sum := by decide
  have hdescent : baseEnd_1472782 < baseStart_1472782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472795 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 3, 4, 2]
def baseStart_1472795 : Nat := 118140960795 + 1472795 * 2 ^ 59
def prefixEnd_1472795 : Nat := 4983230072969 + 3 ^ 40 * 1472795 * 2
def baseEnd_1472795 : Nat := 756251740538670416489245

theorem tailTrace_1472795 : CollatzResearch.WordTrace tailWord_1472795 prefixEnd_1472795 756251740538670416489245 := by
  unfold tailWord_1472795
  simp only [CollatzResearch.WordTrace]
  refine ⟨53717246699322723205515839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35811497799548482137010559 53717246699322723205515839)
  ·
    refine ⟨80575870048984084808273759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53717246699322723205515839 80575870048984084808273759)
    ·
      refine ⟨120863805073476127212410639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80575870048984084808273759 120863805073476127212410639)
      ·
        refine ⟨181295707610214190818615959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120863805073476127212410639 181295707610214190818615959)
        ·
          refine ⟨271943561415321286227923939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181295707610214190818615959 271943561415321286227923939)
          ·
            refine ⟨407915342122981929341885909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271943561415321286227923939 407915342122981929341885909)
            ·
              refine ⟨9560515831007388968950451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 407915342122981929341885909 9560515831007388968950451)
              ·
                refine ⟨14340773746511083453425677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9560515831007388968950451 14340773746511083453425677)
                ·
                  refine ⟨5377790154941656295034629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14340773746511083453425677 5377790154941656295034629)
                  ·
                    refine ⟨1008335654051560555318993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5377790154941656295034629 1008335654051560555318993)
                    ·
                      refine ⟨756251740538670416489245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008335654051560555318993 756251740538670416489245)
                      ·
                        rfl

theorem cell23_1472795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 3, 4, 2].length) (baseStart_1472795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472795 prefixEnd_1472795 := by exact prefixLift 1472795
  have htrace : WordTrace (prefixWord ++ tailWord_1472795) baseStart_1472795 baseEnd_1472795 := by
    simpa [prefixWord, tailWord_1472795, baseEnd_1472795] using wordTrace_append hprefix tailTrace_1472795
  have hstable : (prefixWord ++ tailWord_1472795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472795).length < 2 ^ (prefixWord ++ tailWord_1472795).sum := by decide
  have hdescent : baseEnd_1472795 < baseStart_1472795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472812 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 4, 2, 2]
def baseStart_1472812 : Nat := 118140960795 + 1472812 * 2 ^ 59
def prefixEnd_1472812 : Nat := 4983230072969 + 3 ^ 40 * 1472812 * 2
def baseEnd_1472812 : Nat := 756260469709796849976667

theorem tailTrace_1472812 : CollatzResearch.WordTrace tailWord_1472812 prefixEnd_1472812 756260469709796849976667 := by
  unfold tailWord_1472812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26858933370130567554442345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35811911160174090072589793 26858933370130567554442345)
  ·
    refine ⟨20144200027597925665831759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26858933370130567554442345 20144200027597925665831759)
    ·
      refine ⟨30216300041396888498747639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20144200027597925665831759 30216300041396888498747639)
      ·
        refine ⟨45324450062095332748121459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30216300041396888498747639 45324450062095332748121459)
        ·
          refine ⟨67986675093142999122182189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45324450062095332748121459 67986675093142999122182189)
          ·
            refine ⟨25495003159928624670818321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67986675093142999122182189 25495003159928624670818321)
            ·
              refine ⟨19121252369946468503113741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25495003159928624670818321 19121252369946468503113741)
              ·
                refine ⟨7170469638729925688667653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19121252369946468503113741 7170469638729925688667653)
                ·
                  refine ⟨1344463057261861066625185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7170469638729925688667653 1344463057261861066625185)
                  ·
                    refine ⟨1008347292946395799968889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344463057261861066625185 1008347292946395799968889)
                    ·
                      refine ⟨756260469709796849976667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008347292946395799968889 756260469709796849976667)
                      ·
                        rfl

theorem cell23_1472812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 2, 2].length) (baseStart_1472812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472812 prefixEnd_1472812 := by exact prefixLift 1472812
  have htrace : WordTrace (prefixWord ++ tailWord_1472812) baseStart_1472812 baseEnd_1472812 := by
    simpa [prefixWord, tailWord_1472812, baseEnd_1472812] using wordTrace_append hprefix tailTrace_1472812
  have hstable : (prefixWord ++ tailWord_1472812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472812).length < 2 ^ (prefixWord ++ tailWord_1472812).sum := by decide
  have hdescent : baseEnd_1472812 < baseStart_1472812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472825 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_1472825 : Nat := 118140960795 + 1472825 * 2 ^ 59
def prefixEnd_1472825 : Nat := 4983230072969 + 3 ^ 40 * 1472825 * 2
def baseEnd_1472825 : Nat := 756267144958305299114107

theorem tailTrace_1472825 : CollatzResearch.WordTrace tailWord_1472825 prefixEnd_1472825 756267144958305299114107 := by
  unfold tailWord_1472825
  simp only [CollatzResearch.WordTrace]
  refine ⟨53718340889214038329107929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35812227259476025552738619 53718340889214038329107929)
  ·
    refine ⟨40288755666910528746830947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53718340889214038329107929 40288755666910528746830947)
    ·
      refine ⟨60433133500365793120246421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40288755666910528746830947 60433133500365793120246421)
      ·
        refine ⟨2832803132829646552511551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60433133500365793120246421 2832803132829646552511551)
        ·
          refine ⟨4249204699244469828767327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2832803132829646552511551 4249204699244469828767327)
          ·
            refine ⟨6373807048866704743150991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249204699244469828767327 6373807048866704743150991)
            ·
              refine ⟨9560710573300057114726487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373807048866704743150991 9560710573300057114726487)
              ·
                refine ⟨14341065859950085672089731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9560710573300057114726487 14341065859950085672089731)
                ·
                  refine ⟨21511598789925128508134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14341065859950085672089731 21511598789925128508134597)
                  ·
                    refine ⟨4033424773110961595275237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21511598789925128508134597 4033424773110961595275237)
                    ·
                      refine ⟨756267144958305299114107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4033424773110961595275237 756267144958305299114107)
                      ·
                        rfl

theorem cell23_1472825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_1472825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472825 prefixEnd_1472825 := by exact prefixLift 1472825
  have htrace : WordTrace (prefixWord ++ tailWord_1472825) baseStart_1472825 baseEnd_1472825 := by
    simpa [prefixWord, tailWord_1472825, baseEnd_1472825] using wordTrace_append hprefix tailTrace_1472825
  have hstable : (prefixWord ++ tailWord_1472825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472825).length < 2 ^ (prefixWord ++ tailWord_1472825).sum := by decide
  have hdescent : baseEnd_1472825 < baseStart_1472825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472852 : List Nat := [2, 4, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1472852 : Nat := 118140960795 + 1472852 * 2 ^ 59
def prefixEnd_1472852 : Nat := 4983230072969 + 3 ^ 40 * 1472852 * 2
def baseEnd_1472852 : Nat := 84031223215108521497387

theorem tailTrace_1472852 : CollatzResearch.WordTrace tailWord_1472852 prefixEnd_1472852 84031223215108521497387 := by
  unfold tailWord_1472852
  simp only [CollatzResearch.WordTrace]
  refine ⟨26859662830058110970170405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35812883773410814626893873 26859662830058110970170405)
  ·
    refine ⟨5036186780635895806906951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26859662830058110970170405 5036186780635895806906951)
    ·
      refine ⟨7554280170953843710360427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5036186780635895806906951 7554280170953843710360427)
      ·
        refine ⟨11331420256430765565540641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7554280170953843710360427 11331420256430765565540641)
        ·
          refine ⟨8498565192323074174155481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11331420256430765565540641 8498565192323074174155481)
          ·
            refine ⟨6373923894242305630616611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8498565192323074174155481 6373923894242305630616611)
            ·
              refine ⟨9560885841363458445924917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6373923894242305630616611 9560885841363458445924917)
              ·
                refine ⟨896333047627824229305461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9560885841363458445924917 896333047627824229305461)
                ·
                  refine ⟨84031223215108521497387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896333047627824229305461 84031223215108521497387)
                  ·
                    rfl

theorem cell23_1472852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1472852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472852 prefixEnd_1472852 := by exact prefixLift 1472852
  have htrace : WordTrace (prefixWord ++ tailWord_1472852) baseStart_1472852 baseEnd_1472852 := by
    simpa [prefixWord, tailWord_1472852, baseEnd_1472852] using wordTrace_append hprefix tailTrace_1472852
  have hstable : (prefixWord ++ tailWord_1472852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472852).length < 2 ^ (prefixWord ++ tailWord_1472852).sum := by decide
  have hdescent : baseEnd_1472852 < baseStart_1472852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472922 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_1472922 : Nat := 118140960795 + 1472922 * 2 ^ 59
def prefixEnd_1472922 : Nat := 4983230072969 + 3 ^ 40 * 1472922 * 2
def baseEnd_1472922 : Nat := 756316952581791419601161

theorem tailTrace_1472922 : CollatzResearch.WordTrace tailWord_1472922 prefixEnd_1472922 756316952581791419601161 := by
  unfold tailWord_1472922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13430469692465655973847255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35814585846575082596926013 13430469692465655973847255)
  ·
    refine ⟨20145704538698483960770883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13430469692465655973847255 20145704538698483960770883)
    ·
      refine ⟨30218556808047725941156325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20145704538698483960770883 30218556808047725941156325)
      ·
        refine ⟨5665979401508948613966811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30218556808047725941156325 5665979401508948613966811)
        ·
          refine ⟨8498969102263422920950217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5665979401508948613966811 8498969102263422920950217)
          ·
            refine ⟨6374226826697567190712663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8498969102263422920950217 6374226826697567190712663)
            ·
              refine ⟨9561340240046350786068995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374226826697567190712663 9561340240046350786068995)
              ·
                refine ⟨14342010360069526179103493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9561340240046350786068995 14342010360069526179103493)
                ·
                  refine ⟨2689126942513036158581905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14342010360069526179103493 2689126942513036158581905)
                  ·
                    refine ⟨2016845206884777118936429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2689126942513036158581905 2016845206884777118936429)
                    ·
                      refine ⟨756316952581791419601161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2016845206884777118936429 756316952581791419601161)
                      ·
                        rfl

theorem cell23_1472922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_1472922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472922 prefixEnd_1472922 := by exact prefixLift 1472922
  have htrace : WordTrace (prefixWord ++ tailWord_1472922) baseStart_1472922 baseEnd_1472922 := by
    simpa [prefixWord, tailWord_1472922, baseEnd_1472922] using wordTrace_append hprefix tailTrace_1472922
  have hstable : (prefixWord ++ tailWord_1472922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472922).length < 2 ^ (prefixWord ++ tailWord_1472922).sum := by decide
  have hdescent : baseEnd_1472922 < baseStart_1472922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472952 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_1472952 : Nat := 118140960795 + 1472952 * 2 ^ 59
def prefixEnd_1472952 : Nat := 4983230072969 + 3 ^ 40 * 1472952 * 2
def baseEnd_1472952 : Nat := 756332357001426302226023

theorem tailTrace_1472952 : CollatzResearch.WordTrace tailWord_1472952 prefixEnd_1472952 756332357001426302226023 := by
  unfold tailWord_1472952
  simp only [CollatzResearch.WordTrace]
  refine ⟨26861486479876969509490555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35815315306502626012654073 26861486479876969509490555)
  ·
    refine ⟨40292229719815454264235833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26861486479876969509490555 40292229719815454264235833)
    ·
      refine ⟨30219172289861590698176875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40292229719815454264235833 30219172289861590698176875)
      ·
        refine ⟨45328758434792386047265313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30219172289861590698176875 45328758434792386047265313)
        ·
          refine ⟨33996568826094289535448985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45328758434792386047265313 33996568826094289535448985)
          ·
            refine ⟨25497426619570717151586739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33996568826094289535448985 25497426619570717151586739)
            ·
              refine ⟨38246139929356075727380109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25497426619570717151586739 38246139929356075727380109)
              ·
                refine ⟨14342302473508528397767541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38246139929356075727380109 14342302473508528397767541)
                ·
                  refine ⟨1344590856891424537290707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14342302473508528397767541 1344590856891424537290707)
                  ·
                    refine ⟨2016886285337136805936061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344590856891424537290707 2016886285337136805936061)
                    ·
                      refine ⟨756332357001426302226023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2016886285337136805936061 756332357001426302226023)
                      ·
                        rfl

theorem cell23_1472952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_1472952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472952 prefixEnd_1472952 := by exact prefixLift 1472952
  have htrace : WordTrace (prefixWord ++ tailWord_1472952) baseStart_1472952 baseEnd_1472952 := by
    simpa [prefixWord, tailWord_1472952, baseEnd_1472952] using wordTrace_append hprefix tailTrace_1472952
  have hstable : (prefixWord ++ tailWord_1472952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472952).length < 2 ^ (prefixWord ++ tailWord_1472952).sum := by decide
  have hdescent : baseEnd_1472952 < baseStart_1472952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472985 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 3, 6]
def baseStart_1472985 : Nat := 118140960795 + 1472985 * 2 ^ 59
def prefixEnd_1472985 : Nat := 4983230072969 + 3 ^ 40 * 1472985 * 2
def baseEnd_1472985 : Nat := 252116433954341557704457

theorem tailTrace_1472985 : CollatzResearch.WordTrace tailWord_1472985 prefixEnd_1472985 252116433954341557704457 := by
  unfold tailWord_1472985
  simp only [CollatzResearch.WordTrace]
  refine ⟨53724176568634385654932409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35816117712422923769954939 53724176568634385654932409)
  ·
    refine ⟨40293132426475789241199307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53724176568634385654932409 40293132426475789241199307)
    ·
      refine ⟨60439698639713683861798961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40293132426475789241199307 60439698639713683861798961)
      ·
        refine ⟨45329773979785262896349221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60439698639713683861798961 45329773979785262896349221)
        ·
          refine ⟨8499332621209736793065479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45329773979785262896349221 8499332621209736793065479)
          ·
            refine ⟨12748998931814605189598219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499332621209736793065479 12748998931814605189598219)
            ·
              refine ⟨19123498397721907784397329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12748998931814605189598219 19123498397721907784397329)
              ·
                refine ⟨14342623798291430838297997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19123498397721907784397329 14342623798291430838297997)
                ·
                  refine ⟨5378483924359286564361749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14342623798291430838297997 5378483924359286564361749)
                  ·
                    refine ⟨252116433954341557704457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5378483924359286564361749 252116433954341557704457)
                    ·
                      rfl

theorem cell23_1472985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_1472985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472985 prefixEnd_1472985 := by exact prefixLift 1472985
  have htrace : WordTrace (prefixWord ++ tailWord_1472985) baseStart_1472985 baseEnd_1472985 := by
    simpa [prefixWord, tailWord_1472985, baseEnd_1472985] using wordTrace_append hprefix tailTrace_1472985
  have hstable : (prefixWord ++ tailWord_1472985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472985).length < 2 ^ (prefixWord ++ tailWord_1472985).sum := by decide
  have hdescent : baseEnd_1472985 < baseStart_1472985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1472986 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3]
def baseStart_1472986 : Nat := 118140960795 + 1472986 * 2 ^ 59
def prefixEnd_1472986 : Nat := 4983230072969 + 3 ^ 40 * 1472986 * 2
def baseEnd_1472986 : Nat := 756349815343679169200867

theorem tailTrace_1472986 : CollatzResearch.WordTrace tailWord_1472986 prefixEnd_1472986 756349815343679169200867 := by
  unfold tailWord_1472986
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431053260407690706429703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35816142027753841883812541 13431053260407690706429703)
  ·
    refine ⟨20146579890611536059644555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13431053260407690706429703 20146579890611536059644555)
    ·
      refine ⟨30219869835917304089466833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20146579890611536059644555 30219869835917304089466833)
      ·
        refine ⟨22664902376937978067100125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30219869835917304089466833 22664902376937978067100125)
        ·
          refine ⟨8499338391351741775162547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22664902376937978067100125 8499338391351741775162547)
          ·
            refine ⟨12749007587027612662743821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8499338391351741775162547 12749007587027612662743821)
            ·
              refine ⟨4780877845135354748528933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12749007587027612662743821 4780877845135354748528933)
              ·
                refine ⟨896414595962879015349175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4780877845135354748528933 896414595962879015349175)
                ·
                  refine ⟨1344621893944318523023763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896414595962879015349175 1344621893944318523023763)
                  ·
                    refine ⟨2016932840916477784535645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344621893944318523023763 2016932840916477784535645)
                    ·
                      refine ⟨756349815343679169200867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2016932840916477784535645 756349815343679169200867)
                      ·
                        rfl

theorem cell23_1472986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_1472986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1472986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1472986 prefixEnd_1472986 := by exact prefixLift 1472986
  have htrace : WordTrace (prefixWord ++ tailWord_1472986) baseStart_1472986 baseEnd_1472986 := by
    simpa [prefixWord, tailWord_1472986, baseEnd_1472986] using wordTrace_append hprefix tailTrace_1472986
  have hstable : (prefixWord ++ tailWord_1472986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1472986).length < 2 ^ (prefixWord ++ tailWord_1472986).sum := by decide
  have hdescent : baseEnd_1472986 < baseStart_1472986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1472986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473002 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1473002 : Nat := 118140960795 + 1473002 * 2 ^ 59
def prefixEnd_1473002 : Nat := 4983230072969 + 3 ^ 40 * 1473002 * 2
def baseEnd_1473002 : Nat := 252119343678050368866931

theorem tailTrace_1473002 : CollatzResearch.WordTrace tailWord_1473002 prefixEnd_1473002 252119343678050368866931 := by
  unfold tailWord_1473002
  simp only [CollatzResearch.WordTrace]
  refine ⟨13431199152393199389575315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35816531073048531705534173 13431199152393199389575315)
  ·
    refine ⟨20146798728589799084362973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13431199152393199389575315 20146798728589799084362973)
    ·
      refine ⟨7555049523221174656636115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20146798728589799084362973 7555049523221174656636115)
      ·
        refine ⟨11332574284831761984954173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7555049523221174656636115 11332574284831761984954173)
        ·
          refine ⟨4249715356811910744357815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11332574284831761984954173 4249715356811910744357815)
          ·
            refine ⟨6374573035217866116536723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249715356811910744357815 6374573035217866116536723)
            ·
              refine ⟨9561859552826799174805085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6374573035217866116536723 9561859552826799174805085)
              ·
                refine ⟨3585697332310049690551907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9561859552826799174805085 3585697332310049690551907)
                ·
                  refine ⟨5378545998465074535827861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585697332310049690551907 5378545998465074535827861)
                  ·
                    refine ⟨252119343678050368866931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5378545998465074535827861 252119343678050368866931)
                    ·
                      rfl

theorem cell23_1473002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1473002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473002 prefixEnd_1473002 := by exact prefixLift 1473002
  have htrace : WordTrace (prefixWord ++ tailWord_1473002) baseStart_1473002 baseEnd_1473002 := by
    simpa [prefixWord, tailWord_1473002, baseEnd_1473002] using wordTrace_append hprefix tailTrace_1473002
  have hstable : (prefixWord ++ tailWord_1473002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473002).length < 2 ^ (prefixWord ++ tailWord_1473002).sum := by decide
  have hdescent : baseEnd_1473002 < baseStart_1473002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473036 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_1473036 : Nat := 118140960795 + 1473036 * 2 ^ 59
def prefixEnd_1473036 : Nat := 4983230072969 + 3 ^ 40 * 1473036 * 2
def baseEnd_1473036 : Nat := 252125163125467991191879

theorem tailTrace_1473036 : CollatzResearch.WordTrace tailWord_1473036 prefixEnd_1473036 252125163125467991191879 := by
  unfold tailWord_1473036
  simp only [CollatzResearch.WordTrace]
  refine ⟨26863018345724810682519481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35817357794299747576692641 26863018345724810682519481)
  ·
    refine ⟨20147263759293608011889611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26863018345724810682519481 20147263759293608011889611)
    ·
      refine ⟨30220895638940412017834417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20147263759293608011889611 30220895638940412017834417)
      ·
        refine ⟨22665671729205309013375813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30220895638940412017834417 22665671729205309013375813)
        ·
          refine ⟨4249813449225995440007965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22665671729205309013375813 4249813449225995440007965)
          ·
            refine ⟨1593680043459748290002987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4249813449225995440007965 1593680043459748290002987)
            ·
              refine ⟨2390520065189622435004481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593680043459748290002987 2390520065189622435004481)
              ·
                refine ⟨1792890048892216826253361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2390520065189622435004481 1792890048892216826253361)
                ·
                  refine ⟨1344667536669162619690021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1792890048892216826253361 1344667536669162619690021)
                  ·
                    refine ⟨252125163125467991191879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344667536669162619690021 252125163125467991191879)
                    ·
                      rfl

theorem cell23_1473036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_1473036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473036 prefixEnd_1473036 := by exact prefixLift 1473036
  have htrace : WordTrace (prefixWord ++ tailWord_1473036) baseStart_1473036 baseEnd_1473036 := by
    simpa [prefixWord, tailWord_1473036, baseEnd_1473036] using wordTrace_append hprefix tailTrace_1473036
  have hstable : (prefixWord ++ tailWord_1473036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473036).length < 2 ^ (prefixWord ++ tailWord_1473036).sum := by decide
  have hdescent : baseEnd_1473036 < baseStart_1473036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473056 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4]
def baseStart_1473056 : Nat := 118140960795 + 1473056 * 2 ^ 59
def prefixEnd_1473056 : Nat := 4983230072969 + 3 ^ 40 * 1473056 * 2
def baseEnd_1473056 : Nat := 756385758989493895325545

theorem tailTrace_1473056 : CollatzResearch.WordTrace tailWord_1473056 prefixEnd_1473056 756385758989493895325545 := by
  unfold tailWord_1473056
  simp only [CollatzResearch.WordTrace]
  refine ⟨26863383075688582390383511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35817844100918109853844681 26863383075688582390383511)
  ·
    refine ⟨40295074613532873585575267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26863383075688582390383511 40295074613532873585575267)
    ·
      refine ⟨60442611920299310378362901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40295074613532873585575267 60442611920299310378362901)
      ·
        refine ⟨2833247433764030173985761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60442611920299310378362901 2833247433764030173985761)
        ·
          refine ⟨2124935575323022630489321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2833247433764030173985761 2124935575323022630489321)
          ·
            refine ⟨1593701681492266972866991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2124935575323022630489321 1593701681492266972866991)
            ·
              refine ⟨2390552522238400459300487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1593701681492266972866991 2390552522238400459300487)
              ·
                refine ⟨3585828783357600688950731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390552522238400459300487 3585828783357600688950731)
                ·
                  refine ⟨5378743175036401033426097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585828783357600688950731 5378743175036401033426097)
                  ·
                    refine ⟨4034057381277300775069573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5378743175036401033426097 4034057381277300775069573)
                    ·
                      refine ⟨756385758989493895325545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4034057381277300775069573 756385758989493895325545)
                      ·
                        rfl

theorem cell23_1473056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_1473056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473056 prefixEnd_1473056 := by exact prefixLift 1473056
  have htrace : WordTrace (prefixWord ++ tailWord_1473056) baseStart_1473056 baseEnd_1473056 := by
    simpa [prefixWord, tailWord_1473056, baseEnd_1473056] using wordTrace_append hprefix tailTrace_1473056
  have hstable : (prefixWord ++ tailWord_1473056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473056).length < 2 ^ (prefixWord ++ tailWord_1473056).sum := by decide
  have hdescent : baseEnd_1473056 < baseStart_1473056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473059 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1473059 : Nat := 118140960795 + 1473059 * 2 ^ 59
def prefixEnd_1473059 : Nat := 4983230072969 + 3 ^ 40 * 1473059 * 2
def baseEnd_1473059 : Nat := 756387299431457383588031

theorem tailTrace_1473059 : CollatzResearch.WordTrace tailWord_1473059 prefixEnd_1473059 756387299431457383588031 := by
  unfold tailWord_1473059
  simp only [CollatzResearch.WordTrace]
  refine ⟨53726875570366296293126231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35817917046910864195417487 53726875570366296293126231)
  ·
    refine ⟨80590313355549444439689347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53726875570366296293126231 80590313355549444439689347)
    ·
      refine ⟨120885470033324166659534021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80590313355549444439689347 120885470033324166659534021)
      ·
        refine ⟨22666025631248281248662629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120885470033324166659534021 22666025631248281248662629)
        ·
          refine ⟨4249879805859052734124243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22666025631248281248662629 4249879805859052734124243)
          ·
            refine ⟨6374819708788579101186365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4249879805859052734124243 6374819708788579101186365)
            ·
              refine ⟨2390557390795717162944887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6374819708788579101186365 2390557390795717162944887)
              ·
                refine ⟨3585836086193575744417331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390557390795717162944887 3585836086193575744417331)
                ·
                  refine ⟨5378754129290363616625997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3585836086193575744417331 5378754129290363616625997)
                  ·
                    refine ⟨2017032798483886356234749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5378754129290363616625997 2017032798483886356234749)
                    ·
                      refine ⟨756387299431457383588031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017032798483886356234749 756387299431457383588031)
                      ·
                        rfl

theorem cell23_1473059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1473059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473059 prefixEnd_1473059 := by exact prefixLift 1473059
  have htrace : WordTrace (prefixWord ++ tailWord_1473059) baseStart_1473059 baseEnd_1473059 := by
    simpa [prefixWord, tailWord_1473059, baseEnd_1473059] using wordTrace_append hprefix tailTrace_1473059
  have hstable : (prefixWord ++ tailWord_1473059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473059).length < 2 ^ (prefixWord ++ tailWord_1473059).sum := by decide
  have hdescent : baseEnd_1473059 < baseStart_1473059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473094 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_1473094 : Nat := 118140960795 + 1473094 * 2 ^ 59
def prefixEnd_1473094 : Nat := 4983230072969 + 3 ^ 40 * 1473094 * 2
def baseEnd_1473094 : Nat := 756405271254364746650371

theorem tailTrace_1473094 : CollatzResearch.WordTrace tailWord_1473094 prefixEnd_1473094 756405271254364746650371 := by
  unfold tailWord_1473094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679004753913734289707823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35818768083492998180433557 1679004753913734289707823)
  ·
    refine ⟨2518507130870601434561735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679004753913734289707823 2518507130870601434561735)
    ·
      refine ⟨3777760696305902151842603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2518507130870601434561735 3777760696305902151842603)
      ·
        refine ⟨5666641044458853227763905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3777760696305902151842603 5666641044458853227763905)
        ·
          refine ⟨4249980783344139920822929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5666641044458853227763905 4249980783344139920822929)
          ·
            refine ⟨3187485587508104940617197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4249980783344139920822929 3187485587508104940617197)
            ·
              refine ⟨1195307095315539352731449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3187485587508104940617197 1195307095315539352731449)
              ·
                refine ⟨896480321486654514548587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195307095315539352731449 896480321486654514548587)
                ·
                  refine ⟨1344720482229981771822881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896480321486654514548587 1344720482229981771822881)
                  ·
                    refine ⟨1008540361672486328867161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344720482229981771822881 1008540361672486328867161)
                    ·
                      refine ⟨756405271254364746650371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008540361672486328867161 756405271254364746650371)
                      ·
                        rfl

theorem cell23_1473094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_1473094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473094 prefixEnd_1473094 := by exact prefixLift 1473094
  have htrace : WordTrace (prefixWord ++ tailWord_1473094) baseStart_1473094 baseEnd_1473094 := by
    simpa [prefixWord, tailWord_1473094, baseEnd_1473094] using wordTrace_append hprefix tailTrace_1473094
  have hstable : (prefixWord ++ tailWord_1473094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473094).length < 2 ^ (prefixWord ++ tailWord_1473094).sum := by decide
  have hdescent : baseEnd_1473094 < baseStart_1473094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473112 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1473112 : Nat := 118140960795 + 1473112 * 2 ^ 59
def prefixEnd_1473112 : Nat := 4983230072969 + 3 ^ 40 * 1473112 * 2
def baseEnd_1473112 : Nat := 756414513906145676225287

theorem tailTrace_1473112 : CollatzResearch.WordTrace tailWord_1473112 prefixEnd_1473112 756414513906145676225287 := by
  unfold tailWord_1473112
  simp only [CollatzResearch.WordTrace]
  refine ⟨26864404319587143172402795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35819205759449524229870393 26864404319587143172402795)
  ·
    refine ⟨40296606479380714758604193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26864404319587143172402795 40296606479380714758604193)
    ·
      refine ⟨30222454859535536068953145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40296606479380714758604193 30222454859535536068953145)
      ·
        refine ⟨22666841144651652051714859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30222454859535536068953145 22666841144651652051714859)
        ·
          refine ⟨34000261716977478077572289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22666841144651652051714859 34000261716977478077572289)
          ·
            refine ⟨25500196287733108558179217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34000261716977478077572289 25500196287733108558179217)
            ·
              refine ⟨19125147215799831418634413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25500196287733108558179217 19125147215799831418634413)
              ·
                refine ⟨7171930205924936781987905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19125147215799831418634413 7171930205924936781987905)
                ·
                  refine ⟨5378947654443702586490929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7171930205924936781987905 5378947654443702586490929)
                  ·
                    refine ⟨4034210740832776939868197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5378947654443702586490929 4034210740832776939868197)
                    ·
                      refine ⟨756414513906145676225287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4034210740832776939868197 756414513906145676225287)
                      ·
                        rfl

theorem cell23_1473112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1473112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473112 prefixEnd_1473112 := by exact prefixLift 1473112
  have htrace : WordTrace (prefixWord ++ tailWord_1473112) baseStart_1473112 baseEnd_1473112 := by
    simpa [prefixWord, tailWord_1473112, baseEnd_1473112] using wordTrace_append hprefix tailTrace_1473112
  have hstable : (prefixWord ++ tailWord_1473112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473112).length < 2 ^ (prefixWord ++ tailWord_1473112).sum := by decide
  have hdescent : baseEnd_1473112 < baseStart_1473112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473156 : List Nat := [2, 3, 2, 1, 3, 2, 1, 4, 5]
def baseStart_1473156 : Nat := 118140960795 + 1473156 * 2 ^ 59
def prefixEnd_1473156 : Nat := 4983230072969 + 3 ^ 40 * 1473156 * 2
def baseEnd_1473156 : Nat := 84048567450549278230565

theorem tailTrace_1473156 : CollatzResearch.WordTrace tailWord_1473156 prefixEnd_1473156 84048567450549278230565 := by
  unfold tailWord_1473156
  simp only [CollatzResearch.WordTrace]
  refine ⟨26865206725507440929703661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35820275634009921239604881 26865206725507440929703661)
  ·
    refine ⟨10074452522065290348638873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26865206725507440929703661 10074452522065290348638873)
    ·
      refine ⟨7555839391548967761479155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10074452522065290348638873 7555839391548967761479155)
      ·
        refine ⟨11333759087323451642218733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7555839391548967761479155 11333759087323451642218733)
        ·
          refine ⟨4250159657746294365832025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11333759087323451642218733 4250159657746294365832025)
          ·
            refine ⟨3187619743309720774374019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4250159657746294365832025 3187619743309720774374019)
            ·
              refine ⟨4781429614964581161561029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3187619743309720774374019 4781429614964581161561029)
              ·
                refine ⟨896518052805858967792693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4781429614964581161561029 896518052805858967792693)
                ·
                  refine ⟨84048567450549278230565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896518052805858967792693 84048567450549278230565)
                  ·
                    rfl

theorem cell23_1473156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 4, 5].length) (baseStart_1473156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473156 prefixEnd_1473156 := by exact prefixLift 1473156
  have htrace : WordTrace (prefixWord ++ tailWord_1473156) baseStart_1473156 baseEnd_1473156 := by
    simpa [prefixWord, tailWord_1473156, baseEnd_1473156] using wordTrace_append hprefix tailTrace_1473156
  have hstable : (prefixWord ++ tailWord_1473156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473156).length < 2 ^ (prefixWord ++ tailWord_1473156).sum := by decide
  have hdescent : baseEnd_1473156 < baseStart_1473156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473159 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_1473159 : Nat := 118140960795 + 1473159 * 2 ^ 59
def prefixEnd_1473159 : Nat := 4983230072969 + 3 ^ 40 * 1473159 * 2
def baseEnd_1473159 : Nat := 756438647496906992337571

theorem tailTrace_1473159 : CollatzResearch.WordTrace tailWord_1473159 prefixEnd_1473159 756438647496906992337571 := by
  unfold tailWord_1473159
  simp only [CollatzResearch.WordTrace]
  refine ⟨53730522870004013371766531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35820348580002675581177687 53730522870004013371766531)
  ·
    refine ⟨80595784305006020057649797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53730522870004013371766531 80595784305006020057649797)
    ·
      refine ⟨15111709557188628760809337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80595784305006020057649797 15111709557188628760809337)
      ·
        refine ⟨11333782167891471570607003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15111709557188628760809337 11333782167891471570607003)
        ·
          refine ⟨17000673251837207355910505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11333782167891471570607003 17000673251837207355910505)
          ·
            refine ⟨12750504938877905516932879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17000673251837207355910505 12750504938877905516932879)
            ·
              refine ⟨19125757408316858275399319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12750504938877905516932879 19125757408316858275399319)
              ·
                refine ⟨28688636112475287413098979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19125757408316858275399319 28688636112475287413098979)
                ·
                  refine ⟨43032954168712931119648469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28688636112475287413098979 43032954168712931119648469)
                  ·
                    refine ⟨1008584863329209323116761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43032954168712931119648469 1008584863329209323116761)
                    ·
                      refine ⟨756438647496906992337571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008584863329209323116761 756438647496906992337571)
                      ·
                        rfl

theorem cell23_1473159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_1473159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473159 prefixEnd_1473159 := by exact prefixLift 1473159
  have htrace : WordTrace (prefixWord ++ tailWord_1473159) baseStart_1473159 baseEnd_1473159 := by
    simpa [prefixWord, tailWord_1473159, baseEnd_1473159] using wordTrace_append hprefix tailTrace_1473159
  have hstable : (prefixWord ++ tailWord_1473159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473159).length < 2 ^ (prefixWord ++ tailWord_1473159).sum := by decide
  have hdescent : baseEnd_1473159 < baseStart_1473159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473189 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 3, 6, 2]
def baseStart_1473189 : Nat := 118140960795 + 1473189 * 2 ^ 59
def prefixEnd_1473189 : Nat := 4983230072969 + 3 ^ 40 * 1473189 * 2
def baseEnd_1473189 : Nat := 756454051916541874962433

theorem tailTrace_1473189 : CollatzResearch.WordTrace tailWord_1473189 prefixEnd_1473189 756454051916541874962433 := by
  unfold tailWord_1473189
  simp only [CollatzResearch.WordTrace]
  refine ⟨53731617059895328495358621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35821078039930218996905747 53731617059895328495358621)
  ·
    refine ⟨20149356397460748185759483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53731617059895328495358621 20149356397460748185759483)
    ·
      refine ⟨30224034596191122278639225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20149356397460748185759483 30224034596191122278639225)
      ·
        refine ⟨22668025947143341708979419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30224034596191122278639225 22668025947143341708979419)
        ·
          refine ⟨34002038920715012563469129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22668025947143341708979419 34002038920715012563469129)
          ·
            refine ⟨25501529190536259422601847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34002038920715012563469129 25501529190536259422601847)
            ·
              refine ⟨38252293785804389133902771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25501529190536259422601847 38252293785804389133902771)
              ·
                refine ⟨57378440678706583700854157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38252293785804389133902771 57378440678706583700854157)
                ·
                  refine ⟨21516915254514968887820309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57378440678706583700854157 21516915254514968887820309)
                  ·
                    refine ⟨1008605402555389166616577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21516915254514968887820309 1008605402555389166616577)
                    ·
                      refine ⟨756454051916541874962433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008605402555389166616577 756454051916541874962433)
                      ·
                        rfl

theorem cell23_1473189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_1473189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473189 prefixEnd_1473189 := by exact prefixLift 1473189
  have htrace : WordTrace (prefixWord ++ tailWord_1473189) baseStart_1473189 baseEnd_1473189 := by
    simpa [prefixWord, tailWord_1473189, baseEnd_1473189] using wordTrace_append hprefix tailTrace_1473189
  have hstable : (prefixWord ++ tailWord_1473189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473189).length < 2 ^ (prefixWord ++ tailWord_1473189).sum := by decide
  have hdescent : baseEnd_1473189 < baseStart_1473189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473209 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 3]
def baseStart_1473209 : Nat := 118140960795 + 1473209 * 2 ^ 59
def prefixEnd_1473209 : Nat := 4983230072969 + 3 ^ 40 * 1473209 * 2
def baseEnd_1473209 : Nat := 756464321529631796712341

theorem tailTrace_1473209 : CollatzResearch.WordTrace tailWord_1473209 prefixEnd_1473209 756464321529631796712341 := by
  unfold tailWord_1473209
  simp only [CollatzResearch.WordTrace]
  refine ⟨53732346519822871911086681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35821564346548581274057787 53732346519822871911086681)
  ·
    refine ⟨40299259889867153933315011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53732346519822871911086681 40299259889867153933315011)
    ·
      refine ⟨60448889834800730899972517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40299259889867153933315011 60448889834800730899972517)
      ·
        refine ⟨11334166844025137043744847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60448889834800730899972517 11334166844025137043744847)
        ·
          refine ⟨17001250266037705565617271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334166844025137043744847 17001250266037705565617271)
          ·
            refine ⟨25501875399056558348425907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17001250266037705565617271 25501875399056558348425907)
            ·
              refine ⟨38252813098584837522638861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25501875399056558348425907 38252813098584837522638861)
              ·
                refine ⟨14344804911969314070989573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38252813098584837522638861 14344804911969314070989573)
                ·
                  refine ⟨2689650920994246388310545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14344804911969314070989573 2689650920994246388310545)
                  ·
                    refine ⟨2017238190745684791232909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2689650920994246388310545 2017238190745684791232909)
                    ·
                      refine ⟨756464321529631796712341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017238190745684791232909 756464321529631796712341)
                      ·
                        rfl

theorem cell23_1473209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_1473209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473209 prefixEnd_1473209 := by exact prefixLift 1473209
  have htrace : WordTrace (prefixWord ++ tailWord_1473209) baseStart_1473209 baseEnd_1473209 := by
    simpa [prefixWord, tailWord_1473209, baseEnd_1473209] using wordTrace_append hprefix tailTrace_1473209
  have hstable : (prefixWord ++ tailWord_1473209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473209).length < 2 ^ (prefixWord ++ tailWord_1473209).sum := by decide
  have hdescent : baseEnd_1473209 < baseStart_1473209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473216 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 3, 4]
def baseStart_1473216 : Nat := 118140960795 + 1473216 * 2 ^ 59
def prefixEnd_1473216 : Nat := 4983230072969 + 3 ^ 40 * 1473216 * 2
def baseEnd_1473216 : Nat := 252155971964737756441603

theorem tailTrace_1473216 : CollatzResearch.WordTrace tailWord_1473216 prefixEnd_1473216 252155971964737756441603 := by
  unfold tailWord_1473216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26866300915398756053295751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35821734553865008071061001 26866300915398756053295751)
  ·
    refine ⟨40299451373098134079943627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26866300915398756053295751 40299451373098134079943627)
    ·
      refine ⟨60449177059647201119915441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40299451373098134079943627 60449177059647201119915441)
      ·
        refine ⟨45336882794735400839936581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60449177059647201119915441 45336882794735400839936581)
        ·
          refine ⟨8500665524012887657488109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45336882794735400839936581 8500665524012887657488109)
          ·
            refine ⟨3187749571504832871558041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8500665524012887657488109 3187749571504832871558041)
            ·
              refine ⟨2390812178628624653668531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3187749571504832871558041 2390812178628624653668531)
              ·
                refine ⟨3586218267942936980502797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2390812178628624653668531 3586218267942936980502797)
                ·
                  refine ⟨1344831850478601367688549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3586218267942936980502797 1344831850478601367688549)
                  ·
                    refine ⟨252155971964737756441603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1344831850478601367688549 252155971964737756441603)
                    ·
                      rfl

theorem cell23_1473216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 4].length) (baseStart_1473216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473216 prefixEnd_1473216 := by exact prefixLift 1473216
  have htrace : WordTrace (prefixWord ++ tailWord_1473216) baseStart_1473216 baseEnd_1473216 := by
    simpa [prefixWord, tailWord_1473216, baseEnd_1473216] using wordTrace_append hprefix tailTrace_1473216
  have hstable : (prefixWord ++ tailWord_1473216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473216).length < 2 ^ (prefixWord ++ tailWord_1473216).sum := by decide
  have hdescent : baseEnd_1473216 < baseStart_1473216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473273 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 1, 1, 3]
def baseStart_1473273 : Nat := 118140960795 + 1473273 * 2 ^ 59
def prefixEnd_1473273 : Nat := 4983230072969 + 3 ^ 40 * 1473273 * 2
def baseEnd_1473273 : Nat := 756497184291519546312047

theorem tailTrace_1473273 : CollatzResearch.WordTrace tailWord_1473273 prefixEnd_1473273 756497184291519546312047 := by
  unfold tailWord_1473273
  simp only [CollatzResearch.WordTrace]
  refine ⟨53734680791591010841416473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35823120527727340560944315 53734680791591010841416473)
  ·
    refine ⟨40301010593693258131062355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53734680791591010841416473 40301010593693258131062355)
    ·
      refine ⟨60451515890539887196593533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40301010593693258131062355 60451515890539887196593533)
      ·
        refine ⟨22669318458952457698722575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60451515890539887196593533 22669318458952457698722575)
        ·
          refine ⟨34003977688428686548083863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22669318458952457698722575 34003977688428686548083863)
          ·
            refine ⟨51005966532643029822125795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34003977688428686548083863 51005966532643029822125795)
            ·
              refine ⟨76508949798964544733188693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51005966532643029822125795 76508949798964544733188693)
              ·
                refine ⟨896589255456615758592055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 76508949798964544733188693 896589255456615758592055)
                ·
                  refine ⟨1344883883184923637888083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896589255456615758592055 1344883883184923637888083)
                  ·
                    refine ⟨2017325824777385456832125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344883883184923637888083 2017325824777385456832125)
                    ·
                      refine ⟨756497184291519546312047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017325824777385456832125 756497184291519546312047)
                      ·
                        rfl

theorem cell23_1473273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_1473273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473273 prefixEnd_1473273 := by exact prefixLift 1473273
  have htrace : WordTrace (prefixWord ++ tailWord_1473273) baseStart_1473273 baseEnd_1473273 := by
    simpa [prefixWord, tailWord_1473273, baseEnd_1473273] using wordTrace_append hprefix tailTrace_1473273
  have hstable : (prefixWord ++ tailWord_1473273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473273).length < 2 ^ (prefixWord ++ tailWord_1473273).sum := by decide
  have hdescent : baseEnd_1473273 < baseStart_1473273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473279 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_1473279 : Nat := 118140960795 + 1473279 * 2 ^ 59
def prefixEnd_1473279 : Nat := 4983230072969 + 3 ^ 40 * 1473279 * 2
def baseEnd_1473279 : Nat := 756500265175446522837019

theorem tailTrace_1473279 : CollatzResearch.WordTrace tailWord_1473279 prefixEnd_1473279 756500265175446522837019 := by
  unfold tailWord_1473279
  simp only [CollatzResearch.WordTrace]
  refine ⟨53734899629569273866134891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35823266419712849244089927 53734899629569273866134891)
  ·
    refine ⟨80602349444353910799202337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53734899629569273866134891 80602349444353910799202337)
    ·
      refine ⟨60451762083265433099401753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80602349444353910799202337 60451762083265433099401753)
      ·
        refine ⟨45338821562449074824551315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60451762083265433099401753 45338821562449074824551315)
        ·
          refine ⟨68008232343673612236826973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45338821562449074824551315 68008232343673612236826973)
          ·
            refine ⟨25503087128877604588810115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68008232343673612236826973 25503087128877604588810115)
            ·
              refine ⟨38254630693316406883215173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25503087128877604588810115 38254630693316406883215173)
              ·
                refine ⟨7172743254996826290602845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38254630693316406883215173 7172743254996826290602845)
                ·
                  refine ⟨2689778720623809858976067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7172743254996826290602845 2689778720623809858976067)
                  ·
                    refine ⟨4034668080935714788464101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2689778720623809858976067 4034668080935714788464101)
                    ·
                      refine ⟨756500265175446522837019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4034668080935714788464101 756500265175446522837019)
                      ·
                        rfl

theorem cell23_1473279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_1473279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473279 prefixEnd_1473279 := by exact prefixLift 1473279
  have htrace : WordTrace (prefixWord ++ tailWord_1473279) baseStart_1473279 baseEnd_1473279 := by
    simpa [prefixWord, tailWord_1473279, baseEnd_1473279] using wordTrace_append hprefix tailTrace_1473279
  have hstable : (prefixWord ++ tailWord_1473279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473279).length < 2 ^ (prefixWord ++ tailWord_1473279).sum := by decide
  have hdescent : baseEnd_1473279 < baseStart_1473279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473313 : List Nat := [1, 2, 3, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1473313 : Nat := 118140960795 + 1473313 * 2 ^ 59
def prefixEnd_1473313 : Nat := 4983230072969 + 3 ^ 40 * 1473313 * 2
def baseEnd_1473313 : Nat := 756517723517699389811863

theorem tailTrace_1473313 : CollatzResearch.WordTrace tailWord_1473313 prefixEnd_1473313 756517723517699389811863 := by
  unfold tailWord_1473313
  simp only [CollatzResearch.WordTrace]
  refine ⟨53736139711446097672872593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35824093140964065115248395 53736139711446097672872593)
  ·
    refine ⟨40302104783584573254654445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53736139711446097672872593 40302104783584573254654445)
    ·
      refine ⟨15113289293844214970495417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40302104783584573254654445 15113289293844214970495417)
      ·
        refine ⟨11334966970383161227871563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15113289293844214970495417 11334966970383161227871563)
        ·
          refine ⟨17002450455574741841807345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11334966970383161227871563 17002450455574741841807345)
          ·
            refine ⟨12751837841681056381355509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17002450455574741841807345 12751837841681056381355509)
            ·
              refine ⟨1195484797657599035752079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12751837841681056381355509 1195484797657599035752079)
              ·
                refine ⟨1793227196486398553628119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195484797657599035752079 1793227196486398553628119)
                ·
                  refine ⟨2689840794729597830442179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793227196486398553628119 2689840794729597830442179)
                  ·
                    refine ⟨4034761192094396745663269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2689840794729597830442179 4034761192094396745663269)
                    ·
                      refine ⟨756517723517699389811863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4034761192094396745663269 756517723517699389811863)
                      ·
                        rfl

theorem cell23_1473313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1473313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473313 prefixEnd_1473313 := by exact prefixLift 1473313
  have htrace : WordTrace (prefixWord ++ tailWord_1473313) baseStart_1473313 baseEnd_1473313 := by
    simpa [prefixWord, tailWord_1473313, baseEnd_1473313] using wordTrace_append hprefix tailTrace_1473313
  have hstable : (prefixWord ++ tailWord_1473313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473313).length < 2 ^ (prefixWord ++ tailWord_1473313).sum := by decide
  have hdescent : baseEnd_1473313 < baseStart_1473313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473364 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 1, 2, 2]
def baseStart_1473364 : Nat := 118140960795 + 1473364 * 2 ^ 59
def prefixEnd_1473364 : Nat := 4983230072969 + 3 ^ 40 * 1473364 * 2
def baseEnd_1473364 : Nat := 756543911031078690274129

theorem tailTrace_1473364 : CollatzResearch.WordTrace tailWord_1473364 prefixEnd_1473364 756543911031078690274129 := by
  unfold tailWord_1473364
  simp only [CollatzResearch.WordTrace]
  refine ⟨26868999917130666691489573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35825333222840888921986097 26868999917130666691489573)
  ·
    refine ⟨5037937484462000004654295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26868999917130666691489573 5037937484462000004654295)
    ·
      refine ⟨7556906226693000006981443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5037937484462000004654295 7556906226693000006981443)
      ·
        refine ⟨11335359340039500010472165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7556906226693000006981443 11335359340039500010472165)
        ·
          refine ⟨2125379876257406251963531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11335359340039500010472165 2125379876257406251963531)
          ·
            refine ⟨3188069814386109377945297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125379876257406251963531 3188069814386109377945297)
            ·
              refine ⟨2391052360789582033458973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188069814386109377945297 2391052360789582033458973)
              ·
                refine ⟨896644635296093262547115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2391052360789582033458973 896644635296093262547115)
                ·
                  refine ⟨1344966952944139893820673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896644635296093262547115 1344966952944139893820673)
                  ·
                    refine ⟨1008725214708104920365505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1344966952944139893820673 1008725214708104920365505)
                    ·
                      refine ⟨756543911031078690274129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008725214708104920365505 756543911031078690274129)
                      ·
                        rfl

theorem cell23_1473364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_1473364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473364 prefixEnd_1473364 := by exact prefixLift 1473364
  have htrace : WordTrace (prefixWord ++ tailWord_1473364) baseStart_1473364 baseEnd_1473364 := by
    simpa [prefixWord, tailWord_1473364, baseEnd_1473364] using wordTrace_append hprefix tailTrace_1473364
  have hstable : (prefixWord ++ tailWord_1473364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473364).length < 2 ^ (prefixWord ++ tailWord_1473364).sum := by decide
  have hdescent : baseEnd_1473364 < baseStart_1473364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473380 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_1473380 : Nat := 118140960795 + 1473380 * 2 ^ 59
def prefixEnd_1473380 : Nat := 4983230072969 + 3 ^ 40 * 1473380 * 2
def baseEnd_1473380 : Nat := 756552126721550627674055

theorem tailTrace_1473380 : CollatzResearch.WordTrace tailWord_1473380 prefixEnd_1473380 756552126721550627674055 := by
  unfold tailWord_1473380
  simp only [CollatzResearch.WordTrace]
  refine ⟨26869291701101684057780797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35825722268135578743707729 26869291701101684057780797)
  ·
    refine ⟨10075984387913131521667799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26869291701101684057780797 10075984387913131521667799)
    ·
      refine ⟨15113976581869697282501699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10075984387913131521667799 15113976581869697282501699)
      ·
        refine ⟨22670964872804545923752549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15113976581869697282501699 22670964872804545923752549)
        ·
          refine ⟨4250805913650852360703603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22670964872804545923752549 4250805913650852360703603)
          ·
            refine ⟨6376208870476278541055405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4250805913650852360703603 6376208870476278541055405)
            ·
              refine ⟨2391078326428604452895777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6376208870476278541055405 2391078326428604452895777)
              ·
                refine ⟨1793308744821453339671833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391078326428604452895777 1793308744821453339671833)
                ·
                  refine ⟨1344981558616090004753875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1793308744821453339671833 1344981558616090004753875)
                  ·
                    refine ⟨2017472337924135007130813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344981558616090004753875 2017472337924135007130813)
                    ·
                      refine ⟨756552126721550627674055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017472337924135007130813 756552126721550627674055)
                      ·
                        rfl

theorem cell23_1473380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_1473380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473380 prefixEnd_1473380 := by exact prefixLift 1473380
  have htrace : WordTrace (prefixWord ++ tailWord_1473380) baseStart_1473380 baseEnd_1473380 := by
    simpa [prefixWord, tailWord_1473380, baseEnd_1473380] using wordTrace_append hprefix tailTrace_1473380
  have hstable : (prefixWord ++ tailWord_1473380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473380).length < 2 ^ (prefixWord ++ tailWord_1473380).sum := by decide
  have hdescent : baseEnd_1473380 < baseStart_1473380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473397 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_1473397 : Nat := 118140960795 + 1473397 * 2 ^ 59
def prefixEnd_1473397 : Nat := 4983230072969 + 3 ^ 40 * 1473397 * 2
def baseEnd_1473397 : Nat := 756560855892677061161477

theorem tailTrace_1473397 : CollatzResearch.WordTrace tailWord_1473397 prefixEnd_1473397 756560855892677061161477 := by
  unfold tailWord_1473397
  simp only [CollatzResearch.WordTrace]
  refine ⟨53739203443141780018930445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35826135628761186679286963 53739203443141780018930445)
  ·
    refine ⟨20152201291178167507098917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53739203443141780018930445 20152201291178167507098917)
    ·
      refine ⟨3778537742095906407581047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20152201291178167507098917 3778537742095906407581047)
      ·
        refine ⟨5667806613143859611371571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778537742095906407581047 5667806613143859611371571)
        ·
          refine ⟨8501709919715789417057357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5667806613143859611371571 8501709919715789417057357)
          ·
            refine ⟨3188141219893421031396509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8501709919715789417057357 3188141219893421031396509)
            ·
              refine ⟨1195552957460032886773691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3188141219893421031396509 1195552957460032886773691)
              ·
                refine ⟨1793329436190049330160537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195552957460032886773691 1793329436190049330160537)
                ·
                  refine ⟨1344997077142536997620403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1793329436190049330160537 1344997077142536997620403)
                  ·
                    refine ⟨2017495615713805496430605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1344997077142536997620403 2017495615713805496430605)
                    ·
                      refine ⟨756560855892677061161477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017495615713805496430605 756560855892677061161477)
                      ·
                        rfl

theorem cell23_1473397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_1473397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473397 prefixEnd_1473397 := by exact prefixLift 1473397
  have htrace : WordTrace (prefixWord ++ tailWord_1473397) baseStart_1473397 baseEnd_1473397 := by
    simpa [prefixWord, tailWord_1473397, baseEnd_1473397] using wordTrace_append hprefix tailTrace_1473397
  have hstable : (prefixWord ++ tailWord_1473397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473397).length < 2 ^ (prefixWord ++ tailWord_1473397).sum := by decide
  have hdescent : baseEnd_1473397 < baseStart_1473397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473403 : List Nat := [1, 1, 1, 1, 1, 5, 5, 1, 1, 4, 2]
def baseStart_1473403 : Nat := 118140960795 + 1473403 * 2 ^ 59
def prefixEnd_1473403 : Nat := 4983230072969 + 3 ^ 40 * 1473403 * 2
def baseEnd_1473403 : Nat := 756563936776604037686449

theorem tailTrace_1473403 : CollatzResearch.WordTrace tailWord_1473403 prefixEnd_1473403 756563936776604037686449 := by
  unfold tailWord_1473403
  simp only [CollatzResearch.WordTrace]
  refine ⟨53739422281120043043648863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35826281520746695362432575 53739422281120043043648863)
  ·
    refine ⟨80609133421680064565473295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53739422281120043043648863 80609133421680064565473295)
    ·
      refine ⟨120913700132520096848209943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80609133421680064565473295 120913700132520096848209943)
      ·
        refine ⟨181370550198780145272314915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120913700132520096848209943 181370550198780145272314915)
        ·
          refine ⟨272055825298170217908472373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181370550198780145272314915 272055825298170217908472373)
          ·
            refine ⟨25505233621703457928919285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 272055825298170217908472373 25505233621703457928919285)
            ·
              refine ⟨2391115652034699180836183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25505233621703457928919285 2391115652034699180836183)
              ·
                refine ⟨3586673478052048771254275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391115652034699180836183 3586673478052048771254275)
                ·
                  refine ⟨5380010217078073156881413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3586673478052048771254275 5380010217078073156881413)
                  ·
                    refine ⟨1008751915702138716915265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5380010217078073156881413 1008751915702138716915265)
                    ·
                      refine ⟨756563936776604037686449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008751915702138716915265 756563936776604037686449)
                      ·
                        rfl

theorem cell23_1473403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 1, 1, 4, 2].length) (baseStart_1473403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473403 prefixEnd_1473403 := by exact prefixLift 1473403
  have htrace : WordTrace (prefixWord ++ tailWord_1473403) baseStart_1473403 baseEnd_1473403 := by
    simpa [prefixWord, tailWord_1473403, baseEnd_1473403] using wordTrace_append hprefix tailTrace_1473403
  have hstable : (prefixWord ++ tailWord_1473403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473403).length < 2 ^ (prefixWord ++ tailWord_1473403).sum := by decide
  have hdescent : baseEnd_1473403 < baseStart_1473403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473494 : List Nat := [5, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_1473494 : Nat := 118140960795 + 1473494 * 2 ^ 59
def prefixEnd_1473494 : Nat := 4983230072969 + 3 ^ 40 * 1473494 * 2
def baseEnd_1473494 : Nat := 84067851501795909072059

theorem tailTrace_1473494 : CollatzResearch.WordTrace tailWord_1473494 prefixEnd_1473494 84067851501795909072059 := by
  unfold tailWord_1473494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358921332736897849075721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35828494215860243723474357 3358921332736897849075721)
  ·
    refine ⟨2519190999552673386806791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3358921332736897849075721 2519190999552673386806791)
    ·
      refine ⟨3778786499329010080210187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519190999552673386806791 3778786499329010080210187)
      ·
        refine ⟨5668179748993515120315281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3778786499329010080210187 5668179748993515120315281)
        ·
          refine ⟨4251134811745136340236461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668179748993515120315281 4251134811745136340236461)
          ·
            refine ⟨1594175554404426127588673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251134811745136340236461 1594175554404426127588673)
            ·
              refine ⟨1195631665803319595691505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594175554404426127588673 1195631665803319595691505)
              ·
                refine ⟨896723749352489696768629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195631665803319595691505 896723749352489696768629)
                ·
                  refine ⟨84067851501795909072059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 896723749352489696768629 84067851501795909072059)
                  ·
                    rfl

theorem cell23_1473494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_1473494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473494 prefixEnd_1473494 := by exact prefixLift 1473494
  have htrace : WordTrace (prefixWord ++ tailWord_1473494) baseStart_1473494 baseEnd_1473494 := by
    simpa [prefixWord, tailWord_1473494, baseEnd_1473494] using wordTrace_append hprefix tailTrace_1473494
  have hstable : (prefixWord ++ tailWord_1473494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473494).length < 2 ^ (prefixWord ++ tailWord_1473494).sum := by decide
  have hdescent : baseEnd_1473494 < baseStart_1473494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473524 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1473524 : Nat := 118140960795 + 1473524 * 2 ^ 59
def prefixEnd_1473524 : Nat := 4983230072969 + 3 ^ 40 * 1473524 * 2
def baseEnd_1473524 : Nat := 252208689311932688091131

theorem tailTrace_1473524 : CollatzResearch.WordTrace tailWord_1473524 prefixEnd_1473524 252208689311932688091131 := by
  unfold tailWord_1473524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26871917756840840354401813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35829223675787787139202417 26871917756840840354401813)
  ·
    refine ⟨1259621144851914391612585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 26871917756840840354401813 1259621144851914391612585)
    ·
      refine ⟨944715858638935793709439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1259621144851914391612585 944715858638935793709439)
      ·
        refine ⟨1417073787958403690564159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944715858638935793709439 1417073787958403690564159)
        ·
          refine ⟨2125610681937605535846239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417073787958403690564159 2125610681937605535846239)
          ·
            refine ⟨3188416022906408303769359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125610681937605535846239 3188416022906408303769359)
            ·
              refine ⟨4782624034359612455654039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3188416022906408303769359 4782624034359612455654039)
              ·
                refine ⟨7173936051539418683481059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4782624034359612455654039 7173936051539418683481059)
                ·
                  refine ⟨10760904077309128025221589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7173936051539418683481059 10760904077309128025221589)
                  ·
                    refine ⟨252208689311932688091131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10760904077309128025221589 252208689311932688091131)
                    ·
                      rfl

theorem cell23_1473524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1473524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473524 prefixEnd_1473524 := by exact prefixLift 1473524
  have htrace : WordTrace (prefixWord ++ tailWord_1473524) baseStart_1473524 baseEnd_1473524 := by
    simpa [prefixWord, tailWord_1473524, baseEnd_1473524] using wordTrace_append hprefix tailTrace_1473524
  have hstable : (prefixWord ++ tailWord_1473524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473524).length < 2 ^ (prefixWord ++ tailWord_1473524).sum := by decide
  have hdescent : baseEnd_1473524 < baseStart_1473524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473537 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1473537 : Nat := 118140960795 + 1473537 * 2 ^ 59
def prefixEnd_1473537 : Nat := 4983230072969 + 3 ^ 40 * 1473537 * 2
def baseEnd_1473537 : Nat := 252210914394768837803611

theorem tailTrace_1473537 : CollatzResearch.WordTrace tailWord_1473537 prefixEnd_1473537 252210914394768837803611 := by
  unfold tailWord_1473537
  simp only [CollatzResearch.WordTrace]
  refine ⟨53744309662634583929026865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35829539775089722619351243 53744309662634583929026865)
  ·
    refine ⟨40308232246975937946770149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53744309662634583929026865 40308232246975937946770149)
    ·
      refine ⟨7557793546307988365019403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40308232246975937946770149 7557793546307988365019403)
      ·
        refine ⟨11336690319461982547529105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7557793546307988365019403 11336690319461982547529105)
        ·
          refine ⟨8502517739596486910646829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11336690319461982547529105 8502517739596486910646829)
          ·
            refine ⟨3188444152348682591492561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8502517739596486910646829 3188444152348682591492561)
            ·
              refine ⟨2391333114261511943619421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3188444152348682591492561 2391333114261511943619421)
              ·
                refine ⟨896749917848066978857283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2391333114261511943619421 896749917848066978857283)
                ·
                  refine ⟨1345124876772100468285925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896749917848066978857283 1345124876772100468285925)
                  ·
                    refine ⟨252210914394768837803611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1345124876772100468285925 252210914394768837803611)
                    ·
                      rfl

theorem cell23_1473537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1473537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473537 prefixEnd_1473537 := by exact prefixLift 1473537
  have htrace : WordTrace (prefixWord ++ tailWord_1473537) baseStart_1473537 baseEnd_1473537 := by
    simpa [prefixWord, tailWord_1473537, baseEnd_1473537] using wordTrace_append hprefix tailTrace_1473537
  have hstable : (prefixWord ++ tailWord_1473537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473537).length < 2 ^ (prefixWord ++ tailWord_1473537).sum := by decide
  have hdescent : baseEnd_1473537 < baseStart_1473537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473550 : List Nat := [4, 1, 1, 2, 2, 4, 1, 2, 6]
def baseStart_1473550 : Nat := 118140960795 + 1473550 * 2 ^ 59
def prefixEnd_1473550 : Nat := 4983230072969 + 3 ^ 40 * 1473550 * 2
def baseEnd_1473550 : Nat := 84071046492534995838697

theorem tailTrace_1473550 : CollatzResearch.WordTrace tailWord_1473550 prefixEnd_1473550 84071046492534995838697 := by
  unfold tailWord_1473550
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718097976448435893656263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35829855874391658099500069 6718097976448435893656263)
  ·
    refine ⟨10077146964672653840484395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6718097976448435893656263 10077146964672653840484395)
    ·
      refine ⟨15115720447008980760726593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10077146964672653840484395 15115720447008980760726593)
      ·
        refine ⟨11336790335256735570544945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15115720447008980760726593 11336790335256735570544945)
        ·
          refine ⟨8502592751442551677908709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11336790335256735570544945 8502592751442551677908709)
          ·
            refine ⟨1594236140895478439607883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8502592751442551677908709 1594236140895478439607883)
            ·
              refine ⟨2391354211343217659411825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594236140895478439607883 2391354211343217659411825)
              ·
                refine ⟨1793515658507413244558869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391354211343217659411825 1793515658507413244558869)
                ·
                  refine ⟨84071046492534995838697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1793515658507413244558869 84071046492534995838697)
                  ·
                    rfl

theorem cell23_1473550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_1473550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473550 prefixEnd_1473550 := by exact prefixLift 1473550
  have htrace : WordTrace (prefixWord ++ tailWord_1473550) baseStart_1473550 baseEnd_1473550 := by
    simpa [prefixWord, tailWord_1473550, baseEnd_1473550] using wordTrace_append hprefix tailTrace_1473550
  have hstable : (prefixWord ++ tailWord_1473550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473550).length < 2 ^ (prefixWord ++ tailWord_1473550).sum := by decide
  have hdescent : baseEnd_1473550 < baseStart_1473550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473560 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1473560 : Nat := 118140960795 + 1473560 * 2 ^ 59
def prefixEnd_1473560 : Nat := 4983230072969 + 3 ^ 40 * 1473560 * 2
def baseEnd_1473560 : Nat := 756644553239359923423227

theorem tailTrace_1473560 : CollatzResearch.WordTrace tailWord_1473560 prefixEnd_1473560 756644553239359923423227 := by
  unfold tailWord_1473560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26872574270775629428557067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35830099027700839238076089 26872574270775629428557067)
  ·
    refine ⟨40308861406163444142835601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26872574270775629428557067 40308861406163444142835601)
    ·
      refine ⟨30231646054622583107126701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40308861406163444142835601 30231646054622583107126701)
      ·
        refine ⟨11336867270483468665172513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30231646054622583107126701 11336867270483468665172513)
        ·
          refine ⟨8502650452862601498879385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11336867270483468665172513 8502650452862601498879385)
          ·
            refine ⟨6376987839646951124159539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8502650452862601498879385 6376987839646951124159539)
            ·
              refine ⟨9565481759470426686239309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6376987839646951124159539 9565481759470426686239309)
              ·
                refine ⟨3587055659801410007339741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9565481759470426686239309 3587055659801410007339741)
                ·
                  refine ⟨1345145872425528752752403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3587055659801410007339741 1345145872425528752752403)
                  ·
                    refine ⟨2017718808638293129128605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345145872425528752752403 2017718808638293129128605)
                    ·
                      refine ⟨756644553239359923423227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017718808638293129128605 756644553239359923423227)
                      ·
                        rfl

theorem cell23_1473560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1473560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473560 prefixEnd_1473560 := by exact prefixLift 1473560
  have htrace : WordTrace (prefixWord ++ tailWord_1473560) baseStart_1473560 baseEnd_1473560 := by
    simpa [prefixWord, tailWord_1473560, baseEnd_1473560] using wordTrace_append hprefix tailTrace_1473560
  have hstable : (prefixWord ++ tailWord_1473560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473560).length < 2 ^ (prefixWord ++ tailWord_1473560).sum := by decide
  have hdescent : baseEnd_1473560 < baseStart_1473560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473570 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_1473570 : Nat := 118140960795 + 1473570 * 2 ^ 59
def prefixEnd_1473570 : Nat := 4983230072969 + 3 ^ 40 * 1473570 * 2
def baseEnd_1473570 : Nat := 756649688045904884298181

theorem tailTrace_1473570 : CollatzResearch.WordTrace tailWord_1473570 prefixEnd_1473570 756649688045904884298181 := by
  unfold tailWord_1473570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436378317878757641244541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35830342181010020376652109 13436378317878757641244541)
  ·
    refine ⟨5038641869204534115466703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13436378317878757641244541 5038641869204534115466703)
    ·
      refine ⟨7557962803806801173200055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5038641869204534115466703 7557962803806801173200055)
      ·
        refine ⟨11336944205710201759800083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7557962803806801173200055 11336944205710201759800083)
        ·
          refine ⟨17005416308565302639700125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11336944205710201759800083 17005416308565302639700125)
          ·
            refine ⟨6377031115711988489887547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17005416308565302639700125 6377031115711988489887547)
            ·
              refine ⟨9565546673567982734831321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377031115711988489887547 9565546673567982734831321)
              ·
                refine ⟨7174160005175987051123491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9565546673567982734831321 7174160005175987051123491)
                ·
                  refine ⟨10761240007763980576685237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7174160005175987051123491 10761240007763980576685237)
                  ·
                    refine ⟨1008866250727873179064241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10761240007763980576685237 1008866250727873179064241)
                    ·
                      refine ⟨756649688045904884298181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008866250727873179064241 756649688045904884298181)
                      ·
                        rfl

theorem cell23_1473570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_1473570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473570 prefixEnd_1473570 := by exact prefixLift 1473570
  have htrace : WordTrace (prefixWord ++ tailWord_1473570) baseStart_1473570 baseEnd_1473570 := by
    simpa [prefixWord, tailWord_1473570, baseEnd_1473570] using wordTrace_append hprefix tailTrace_1473570
  have hstable : (prefixWord ++ tailWord_1473570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473570).length < 2 ^ (prefixWord ++ tailWord_1473570).sum := by decide
  have hdescent : baseEnd_1473570 < baseStart_1473570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473603 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5]
def baseStart_1473603 : Nat := 118140960795 + 1473603 * 2 ^ 59
def prefixEnd_1473603 : Nat := 4983230072969 + 3 ^ 40 * 1473603 * 2
def baseEnd_1473603 : Nat := 756666632907503255185529

theorem tailTrace_1473603 : CollatzResearch.WordTrace tailWord_1473603 prefixEnd_1473603 756666632907503255185529 := by
  unfold tailWord_1473603
  simp only [CollatzResearch.WordTrace]
  refine ⟨53746716880395477200929463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35831144586930318133952975 53746716880395477200929463)
  ·
    refine ⟨80620075320593215801394195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53746716880395477200929463 80620075320593215801394195)
    ·
      refine ⟨120930112980889823702091293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80620075320593215801394195 120930112980889823702091293)
      ·
        refine ⟨45348792367833683888284235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120930112980889823702091293 45348792367833683888284235)
        ·
          refine ⟨68023188551750525832426353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45348792367833683888284235 68023188551750525832426353)
          ·
            refine ⟨51017391413812894374319765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68023188551750525832426353 51017391413812894374319765)
            ·
              refine ⟨2391440222522479423796239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51017391413812894374319765 2391440222522479423796239)
              ·
                refine ⟨3587160333783719135694359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391440222522479423796239 3587160333783719135694359)
                ·
                  refine ⟨5380740500675578703541539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587160333783719135694359 5380740500675578703541539)
                  ·
                    refine ⟨8071110751013368055312309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5380740500675578703541539 8071110751013368055312309)
                    ·
                      refine ⟨756666632907503255185529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8071110751013368055312309 756666632907503255185529)
                      ·
                        rfl

theorem cell23_1473603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_1473603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473603 prefixEnd_1473603 := by exact prefixLift 1473603
  have htrace : WordTrace (prefixWord ++ tailWord_1473603) baseStart_1473603 baseEnd_1473603 := by
    simpa [prefixWord, tailWord_1473603, baseEnd_1473603] using wordTrace_append hprefix tailTrace_1473603
  have hstable : (prefixWord ++ tailWord_1473603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473603).length < 2 ^ (prefixWord ++ tailWord_1473603).sum := by decide
  have hdescent : baseEnd_1473603 < baseStart_1473603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473617 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_1473617 : Nat := 118140960795 + 1473617 * 2 ^ 59
def prefixEnd_1473617 : Nat := 4983230072969 + 3 ^ 40 * 1473617 * 2
def baseEnd_1473617 : Nat := 756673821636666200410465

theorem tailTrace_1473617 : CollatzResearch.WordTrace tailWord_1473617 prefixEnd_1473617 756673821636666200410465 := by
  unfold tailWord_1473617
  simp only [CollatzResearch.WordTrace]
  refine ⟨53747227502344757591939105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35831485001563171727959403 53747227502344757591939105)
  ·
    refine ⟨40310420626758568193954329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53747227502344757591939105 40310420626758568193954329)
    ·
      refine ⟨30232815470068926145465747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40310420626758568193954329 30232815470068926145465747)
      ·
        refine ⟨45349223205103389218198621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30232815470068926145465747 45349223205103389218198621)
        ·
          refine ⟨17005958701913770956824483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45349223205103389218198621 17005958701913770956824483)
          ·
            refine ⟨25508938052870656435236725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17005958701913770956824483 25508938052870656435236725)
            ·
              refine ⟨2391462942456624040803443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25508938052870656435236725 2391462942456624040803443)
              ·
                refine ⟨3587194413684936061205165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2391462942456624040803443 3587194413684936061205165)
                ·
                  refine ⟨1345197905131851022951937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3587194413684936061205165 1345197905131851022951937)
                  ·
                    refine ⟨1008898428848888267213953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345197905131851022951937 1008898428848888267213953)
                    ·
                      refine ⟨756673821636666200410465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008898428848888267213953 756673821636666200410465)
                      ·
                        rfl

theorem cell23_1473617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_1473617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473617 prefixEnd_1473617 := by exact prefixLift 1473617
  have htrace : WordTrace (prefixWord ++ tailWord_1473617) baseStart_1473617 baseEnd_1473617 := by
    simpa [prefixWord, tailWord_1473617, baseEnd_1473617] using wordTrace_append hprefix tailTrace_1473617
  have hstable : (prefixWord ++ tailWord_1473617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473617).length < 2 ^ (prefixWord ++ tailWord_1473617).sum := by decide
  have hdescent : baseEnd_1473617 < baseStart_1473617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473634 : List Nat := [3, 3, 2, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1473634 : Nat := 118140960795 + 1473634 * 2 ^ 59
def prefixEnd_1473634 : Nat := 4983230072969 + 3 ^ 40 * 1473634 * 2
def baseEnd_1473634 : Nat := 756682550807792633897887

theorem tailTrace_1473634 : CollatzResearch.WordTrace tailWord_1473634 prefixEnd_1473634 756682550807792633897887 := by
  unfold tailWord_1473634
  simp only [CollatzResearch.WordTrace]
  refine ⟨13436961885820792373826989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35831898362188779663538637 13436961885820792373826989)
  ·
    refine ⟨5038860707182797140185121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13436961885820792373826989 5038860707182797140185121)
    ·
      refine ⟨3779145530387097855138841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5038860707182797140185121 3779145530387097855138841)
      ·
        refine ⟨2834359147790323391354131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3779145530387097855138841 2834359147790323391354131)
        ·
          refine ⟨4251538721685485087031197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2834359147790323391354131 4251538721685485087031197)
          ·
            refine ⟨1594327020632056907636699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4251538721685485087031197 1594327020632056907636699)
            ·
              refine ⟨2391490530948085361455049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1594327020632056907636699 2391490530948085361455049)
              ·
                refine ⟨1793617898211064021091287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391490530948085361455049 1793617898211064021091287)
                ·
                  refine ⟨2690426847316596031636931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793617898211064021091287 2690426847316596031636931)
                  ·
                    refine ⟨4035640270974894047455397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2690426847316596031636931 4035640270974894047455397)
                    ·
                      refine ⟨756682550807792633897887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4035640270974894047455397 756682550807792633897887)
                      ·
                        rfl

theorem cell23_1473634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1473634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473634 prefixEnd_1473634 := by exact prefixLift 1473634
  have htrace : WordTrace (prefixWord ++ tailWord_1473634) baseStart_1473634 baseEnd_1473634 := by
    simpa [prefixWord, tailWord_1473634, baseEnd_1473634] using wordTrace_append hprefix tailTrace_1473634
  have hstable : (prefixWord ++ tailWord_1473634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473634).length < 2 ^ (prefixWord ++ tailWord_1473634).sum := by decide
  have hdescent : baseEnd_1473634 < baseStart_1473634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473650 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_1473650 : Nat := 118140960795 + 1473650 * 2 ^ 59
def prefixEnd_1473650 : Nat := 4983230072969 + 3 ^ 40 * 1473650 * 2
def baseEnd_1473650 : Nat := 756690766498264571297813

theorem tailTrace_1473650 : CollatzResearch.WordTrace tailWord_1473650 prefixEnd_1473650 756690766498264571297813 := by
  unfold tailWord_1473650
  simp only [CollatzResearch.WordTrace]
  refine ⟨13437107777806301056972601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35832287407483469485260269 13437107777806301056972601)
  ·
    refine ⟨10077830833354725792729451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13437107777806301056972601 10077830833354725792729451)
    ·
      refine ⟨15116746250032088689094177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10077830833354725792729451 15116746250032088689094177)
      ·
        refine ⟨11337559687524066516820633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15116746250032088689094177 11337559687524066516820633)
        ·
          refine ⟨8503169765643049887615475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11337559687524066516820633 8503169765643049887615475)
          ·
            refine ⟨12754754648464574831423213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503169765643049887615475 12754754648464574831423213)
            ·
              refine ⟨4783032993174215561783705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12754754648464574831423213 4783032993174215561783705)
              ·
                refine ⟨3587274744880661671337779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4783032993174215561783705 3587274744880661671337779)
                ·
                  refine ⟨5380912117320992507006669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3587274744880661671337779 5380912117320992507006669)
                  ·
                    refine ⟨2017842043995372190127501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5380912117320992507006669 2017842043995372190127501)
                    ·
                      refine ⟨756690766498264571297813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017842043995372190127501 756690766498264571297813)
                      ·
                        rfl

theorem cell23_1473650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_1473650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473650 prefixEnd_1473650 := by exact prefixLift 1473650
  have htrace : WordTrace (prefixWord ++ tailWord_1473650) baseStart_1473650 baseEnd_1473650 := by
    simpa [prefixWord, tailWord_1473650, baseEnd_1473650] using wordTrace_append hprefix tailTrace_1473650
  have hstable : (prefixWord ++ tailWord_1473650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473650).length < 2 ^ (prefixWord ++ tailWord_1473650).sum := by decide
  have hdescent : baseEnd_1473650 < baseStart_1473650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473654 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3]
def baseStart_1473654 : Nat := 118140960795 + 1473654 * 2 ^ 59
def prefixEnd_1473654 : Nat := 4983230072969 + 3 ^ 40 * 1473654 * 2
def baseEnd_1473654 : Nat := 756692820420882555647795

theorem tailTrace_1473654 : CollatzResearch.WordTrace tailWord_1473654 prefixEnd_1473654 756692820420882555647795 := by
  unfold tailWord_1473654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3359286062700669556939751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35832384668807141940690677 3359286062700669556939751)
  ·
    refine ⟨5038929094051004335409627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3359286062700669556939751 5038929094051004335409627)
    ·
      refine ⟨7558393641076506503114441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5038929094051004335409627 7558393641076506503114441)
      ·
        refine ⟨5668795230807379877335831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7558393641076506503114441 5668795230807379877335831)
        ·
          refine ⟨8503192846211069816003747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5668795230807379877335831 8503192846211069816003747)
          ·
            refine ⟨12754789269316604724005621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8503192846211069816003747 12754789269316604724005621)
            ·
              refine ⟨1195761493998431692875527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12754789269316604724005621 1195761493998431692875527)
              ·
                refine ⟨1793642240997647539313291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1195761493998431692875527 1793642240997647539313291)
                ·
                  refine ⟨2690463361496471308969937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1793642240997647539313291 2690463361496471308969937)
                  ·
                    refine ⟨2017847521122353481727453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2690463361496471308969937 2017847521122353481727453)
                    ·
                      refine ⟨756692820420882555647795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017847521122353481727453 756692820420882555647795)
                      ·
                        rfl

theorem cell23_1473654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_1473654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473654 prefixEnd_1473654 := by exact prefixLift 1473654
  have htrace : WordTrace (prefixWord ++ tailWord_1473654) baseStart_1473654 baseEnd_1473654 := by
    simpa [prefixWord, tailWord_1473654, baseEnd_1473654] using wordTrace_append hprefix tailTrace_1473654
  have hstable : (prefixWord ++ tailWord_1473654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473654).length < 2 ^ (prefixWord ++ tailWord_1473654).sum := by decide
  have hdescent : baseEnd_1473654 < baseStart_1473654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473662 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1473662 : Nat := 118140960795 + 1473662 * 2 ^ 59
def prefixEnd_1473662 : Nat := 4983230072969 + 3 ^ 40 * 1473662 * 2
def baseEnd_1473662 : Nat := 756696928266118524347759

theorem tailTrace_1473662 : CollatzResearch.WordTrace tailWord_1473662 prefixEnd_1473662 756696928266118524347759 := by
  unfold tailWord_1473662
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718608598397716284665905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35832579191454486851551493 6718608598397716284665905)
  ·
    refine ⟨5038956448798287213499429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6718608598397716284665905 5038956448798287213499429)
    ·
      refine ⟨944804334149678852531143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5038956448798287213499429 944804334149678852531143)
      ·
        refine ⟨1417206501224518278796715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 944804334149678852531143 1417206501224518278796715)
        ·
          refine ⟨2125809751836777418195073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1417206501224518278796715 2125809751836777418195073)
          ·
            refine ⟨1594357313877583063646305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2125809751836777418195073 1594357313877583063646305)
            ·
              refine ⟨1195767985408187297734729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594357313877583063646305 1195767985408187297734729)
              ·
                refine ⟨896825989056140473301047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195767985408187297734729 896825989056140473301047)
                ·
                  refine ⟨1345238983584210709951571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896825989056140473301047 1345238983584210709951571)
                  ·
                    refine ⟨2017858475376316064927357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345238983584210709951571 2017858475376316064927357)
                    ·
                      refine ⟨756696928266118524347759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017858475376316064927357 756696928266118524347759)
                      ·
                        rfl

theorem cell23_1473662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1473662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473662 prefixEnd_1473662 := by exact prefixLift 1473662
  have htrace : WordTrace (prefixWord ++ tailWord_1473662) baseStart_1473662 baseEnd_1473662 := by
    simpa [prefixWord, tailWord_1473662, baseEnd_1473662] using wordTrace_append hprefix tailTrace_1473662
  have hstable : (prefixWord ++ tailWord_1473662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473662).length < 2 ^ (prefixWord ++ tailWord_1473662).sum := by decide
  have hdescent : baseEnd_1473662 < baseStart_1473662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473667 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 3]
def baseStart_1473667 : Nat := 118140960795 + 1473667 * 2 ^ 59
def prefixEnd_1473667 : Nat := 4983230072969 + 3 ^ 40 * 1473667 * 2
def baseEnd_1473667 : Nat := 756699495669391004785235

theorem tailTrace_1473667 : CollatzResearch.WordTrace tailWord_1473667 prefixEnd_1473667 756699495669391004785235 := by
  unfold tailWord_1473667
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749051152163616131259255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35832700768109077420839503 53749051152163616131259255)
  ·
    refine ⟨80623576728245424196888883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53749051152163616131259255 80623576728245424196888883)
    ·
      refine ⟨120935365092368136295333325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80623576728245424196888883 120935365092368136295333325)
      ·
        refine ⟨45350761909638051110749997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120935365092368136295333325 45350761909638051110749997)
        ·
          refine ⟨17006535716114269166531249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45350761909638051110749997 17006535716114269166531249)
          ·
            refine ⟨12754901787085701874898437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17006535716114269166531249 12754901787085701874898437)
            ·
              refine ⟨2391544085078569101543457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12754901787085701874898437 2391544085078569101543457)
              ·
                refine ⟨1793658063808926826157593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2391544085078569101543457 1793658063808926826157593)
                ·
                  refine ⟨1345243547856695119618195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1793658063808926826157593 1345243547856695119618195)
                  ·
                    refine ⟨2017865321785042679427293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1345243547856695119618195 2017865321785042679427293)
                    ·
                      refine ⟨756699495669391004785235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2017865321785042679427293 756699495669391004785235)
                      ·
                        rfl

theorem cell23_1473667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_1473667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473667 prefixEnd_1473667 := by exact prefixLift 1473667
  have htrace : WordTrace (prefixWord ++ tailWord_1473667) baseStart_1473667 baseEnd_1473667 := by
    simpa [prefixWord, tailWord_1473667, baseEnd_1473667] using wordTrace_append hprefix tailTrace_1473667
  have hstable : (prefixWord ++ tailWord_1473667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473667).length < 2 ^ (prefixWord ++ tailWord_1473667).sum := by decide
  have hdescent : baseEnd_1473667 < baseStart_1473667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473668 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_1473668 : Nat := 118140960795 + 1473668 * 2 ^ 59
def prefixEnd_1473668 : Nat := 4983230072969 + 3 ^ 40 * 1473668 * 2
def baseEnd_1473668 : Nat := 756700009150045500872731

theorem tailTrace_1473668 : CollatzResearch.WordTrace tailWord_1473668 prefixEnd_1473668 756700009150045500872731 := by
  unfold tailWord_1473668
  simp only [CollatzResearch.WordTrace]
  refine ⟨26874543812579996651022829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35832725083439995534697105 26874543812579996651022829)
  ·
    refine ⟨10077953929717498744133561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26874543812579996651022829 10077953929717498744133561)
    ·
      refine ⟨7558465447288124058100171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10077953929717498744133561 7558465447288124058100171)
      ·
        refine ⟨11337698170932186087150257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7558465447288124058100171 11337698170932186087150257)
        ·
          refine ⟨8503273628199139565362693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11337698170932186087150257 8503273628199139565362693)
          ·
            refine ⟨1594363805287338668505505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8503273628199139565362693 1594363805287338668505505)
            ·
              refine ⟨1195772853965504001379129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1594363805287338668505505 1195772853965504001379129)
              ·
                refine ⟨896829640474128001034347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1195772853965504001379129 896829640474128001034347)
                ·
                  refine ⟨1345244460711192001551521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 896829640474128001034347 1345244460711192001551521)
                  ·
                    refine ⟨1008933345533394001163641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1345244460711192001551521 1008933345533394001163641)
                    ·
                      refine ⟨756700009150045500872731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008933345533394001163641 756700009150045500872731)
                      ·
                        rfl

theorem cell23_1473668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_1473668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473668 prefixEnd_1473668 := by exact prefixLift 1473668
  have htrace : WordTrace (prefixWord ++ tailWord_1473668) baseStart_1473668 baseEnd_1473668 := by
    simpa [prefixWord, tailWord_1473668, baseEnd_1473668] using wordTrace_append hprefix tailTrace_1473668
  have hstable : (prefixWord ++ tailWord_1473668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473668).length < 2 ^ (prefixWord ++ tailWord_1473668).sum := by decide
  have hdescent : baseEnd_1473668 < baseStart_1473668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473673 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_1473673 : Nat := 118140960795 + 1473673 * 2 ^ 59
def prefixEnd_1473673 : Nat := 4983230072969 + 3 ^ 40 * 1473673 * 2
def baseEnd_1473673 : Nat := 756702576553317981310207

theorem tailTrace_1473673 : CollatzResearch.WordTrace tailWord_1473673 prefixEnd_1473673 756702576553317981310207 := by
  unfold tailWord_1473673
  simp only [CollatzResearch.WordTrace]
  refine ⟨53749269990141879155977673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35832846660094586103985115 53749269990141879155977673)
  ·
    refine ⟨40311952492606409366983255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53749269990141879155977673 40311952492606409366983255)
    ·
      refine ⟨60467928738909614050474883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40311952492606409366983255 60467928738909614050474883)
      ·
        refine ⟨90701893108364421075712325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60467928738909614050474883 90701893108364421075712325)
        ·
          refine ⟨17006604957818328951696061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90701893108364421075712325 17006604957818328951696061)
          ·
            refine ⟨6377476859181873356886023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17006604957818328951696061 6377476859181873356886023)
            ·
              refine ⟨9566215288772810035329035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6377476859181873356886023 9566215288772810035329035)
              ·
                refine ⟨14349322933159215052993553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9566215288772810035329035 14349322933159215052993553)
                ·
                  refine ⟨10761992199869411289745165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14349322933159215052993553 10761992199869411289745165)
                  ·
                    refine ⟨4035747074951029233654437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10761992199869411289745165 4035747074951029233654437)
                    ·
                      refine ⟨756702576553317981310207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4035747074951029233654437 756702576553317981310207)
                      ·
                        rfl

theorem cell23_1473673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_1473673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473673 prefixEnd_1473673 := by exact prefixLift 1473673
  have htrace : WordTrace (prefixWord ++ tailWord_1473673) baseStart_1473673 baseEnd_1473673 := by
    simpa [prefixWord, tailWord_1473673, baseEnd_1473673] using wordTrace_append hprefix tailTrace_1473673
  have hstable : (prefixWord ++ tailWord_1473673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473673).length < 2 ^ (prefixWord ++ tailWord_1473673).sum := by decide
  have hdescent : baseEnd_1473673 < baseStart_1473673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1473694 : List Nat := [4, 3, 1, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_1473694 : Nat := 118140960795 + 1473694 * 2 ^ 59
def prefixEnd_1473694 : Nat := 4983230072969 + 3 ^ 40 * 1473694 * 2
def baseEnd_1473694 : Nat := 756713359647062399147611

theorem tailTrace_1473694 : CollatzResearch.WordTrace tailWord_1473694 prefixEnd_1473694 756713359647062399147611 := by
  unfold tailWord_1473694
  simp only [CollatzResearch.WordTrace]
  refine ⟨6718754490383224967811517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35833357282043866494994757 6718754490383224967811517)
  ·
    refine ⟨2519532933893709362929319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6718754490383224967811517 2519532933893709362929319)
    ·
      refine ⟨3779299400840564044393979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2519532933893709362929319 3779299400840564044393979)
      ·
        refine ⟨5668949101260846066590969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3779299400840564044393979 5668949101260846066590969)
        ·
          refine ⟨4251711825945634549943227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5668949101260846066590969 4251711825945634549943227)
          ·
            refine ⟨6377567738918451824914841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4251711825945634549943227 6377567738918451824914841)
            ·
              refine ⟨4783175804188838868686131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6377567738918451824914841 4783175804188838868686131)
              ·
                refine ⟨7174763706283258303029197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4783175804188838868686131 7174763706283258303029197)
                ·
                  refine ⟨2690536389856221863635949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7174763706283258303029197 2690536389856221863635949)
                  ·
                    refine ⟨1008951146196083198863481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2690536389856221863635949 1008951146196083198863481)
                    ·
                      refine ⟨756713359647062399147611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1008951146196083198863481 756713359647062399147611)
                      ·
                        rfl

theorem cell23_1473694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_1473694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1473694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1473694 prefixEnd_1473694 := by exact prefixLift 1473694
  have htrace : WordTrace (prefixWord ++ tailWord_1473694) baseStart_1473694 baseEnd_1473694 := by
    simpa [prefixWord, tailWord_1473694, baseEnd_1473694] using wordTrace_append hprefix tailTrace_1473694
  have hstable : (prefixWord ++ tailWord_1473694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1473694).length < 2 ^ (prefixWord ++ tailWord_1473694).sum := by decide
  have hdescent : baseEnd_1473694 < baseStart_1473694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1473694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
