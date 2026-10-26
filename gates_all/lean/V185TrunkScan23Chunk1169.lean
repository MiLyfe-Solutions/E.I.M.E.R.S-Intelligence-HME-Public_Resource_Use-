import V185TrunkScan23Chunk1168

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6925637 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_6925637 : Nat := 118140960795 + 6925637 * 2 ^ 59
def prefixEnd_6925637 : Nat := 4983230072969 + 3 ^ 40 * 6925637 * 2
def baseEnd_6925637 : Nat := 3556180619562425147087081

theorem tailTrace_6925637 : CollatzResearch.WordTrace tailWord_6925637 prefixEnd_6925637 3556180619562425147087081 := by
  unfold tailWord_6925637
  simp only [CollatzResearch.WordTrace]
  refine ⟨252598733210607428476823165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168399155473738285651215443 252598733210607428476823165)
  ·
    refine ⟨94724524953977785678808687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252598733210607428476823165 94724524953977785678808687)
    ·
      refine ⟨142086787430966678518213031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94724524953977785678808687 142086787430966678518213031)
      ·
        refine ⟨213130181146450017777319547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142086787430966678518213031 213130181146450017777319547)
        ·
          refine ⟨319695271719675026665979321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213130181146450017777319547 319695271719675026665979321)
          ·
            refine ⟨239771453789756269999484491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319695271719675026665979321 239771453789756269999484491)
            ·
              refine ⟨359657180684634404999226737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239771453789756269999484491 359657180684634404999226737)
              ·
                refine ⟨269742885513475803749420053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359657180684634404999226737 269742885513475803749420053)
                ·
                  refine ⟨12644197758444178300754065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 269742885513475803749420053 12644197758444178300754065)
                  ·
                    refine ⟨9483148318833133725565549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12644197758444178300754065 9483148318833133725565549)
                    ·
                      refine ⟨3556180619562425147087081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9483148318833133725565549 3556180619562425147087081)
                      ·
                        rfl

theorem cell23_6925637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_6925637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925637 prefixEnd_6925637 := by exact prefixLift 6925637
  have htrace : WordTrace (prefixWord ++ tailWord_6925637) baseStart_6925637 baseEnd_6925637 := by
    simpa [prefixWord, tailWord_6925637, baseEnd_6925637] using wordTrace_append hprefix tailTrace_6925637
  have hstable : (prefixWord ++ tailWord_6925637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925637).length < 2 ^ (prefixWord ++ tailWord_6925637).sum := by decide
  have hdescent : baseEnd_6925637 < baseStart_6925637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925687 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 3, 5]
def baseStart_6925687 : Nat := 118140960795 + 6925687 * 2 ^ 59
def prefixEnd_6925687 : Nat := 4983230072969 + 3 ^ 40 * 6925687 * 2
def baseEnd_6925687 : Nat := 1185402097865049983820617

theorem tailTrace_6925687 : CollatzResearch.WordTrace tailWord_6925687 prefixEnd_6925687 1185402097865049983820617 := by
  unfold tailWord_6925687
  simp only [CollatzResearch.WordTrace]
  refine ⟨252600556860426287016143315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168400371240284191344095543 252600556860426287016143315)
  ·
    refine ⟨378900835290639430524214973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252600556860426287016143315 378900835290639430524214973)
    ·
      refine ⟨142087813233989786446580615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378900835290639430524214973 142087813233989786446580615)
      ·
        refine ⟨213131719850984679669870923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142087813233989786446580615 213131719850984679669870923)
        ·
          refine ⟨319697579776477019504806385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213131719850984679669870923 319697579776477019504806385)
          ·
            refine ⟨239773184832357764628604789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319697579776477019504806385 239773184832357764628604789)
            ·
              refine ⟨22478736078033540433931699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239773184832357764628604789 22478736078033540433931699)
              ·
                refine ⟨33718104117050310650897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22478736078033540433931699 33718104117050310650897549)
                ·
                  refine ⟨12644289043893866494086581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33718104117050310650897549 12644289043893866494086581)
                  ·
                    refine ⟨1185402097865049983820617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12644289043893866494086581 1185402097865049983820617)
                    ·
                      rfl

theorem cell23_6925687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_6925687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925687 prefixEnd_6925687 := by exact prefixLift 6925687
  have htrace : WordTrace (prefixWord ++ tailWord_6925687) baseStart_6925687 baseEnd_6925687 := by
    simpa [prefixWord, tailWord_6925687, baseEnd_6925687] using wordTrace_append hprefix tailTrace_6925687
  have hstable : (prefixWord ++ tailWord_6925687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925687).length < 2 ^ (prefixWord ++ tailWord_6925687).sum := by decide
  have hdescent : baseEnd_6925687 < baseStart_6925687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925741 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6925741 : Nat := 118140960795 + 6925741 * 2 ^ 59
def prefixEnd_6925741 : Nat := 4983230072969 + 3 ^ 40 * 6925741 * 2
def baseEnd_6925741 : Nat := 3556234021550492740186603

theorem tailTrace_6925741 : CollatzResearch.WordTrace tailWord_6925741 prefixEnd_6925741 3556234021550492740186603 := by
  unfold tailWord_6925741
  simp only [CollatzResearch.WordTrace]
  refine ⟨252602526402230654238609077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168401684268153769492406051 252602526402230654238609077)
  ·
    refine ⟨23681486850209123834869601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252602526402230654238609077 23681486850209123834869601)
    ·
      refine ⟨17761115137656842876152201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23681486850209123834869601 17761115137656842876152201)
      ·
        refine ⟨13320836353242632157114151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17761115137656842876152201 13320836353242632157114151)
        ·
          refine ⟨19981254529863948235671227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13320836353242632157114151 19981254529863948235671227)
          ·
            refine ⟨29971881794795922353506841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19981254529863948235671227 29971881794795922353506841)
            ·
              refine ⟨22478911346096941765130131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29971881794795922353506841 22478911346096941765130131)
              ·
                refine ⟨33718367019145412647695197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22478911346096941765130131 33718367019145412647695197)
                ·
                  refine ⟨12644387632179529742885699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33718367019145412647695197 12644387632179529742885699)
                  ·
                    refine ⟨18966581448269294614328549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12644387632179529742885699 18966581448269294614328549)
                    ·
                      refine ⟨3556234021550492740186603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18966581448269294614328549 3556234021550492740186603)
                      ·
                        rfl

theorem cell23_6925741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6925741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925741 prefixEnd_6925741 := by exact prefixLift 6925741
  have htrace : WordTrace (prefixWord ++ tailWord_6925741) baseStart_6925741 baseEnd_6925741 := by
    simpa [prefixWord, tailWord_6925741, baseEnd_6925741] using wordTrace_append hprefix tailTrace_6925741
  have hstable : (prefixWord ++ tailWord_6925741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925741).length < 2 ^ (prefixWord ++ tailWord_6925741).sum := by decide
  have hdescent : baseEnd_6925741 < baseStart_6925741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925764 : List Nat := [2, 3, 3, 2, 1, 2, 10]
def baseStart_6925764 : Nat := 118140960795 + 6925764 * 2 ^ 59
def prefixEnd_6925764 : Nat := 4983230072969 + 3 ^ 40 * 6925764 * 2
def baseEnd_6925764 : Nat := 43904269525994396916037

theorem tailTrace_6925764 : CollatzResearch.WordTrace tailWord_6925764 prefixEnd_6925764 43904269525994396916037 := by
  unfold tailWord_6925764
  simp only [CollatzResearch.WordTrace]
  refine ⟨126301682640573664583348173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168402243520764886111130897 126301682640573664583348173)
  ·
    refine ⟨47363130990215124218755565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126301682640573664583348173 47363130990215124218755565)
    ·
      refine ⟨17761174121330671582033337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47363130990215124218755565 17761174121330671582033337)
      ·
        refine ⟨13320880590998003686525003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17761174121330671582033337 13320880590998003686525003)
        ·
          refine ⟨19981320886497005529787505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13320880590998003686525003 19981320886497005529787505)
          ·
            refine ⟨14985990664872754147340629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19981320886497005529787505 14985990664872754147340629)
            ·
              refine ⟨43904269525994396916037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14985990664872754147340629 43904269525994396916037)
              ·
                rfl

theorem cell23_6925764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 10].length) (baseStart_6925764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925764 prefixEnd_6925764 := by exact prefixLift 6925764
  have htrace : WordTrace (prefixWord ++ tailWord_6925764) baseStart_6925764 baseEnd_6925764 := by
    simpa [prefixWord, tailWord_6925764, baseEnd_6925764] using wordTrace_append hprefix tailTrace_6925764
  have hstable : (prefixWord ++ tailWord_6925764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925764).length < 2 ^ (prefixWord ++ tailWord_6925764).sum := by decide
  have hdescent : baseEnd_6925764 < baseStart_6925764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925774 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_6925774 : Nat := 118140960795 + 6925774 * 2 ^ 59
def prefixEnd_6925774 : Nat := 4983230072969 + 3 ^ 40 * 6925774 * 2
def baseEnd_6925774 : Nat := 3556250966412091111073951

theorem tailTrace_6925774 : CollatzResearch.WordTrace tailWord_6925774 prefixEnd_6925774 3556250966412091111073951 := by
  unfold tailWord_6925774
  simp only [CollatzResearch.WordTrace]
  refine ⟨31575466251388887609320047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168402486674074067249706917 31575466251388887609320047)
  ·
    refine ⟨47363199377083331413980071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31575466251388887609320047 47363199377083331413980071)
    ·
      refine ⟨71044799065624997120970107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47363199377083331413980071 71044799065624997120970107)
      ·
        refine ⟨106567198598437495681455161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71044799065624997120970107 106567198598437495681455161)
        ·
          refine ⟨79925398948828121761091371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106567198598437495681455161 79925398948828121761091371)
          ·
            refine ⟨119888098423242182641637057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79925398948828121761091371 119888098423242182641637057)
            ·
              refine ⟨89916073817431636981227793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119888098423242182641637057 89916073817431636981227793)
              ·
                refine ⟨67437055363073727735920845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89916073817431636981227793 67437055363073727735920845)
                ·
                  refine ⟨25288895761152647900970317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67437055363073727735920845 25288895761152647900970317)
                  ·
                    refine ⟨9483335910432242962863869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25288895761152647900970317 9483335910432242962863869)
                    ·
                      refine ⟨3556250966412091111073951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9483335910432242962863869 3556250966412091111073951)
                      ·
                        rfl

theorem cell23_6925774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_6925774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925774 prefixEnd_6925774 := by exact prefixLift 6925774
  have htrace : WordTrace (prefixWord ++ tailWord_6925774) baseStart_6925774 baseEnd_6925774 := by
    simpa [prefixWord, tailWord_6925774, baseEnd_6925774] using wordTrace_append hprefix tailTrace_6925774
  have hstable : (prefixWord ++ tailWord_6925774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925774).length < 2 ^ (prefixWord ++ tailWord_6925774).sum := by decide
  have hdescent : baseEnd_6925774 < baseStart_6925774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925807 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 1, 8]
def baseStart_6925807 : Nat := 118140960795 + 6925807 * 2 ^ 59
def prefixEnd_6925807 : Nat := 4983230072969 + 3 ^ 40 * 6925807 * 2
def baseEnd_6925807 : Nat := 1185422637091229827320433

theorem tailTrace_6925807 : CollatzResearch.WordTrace tailWord_6925807 prefixEnd_6925807 1185422637091229827320433 := by
  unfold tailWord_6925807
  simp only [CollatzResearch.WordTrace]
  refine ⟨252604933619991547510511675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168403289079994365007007783 252604933619991547510511675)
  ·
    refine ⟨378907400429987321265767513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252604933619991547510511675 378907400429987321265767513)
    ·
      refine ⟨284180550322490490949325635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378907400429987321265767513 284180550322490490949325635)
      ·
        refine ⟨426270825483735736423988453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284180550322490490949325635 426270825483735736423988453)
        ·
          refine ⟨79925779778200450579497835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426270825483735736423988453 79925779778200450579497835)
          ·
            refine ⟨119888669667300675869246753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79925779778200450579497835 119888669667300675869246753)
            ·
              refine ⟨89916502250475506901935065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119888669667300675869246753 89916502250475506901935065)
              ·
                refine ⟨67437376687856630176451299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89916502250475506901935065 67437376687856630176451299)
                ·
                  refine ⟨101156065031784945264676949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67437376687856630176451299 101156065031784945264676949)
                  ·
                    refine ⟨1185422637091229827320433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101156065031784945264676949 1185422637091229827320433)
                    ·
                      rfl

theorem cell23_6925807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_6925807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925807 prefixEnd_6925807 := by exact prefixLift 6925807
  have htrace : WordTrace (prefixWord ++ tailWord_6925807) baseStart_6925807 baseEnd_6925807 := by
    simpa [prefixWord, tailWord_6925807, baseEnd_6925807] using wordTrace_append hprefix tailTrace_6925807
  have hstable : (prefixWord ++ tailWord_6925807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925807).length < 2 ^ (prefixWord ++ tailWord_6925807).sum := by decide
  have hdescent : baseEnd_6925807 < baseStart_6925807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925827 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_6925827 : Nat := 118140960795 + 6925827 * 2 ^ 59
def prefixEnd_6925827 : Nat := 4983230072969 + 3 ^ 40 * 6925827 * 2
def baseEnd_6925827 : Nat := 3556278180886779403711207

theorem tailTrace_6925827 : CollatzResearch.WordTrace tailWord_6925827 prefixEnd_6925827 3556278180886779403711207 := by
  unfold tailWord_6925827
  simp only [CollatzResearch.WordTrace]
  refine ⟨252605663079919090926239735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168403775386612727284159823 252605663079919090926239735)
  ·
    refine ⟨378908494619878636389359603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252605663079919090926239735 378908494619878636389359603)
    ·
      refine ⟨568362741929817954584039405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378908494619878636389359603 568362741929817954584039405)
      ·
        refine ⟨213136028223681732969014777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568362741929817954584039405 213136028223681732969014777)
        ·
          refine ⟨159852021167761299726761083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213136028223681732969014777 159852021167761299726761083)
          ·
            refine ⟨239778031751641949590141625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159852021167761299726761083 239778031751641949590141625)
            ·
              refine ⟨179833523813731462192606219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239778031751641949590141625 179833523813731462192606219)
              ·
                refine ⟨269750285720597193288909329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179833523813731462192606219 269750285720597193288909329)
                ·
                  refine ⟨202312714290447894966681997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269750285720597193288909329 202312714290447894966681997)
                  ·
                    refine ⟨75867267858917960612505749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202312714290447894966681997 75867267858917960612505749)
                    ·
                      refine ⟨3556278180886779403711207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75867267858917960612505749 3556278180886779403711207)
                      ·
                        rfl

theorem cell23_6925827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_6925827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925827 prefixEnd_6925827 := by exact prefixLift 6925827
  have htrace : WordTrace (prefixWord ++ tailWord_6925827) baseStart_6925827 baseEnd_6925827 := by
    simpa [prefixWord, tailWord_6925827, baseEnd_6925827] using wordTrace_append hprefix tailTrace_6925827
  have hstable : (prefixWord ++ tailWord_6925827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925827).length < 2 ^ (prefixWord ++ tailWord_6925827).sum := by decide
  have hdescent : baseEnd_6925827 < baseStart_6925827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925904 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4]
def baseStart_6925904 : Nat := 118140960795 + 6925904 * 2 ^ 59
def prefixEnd_6925904 : Nat := 4983230072969 + 3 ^ 40 * 6925904 * 2
def baseEnd_6925904 : Nat := 3556317718897175602448353

theorem tailTrace_6925904 : CollatzResearch.WordTrace tailWord_6925904 prefixEnd_6925904 3556317718897175602448353 := by
  unfold tailWord_6925904
  simp only [CollatzResearch.WordTrace]
  refine ⟨126304235750320066538396383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168405647667093422051195177 126304235750320066538396383)
  ·
    refine ⟨189456353625480099807594575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126304235750320066538396383 189456353625480099807594575)
    ·
      refine ⟨284184530438220149711391863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189456353625480099807594575 284184530438220149711391863)
      ·
        refine ⟨426276795657330224567087795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284184530438220149711391863 426276795657330224567087795)
        ·
          refine ⟨639415193485995336850631693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426276795657330224567087795 639415193485995336850631693)
          ·
            refine ⟨239780697557248251318986885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639415193485995336850631693 239780697557248251318986885)
            ·
              refine ⟨44958880791984047122310041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239780697557248251318986885 44958880791984047122310041)
              ·
                refine ⟨33719160593988035341732531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44958880791984047122310041 33719160593988035341732531)
                ·
                  refine ⟨50578740890982053012598797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33719160593988035341732531 50578740890982053012598797)
                  ·
                    refine ⟨18967027834118269879724549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50578740890982053012598797 18967027834118269879724549)
                    ·
                      refine ⟨3556317718897175602448353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18967027834118269879724549 3556317718897175602448353)
                      ·
                        rfl

theorem cell23_6925904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_6925904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925904 prefixEnd_6925904 := by exact prefixLift 6925904
  have htrace : WordTrace (prefixWord ++ tailWord_6925904) baseStart_6925904 baseEnd_6925904 := by
    simpa [prefixWord, tailWord_6925904, baseEnd_6925904] using wordTrace_append hprefix tailTrace_6925904
  have hstable : (prefixWord ++ tailWord_6925904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925904).length < 2 ^ (prefixWord ++ tailWord_6925904).sum := by decide
  have hdescent : baseEnd_6925904 < baseStart_6925904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925921 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 6, 2]
def baseStart_6925921 : Nat := 118140960795 + 6925921 * 2 ^ 59
def prefixEnd_6925921 : Nat := 4983230072969 + 3 ^ 40 * 6925921 * 2
def baseEnd_6925921 : Nat := 3556326448068302035935775

theorem tailTrace_6925921 : CollatzResearch.WordTrace tailWord_6925921 prefixEnd_6925921 3556326448068302035935775 := by
  unfold tailWord_6925921
  simp only [CollatzResearch.WordTrace]
  refine ⟨252609091541578544980161617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168406061027719029986774411 252609091541578544980161617)
  ·
    refine ⟨189456818656183908735121213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252609091541578544980161617 189456818656183908735121213)
    ·
      refine ⟨71046306996068965775670455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189456818656183908735121213 71046306996068965775670455)
      ·
        refine ⟨106569460494103448663505683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71046306996068965775670455 106569460494103448663505683)
        ·
          refine ⟨159854190741155172995258525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106569460494103448663505683 159854190741155172995258525)
          ·
            refine ⟨59945321527933189873221947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159854190741155172995258525 59945321527933189873221947)
            ·
              refine ⟨89917982291899784809832921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59945321527933189873221947 89917982291899784809832921)
              ·
                refine ⟨67438486718924838607374691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89917982291899784809832921 67438486718924838607374691)
                ·
                  refine ⟨101157730078387257911062037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67438486718924838607374691 101157730078387257911062037)
                  ·
                    refine ⟨4741768597424402714581033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101157730078387257911062037 4741768597424402714581033)
                    ·
                      refine ⟨3556326448068302035935775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4741768597424402714581033 3556326448068302035935775)
                      ·
                        rfl

theorem cell23_6925921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_6925921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925921 prefixEnd_6925921 := by exact prefixLift 6925921
  have htrace : WordTrace (prefixWord ++ tailWord_6925921) baseStart_6925921 baseEnd_6925921 := by
    simpa [prefixWord, tailWord_6925921, baseEnd_6925921] using wordTrace_append hprefix tailTrace_6925921
  have hstable : (prefixWord ++ tailWord_6925921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925921).length < 2 ^ (prefixWord ++ tailWord_6925921).sum := by decide
  have hdescent : baseEnd_6925921 < baseStart_6925921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925938 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_6925938 : Nat := 118140960795 + 6925938 * 2 ^ 59
def prefixEnd_6925938 : Nat := 4983230072969 + 3 ^ 40 * 6925938 * 2
def baseEnd_6925938 : Nat := 3556335177239428469423197

theorem tailTrace_6925938 : CollatzResearch.WordTrace tailWord_6925938 prefixEnd_6925938 3556335177239428469423197 := by
  unfold tailWord_6925938
  simp only [CollatzResearch.WordTrace]
  refine ⟨63152427895629239220882617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168406474388344637922353645 63152427895629239220882617)
  ·
    refine ⟨47364320921721929415661963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63152427895629239220882617 47364320921721929415661963)
    ·
      refine ⟨71046481382582894123492945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47364320921721929415661963 71046481382582894123492945)
      ·
        refine ⟨53284861036937170592619709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71046481382582894123492945 53284861036937170592619709)
        ·
          refine ⟨19981822888851438972232391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53284861036937170592619709 19981822888851438972232391)
          ·
            refine ⟨29972734333277158458348587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19981822888851438972232391 29972734333277158458348587)
            ·
              refine ⟨44959101499915737687522881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29972734333277158458348587 44959101499915737687522881)
              ·
                refine ⟨33719326124936803265642161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44959101499915737687522881 33719326124936803265642161)
                ·
                  refine ⟨25289494593702602449231621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33719326124936803265642161 25289494593702602449231621)
                  ·
                    refine ⟨4741780236319237959230929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25289494593702602449231621 4741780236319237959230929)
                    ·
                      refine ⟨3556335177239428469423197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4741780236319237959230929 3556335177239428469423197)
                      ·
                        rfl

theorem cell23_6925938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_6925938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925938 prefixEnd_6925938 := by exact prefixLift 6925938
  have htrace : WordTrace (prefixWord ++ tailWord_6925938) baseStart_6925938 baseEnd_6925938 := by
    simpa [prefixWord, tailWord_6925938, baseEnd_6925938] using wordTrace_append hprefix tailTrace_6925938
  have hstable : (prefixWord ++ tailWord_6925938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925938).length < 2 ^ (prefixWord ++ tailWord_6925938).sum := by decide
  have hdescent : baseEnd_6925938 < baseStart_6925938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925964 : List Nat := [2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6925964 : Nat := 118140960795 + 6925964 * 2 ^ 59
def prefixEnd_6925964 : Nat := 4983230072969 + 3 ^ 40 * 6925964 * 2
def baseEnd_6925964 : Nat := 3556348527736445367698077

theorem tailTrace_6925964 : CollatzResearch.WordTrace tailWord_6925964 prefixEnd_6925964 3556348527736445367698077 := by
  unfold tailWord_6925964
  simp only [CollatzResearch.WordTrace]
  refine ⟨126305329940211381661988473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168407106586948508882651297 126305329940211381661988473)
  ·
    refine ⟨94728997455158536246491355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126305329940211381661988473 94728997455158536246491355)
    ·
      refine ⟨142093496182737804369737033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94728997455158536246491355 142093496182737804369737033)
      ·
        refine ⟨106570122137053353277302775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142093496182737804369737033 106570122137053353277302775)
        ·
          refine ⟨159855183205580029915954163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106570122137053353277302775 159855183205580029915954163)
          ·
            refine ⟨239782774808370044873931245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159855183205580029915954163 239782774808370044873931245)
            ·
              refine ⟨89918540553138766827724217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239782774808370044873931245 89918540553138766827724217)
              ·
                refine ⟨67438905414854075120793163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89918540553138766827724217 67438905414854075120793163)
                ·
                  refine ⟨101158358122281112681189745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67438905414854075120793163 101158358122281112681189745)
                  ·
                    refine ⟨75868768591710834510892309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101158358122281112681189745 75868768591710834510892309)
                    ·
                      refine ⟨3556348527736445367698077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75868768591710834510892309 3556348527736445367698077)
                      ·
                        rfl

theorem cell23_6925964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6925964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925964 prefixEnd_6925964 := by exact prefixLift 6925964
  have htrace : WordTrace (prefixWord ++ tailWord_6925964) baseStart_6925964 baseEnd_6925964 := by
    simpa [prefixWord, tailWord_6925964, baseEnd_6925964] using wordTrace_append hprefix tailTrace_6925964
  have hstable : (prefixWord ++ tailWord_6925964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925964).length < 2 ^ (prefixWord ++ tailWord_6925964).sum := by decide
  have hdescent : baseEnd_6925964 < baseStart_6925964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6925982 : List Nat := [4, 3, 1, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6925982 : Nat := 118140960795 + 6925982 * 2 ^ 59
def prefixEnd_6925982 : Nat := 4983230072969 + 3 ^ 40 * 6925982 * 2
def baseEnd_6925982 : Nat := 1185452590129408765757665

theorem tailTrace_6925982 : CollatzResearch.WordTrace tailWord_6925982 prefixEnd_6925982 1185452590129408765757665 := by
  unfold tailWord_6925982
  simp only [CollatzResearch.WordTrace]
  refine ⟨31576414549294694049766525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168407544262905034932088133 31576414549294694049766525)
  ·
    refine ⟨11841155455985510268662447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31576414549294694049766525 11841155455985510268662447)
    ·
      refine ⟨17761733183978265402993671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11841155455985510268662447 17761733183978265402993671)
      ·
        refine ⟨26642599775967398104490507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17761733183978265402993671 26642599775967398104490507)
        ·
          refine ⟨39963899663951097156735761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26642599775967398104490507 39963899663951097156735761)
          ·
            refine ⟨29972924747963322867551821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39963899663951097156735761 29972924747963322867551821)
            ·
              refine ⟨11239846780486246075331933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29972924747963322867551821 11239846780486246075331933)
              ·
                refine ⟨4214942542682342278249475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11239846780486246075331933 4214942542682342278249475)
                ·
                  refine ⟨6322413814023513417374213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4214942542682342278249475 6322413814023513417374213)
                  ·
                    refine ⟨1185452590129408765757665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322413814023513417374213 1185452590129408765757665)
                    ·
                      rfl

theorem cell23_6925982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6925982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6925982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6925982 prefixEnd_6925982 := by exact prefixLift 6925982
  have htrace : WordTrace (prefixWord ++ tailWord_6925982) baseStart_6925982 baseEnd_6925982 := by
    simpa [prefixWord, tailWord_6925982, baseEnd_6925982] using wordTrace_append hprefix tailTrace_6925982
  have hstable : (prefixWord ++ tailWord_6925982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6925982).length < 2 ^ (prefixWord ++ tailWord_6925982).sum := by decide
  have hdescent : baseEnd_6925982 < baseStart_6925982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6925982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926041 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 4]
def baseStart_6926041 : Nat := 118140960795 + 6926041 * 2 ^ 59
def prefixEnd_6926041 : Nat := 4983230072969 + 3 ^ 40 * 6926041 * 2
def baseEnd_6926041 : Nat := 3556388065746841566435223

theorem tailTrace_6926041 : CollatzResearch.WordTrace tailWord_6926041 prefixEnd_6926041 3556388065746841566435223 := by
  unfold tailWord_6926041
  simp only [CollatzResearch.WordTrace]
  refine ⟨252613468301143805474529977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168408978867429203649686651 252613468301143805474529977)
  ·
    refine ⟨189460101225857854105897483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252613468301143805474529977 189460101225857854105897483)
    ·
      refine ⟨284190151838786781158846225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189460101225857854105897483 284190151838786781158846225)
      ·
        refine ⟨213142613879090085869134669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284190151838786781158846225 213142613879090085869134669)
        ·
          refine ⟨79928480204658782200925501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213142613879090085869134669 79928480204658782200925501)
          ·
            refine ⟨29973180076747043325347063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79928480204658782200925501 29973180076747043325347063)
            ·
              refine ⟨44959770115120564988020595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29973180076747043325347063 44959770115120564988020595)
              ·
                refine ⟨67439655172680847482030893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44959770115120564988020595 67439655172680847482030893)
                ·
                  refine ⟨25289870689755317805761585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67439655172680847482030893 25289870689755317805761585)
                  ·
                    refine ⟨18967403017316488354321189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25289870689755317805761585 18967403017316488354321189)
                    ·
                      refine ⟨3556388065746841566435223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18967403017316488354321189 3556388065746841566435223)
                      ·
                        rfl

theorem cell23_6926041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_6926041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926041 prefixEnd_6926041 := by exact prefixLift 6926041
  have htrace : WordTrace (prefixWord ++ tailWord_6926041) baseStart_6926041 baseEnd_6926041 := by
    simpa [prefixWord, tailWord_6926041, baseEnd_6926041] using wordTrace_append hprefix tailTrace_6926041
  have hstable : (prefixWord ++ tailWord_6926041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926041).length < 2 ^ (prefixWord ++ tailWord_6926041).sum := by decide
  have hdescent : baseEnd_6926041 < baseStart_6926041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926048 : List Nat := [2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3]
def baseStart_6926048 : Nat := 118140960795 + 6926048 * 2 ^ 59
def prefixEnd_6926048 : Nat := 4983230072969 + 3 ^ 40 * 6926048 * 2
def baseEnd_6926048 : Nat := 3556391660111423039047691

theorem tailTrace_6926048 : CollatzResearch.WordTrace tailWord_6926048 prefixEnd_6926048 3556391660111423039047691 := by
  unfold tailWord_6926048
  simp only [CollatzResearch.WordTrace]
  refine ⟨126306861806059222835017399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168409149074745630446689865 126306861806059222835017399)
  ·
    refine ⟨189460292709088834252526099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126306861806059222835017399 189460292709088834252526099)
    ·
      refine ⟨284190439063633251378789149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189460292709088834252526099 284190439063633251378789149)
      ·
        refine ⟨106571414648862469267045931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284190439063633251378789149 106571414648862469267045931)
        ·
          refine ⟨159857121973293703900568897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106571414648862469267045931 159857121973293703900568897)
          ·
            refine ⟨119892841479970277925426673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159857121973293703900568897 119892841479970277925426673)
            ·
              refine ⟨89919631109977708444070005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119892841479970277925426673 89919631109977708444070005)
              ·
                refine ⟨8429965416560410166631563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89919631109977708444070005 8429965416560410166631563)
                ·
                  refine ⟨12644948124840615249947345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8429965416560410166631563 12644948124840615249947345)
                  ·
                    refine ⟨9483711093630461437460509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12644948124840615249947345 9483711093630461437460509)
                    ·
                      refine ⟨3556391660111423039047691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9483711093630461437460509 3556391660111423039047691)
                      ·
                        rfl

theorem cell23_6926048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_6926048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926048 prefixEnd_6926048 := by exact prefixLift 6926048
  have htrace : WordTrace (prefixWord ++ tailWord_6926048) baseStart_6926048 baseEnd_6926048 := by
    simpa [prefixWord, tailWord_6926048, baseEnd_6926048] using wordTrace_append hprefix tailTrace_6926048
  have hstable : (prefixWord ++ tailWord_6926048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926048).length < 2 ^ (prefixWord ++ tailWord_6926048).sum := by decide
  have hdescent : baseEnd_6926048 < baseStart_6926048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926051 : List Nat := [1, 1, 1, 7, 2, 11]
def baseStart_6926051 : Nat := 118140960795 + 6926051 * 2 ^ 59
def prefixEnd_6926051 : Nat := 4983230072969 + 3 ^ 40 * 6926051 * 2
def baseEnd_6926051 : Nat := 14635362965240273774939

theorem tailTrace_6926051 : CollatzResearch.WordTrace tailWord_6926051 prefixEnd_6926051 14635362965240273774939 := by
  unfold tailWord_6926051
  simp only [CollatzResearch.WordTrace]
  refine ⟨252613833031107577182394007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168409222020738384788262671 252613833031107577182394007)
  ·
    refine ⟨378920749546661365773591011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252613833031107577182394007 378920749546661365773591011)
    ·
      refine ⟨568381124319992048660386517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378920749546661365773591011 568381124319992048660386517)
      ·
        refine ⟨13321432601249813640477809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 568381124319992048660386517 13321432601249813640477809)
        ·
          refine ⟨9991074450937360230358357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13321432601249813640477809 9991074450937360230358357)
          ·
            refine ⟨14635362965240273774939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9991074450937360230358357 14635362965240273774939)
            ·
              rfl

theorem cell23_6926051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 11].length) (baseStart_6926051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926051 prefixEnd_6926051 := by exact prefixLift 6926051
  have htrace : WordTrace (prefixWord ++ tailWord_6926051) baseStart_6926051 baseEnd_6926051 := by
    simpa [prefixWord, tailWord_6926051, baseEnd_6926051] using wordTrace_append hprefix tailTrace_6926051
  have hstable : (prefixWord ++ tailWord_6926051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926051).length < 2 ^ (prefixWord ++ tailWord_6926051).sum := by decide
  have hdescent : baseEnd_6926051 < baseStart_6926051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926093 : List Nat := [1, 7, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6926093 : Nat := 118140960795 + 6926093 * 2 ^ 59
def prefixEnd_6926093 : Nat := 4983230072969 + 3 ^ 40 * 6926093 * 2
def baseEnd_6926093 : Nat := 1185471588913625120994995

theorem tailTrace_6926093 : CollatzResearch.WordTrace tailWord_6926093 prefixEnd_6926093 1185471588913625120994995 := by
  unfold tailWord_6926093
  simp only [CollatzResearch.WordTrace]
  refine ⟨252615364896955418355422933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168410243264636945570281955 252615364896955418355422933)
  ·
    refine ⟨5920672614772392617705225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 252615364896955418355422933 5920672614772392617705225)
    ·
      refine ⟨4440504461079294463278919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5920672614772392617705225 4440504461079294463278919)
      ·
        refine ⟨6660756691618941694918379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440504461079294463278919 6660756691618941694918379)
        ·
          refine ⟨9991135037428412542377569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660756691618941694918379 9991135037428412542377569)
          ·
            refine ⟨7493351278071309406783177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9991135037428412542377569 7493351278071309406783177)
            ·
              refine ⟨5620013458553482055087383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7493351278071309406783177 5620013458553482055087383)
              ·
                refine ⟨8430020187830223082631075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620013458553482055087383 8430020187830223082631075)
                ·
                  refine ⟨12645030281745334623946613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8430020187830223082631075 12645030281745334623946613)
                  ·
                    refine ⟨1185471588913625120994995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12645030281745334623946613 1185471588913625120994995)
                    ·
                      rfl

theorem cell23_6926093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6926093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926093 prefixEnd_6926093 := by exact prefixLift 6926093
  have htrace : WordTrace (prefixWord ++ tailWord_6926093) baseStart_6926093 baseEnd_6926093 := by
    simpa [prefixWord, tailWord_6926093, baseEnd_6926093] using wordTrace_append hprefix tailTrace_6926093
  have hstable : (prefixWord ++ tailWord_6926093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926093).length < 2 ^ (prefixWord ++ tailWord_6926093).sum := by decide
  have hdescent : baseEnd_6926093 < baseStart_6926093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926111 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 4, 6]
def baseStart_6926111 : Nat := 118140960795 + 6926111 * 2 ^ 59
def prefixEnd_6926111 : Nat := 4983230072969 + 3 ^ 40 * 6926111 * 2
def baseEnd_6926111 : Nat := 1185474669797552097519967

theorem tailTrace_6926111 : CollatzResearch.WordTrace tailWord_6926111 prefixEnd_6926111 1185474669797552097519967 := by
  unfold tailWord_6926111
  simp only [CollatzResearch.WordTrace]
  refine ⟨252616021410890207429578187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168410680940593471619718791 252616021410890207429578187)
  ·
    refine ⟨378924032116335311144367281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252616021410890207429578187 378924032116335311144367281)
    ·
      refine ⟨284193024087251483358275461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378924032116335311144367281 284193024087251483358275461)
      ·
        refine ⟨53286192016359653129676649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284193024087251483358275461 53286192016359653129676649)
        ·
          refine ⟨39964644012269739847257487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53286192016359653129676649 39964644012269739847257487)
          ·
            refine ⟨59946966018404609770886231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39964644012269739847257487 59946966018404609770886231)
            ·
              refine ⟨89920449027606914656329347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59946966018404609770886231 89920449027606914656329347)
              ·
                refine ⟨134880673541410371984494021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89920449027606914656329347 134880673541410371984494021)
                ·
                  refine ⟨25290126289014444747092629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134880673541410371984494021 25290126289014444747092629)
                  ·
                    refine ⟨1185474669797552097519967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25290126289014444747092629 1185474669797552097519967)
                    ·
                      rfl

theorem cell23_6926111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_6926111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926111 prefixEnd_6926111 := by exact prefixLift 6926111
  have htrace : WordTrace (prefixWord ++ tailWord_6926111) baseStart_6926111 baseEnd_6926111 := by
    simpa [prefixWord, tailWord_6926111, baseEnd_6926111] using wordTrace_append hprefix tailTrace_6926111
  have hstable : (prefixWord ++ tailWord_6926111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926111).length < 2 ^ (prefixWord ++ tailWord_6926111).sum := by decide
  have hdescent : baseEnd_6926111 < baseStart_6926111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926186 : List Nat := [3, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6926186 : Nat := 118140960795 + 6926186 * 2 ^ 59
def prefixEnd_6926186 : Nat := 4983230072969 + 3 ^ 40 * 6926186 * 2
def baseEnd_6926186 : Nat := 3556462520441743499122057

theorem tailTrace_6926186 : CollatzResearch.WordTrace tailWord_6926186 prefixEnd_6926186 3556462520441743499122057 := by
  unfold tailWord_6926186
  simp only [CollatzResearch.WordTrace]
  refine ⟨63154689221404623809639603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168412504590412330159038941 63154689221404623809639603)
  ·
    refine ⟨94732033832106935714459405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63154689221404623809639603 94732033832106935714459405)
    ·
      refine ⟨35524512687040100892922277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94732033832106935714459405 35524512687040100892922277)
      ·
        refine ⟨6660846128820018917422927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35524512687040100892922277 6660846128820018917422927)
        ·
          refine ⟨9991269193230028376134391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6660846128820018917422927 9991269193230028376134391)
          ·
            refine ⟨14986903789845042564201587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9991269193230028376134391 14986903789845042564201587)
            ·
              refine ⟨22480355684767563846302381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14986903789845042564201587 22480355684767563846302381)
              ·
                refine ⟨8430133381787836442363393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22480355684767563846302381 8430133381787836442363393)
                ·
                  refine ⟨6322600036340877331772545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8430133381787836442363393 6322600036340877331772545)
                  ·
                    refine ⟨4741950027255657998829409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6322600036340877331772545 4741950027255657998829409)
                    ·
                      refine ⟨3556462520441743499122057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4741950027255657998829409 3556462520441743499122057)
                      ·
                        rfl

theorem cell23_6926186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6926186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926186 prefixEnd_6926186 := by exact prefixLift 6926186
  have htrace : WordTrace (prefixWord ++ tailWord_6926186) baseStart_6926186 baseEnd_6926186 := by
    simpa [prefixWord, tailWord_6926186, baseEnd_6926186] using wordTrace_append hprefix tailTrace_6926186
  have hstable : (prefixWord ++ tailWord_6926186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926186).length < 2 ^ (prefixWord ++ tailWord_6926186).sum := by decide
  have hdescent : baseEnd_6926186 < baseStart_6926186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926269 : List Nat := [1, 4, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_6926269 : Nat := 118140960795 + 6926269 * 2 ^ 59
def prefixEnd_6926269 : Nat := 4983230072969 + 3 ^ 40 * 6926269 * 2
def baseEnd_6926269 : Nat := 1185501713112022224794725

theorem tailTrace_6926269 : CollatzResearch.WordTrace tailWord_6926269 prefixEnd_6926269 1185501713112022224794725 := by
  unfold tailWord_6926269
  simp only [CollatzResearch.WordTrace]
  refine ⟨252621784144317800413829861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168414522762878533609219907 252621784144317800413829861)
  ·
    refine ⟨47366584527059587577593099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252621784144317800413829861 47366584527059587577593099)
    ·
      refine ⟨71049876790589381366389649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47366584527059587577593099 71049876790589381366389649)
      ·
        refine ⟨53287407592942036024792237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71049876790589381366389649 53287407592942036024792237)
        ·
          refine ⟨19982777847353263509297089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53287407592942036024792237 19982777847353263509297089)
          ·
            refine ⟨14987083385514947631972817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19982777847353263509297089 14987083385514947631972817)
            ·
              refine ⟨11240312539136210723979613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14987083385514947631972817 11240312539136210723979613)
              ·
                refine ⟨4215117202176079021492355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11240312539136210723979613 4215117202176079021492355)
                ·
                  refine ⟨6322675803264118532238533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215117202176079021492355 6322675803264118532238533)
                  ·
                    refine ⟨1185501713112022224794725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322675803264118532238533 1185501713112022224794725)
                    ·
                      rfl

theorem cell23_6926269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_6926269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926269 prefixEnd_6926269 := by exact prefixLift 6926269
  have htrace : WordTrace (prefixWord ++ tailWord_6926269) baseStart_6926269 baseEnd_6926269 := by
    simpa [prefixWord, tailWord_6926269, baseEnd_6926269] using wordTrace_append hprefix tailTrace_6926269
  have hstable : (prefixWord ++ tailWord_6926269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926269).length < 2 ^ (prefixWord ++ tailWord_6926269).sum := by decide
  have hdescent : baseEnd_6926269 < baseStart_6926269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926359 : List Nat := [1, 1, 3, 5, 2, 1, 1, 3, 2, 4]
def baseStart_6926359 : Nat := 118140960795 + 6926359 * 2 ^ 59
def prefixEnd_6926359 : Nat := 4983230072969 + 3 ^ 40 * 6926359 * 2
def baseEnd_6926359 : Nat := 1185517117531657107419587

theorem tailTrace_6926359 : CollatzResearch.WordTrace tailWord_6926359 prefixEnd_6926359 1185517117531657107419587 := by
  unfold tailWord_6926359
  simp only [CollatzResearch.WordTrace]
  refine ⟨252625066713991745784606131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168416711142661163856404087 252625066713991745784606131)
  ·
    refine ⟨378937600070987618676909197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252625066713991745784606131 378937600070987618676909197)
    ·
      refine ⟨142101600026620357003840949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378937600070987618676909197 142101600026620357003840949)
      ·
        refine ⟨13322025002495658469110089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142101600026620357003840949 13322025002495658469110089)
        ·
          refine ⟨9991518751871743851832567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13322025002495658469110089 9991518751871743851832567)
          ·
            refine ⟨14987278127807615777748851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9991518751871743851832567 14987278127807615777748851)
            ·
              refine ⟨22480917191711423666623277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14987278127807615777748851 22480917191711423666623277)
              ·
                refine ⟨8430343946891783874983729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22480917191711423666623277 8430343946891783874983729)
                ·
                  refine ⟨6322757960168837906237797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8430343946891783874983729 6322757960168837906237797)
                  ·
                    refine ⟨1185517117531657107419587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322757960168837906237797 1185517117531657107419587)
                    ·
                      rfl

theorem cell23_6926359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 4].length) (baseStart_6926359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926359 prefixEnd_6926359 := by exact prefixLift 6926359
  have htrace : WordTrace (prefixWord ++ tailWord_6926359) baseStart_6926359 baseEnd_6926359 := by
    simpa [prefixWord, tailWord_6926359, baseEnd_6926359] using wordTrace_append hprefix tailTrace_6926359
  have hstable : (prefixWord ++ tailWord_6926359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926359).length < 2 ^ (prefixWord ++ tailWord_6926359).sum := by decide
  have hdescent : baseEnd_6926359 < baseStart_6926359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926382 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_6926382 : Nat := 118140960795 + 6926382 * 2 ^ 59
def prefixEnd_6926382 : Nat := 4983230072969 + 3 ^ 40 * 6926382 * 2
def baseEnd_6926382 : Nat := 3556563162650024732271155

theorem tailTrace_6926382 : CollatzResearch.WordTrace tailWord_6926382 prefixEnd_6926382 3556563162650024732271155 := by
  unfold tailWord_6926382
  simp only [CollatzResearch.WordTrace]
  refine ⟨31578238199113552589086675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168417270395272280475128933 31578238199113552589086675)
  ·
    refine ⟨47367357298670328883630013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31578238199113552589086675 47367357298670328883630013)
    ·
      refine ⟨17762758987001373331361255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47367357298670328883630013 17762758987001373331361255)
      ·
        refine ⟨26644138480502059997041883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17762758987001373331361255 26644138480502059997041883)
        ·
          refine ⟨39966207720753089995562825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26644138480502059997041883 39966207720753089995562825)
          ·
            refine ⟨29974655790564817496672119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39966207720753089995562825 29974655790564817496672119)
            ·
              refine ⟨44961983685847226245008179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29974655790564817496672119 44961983685847226245008179)
              ·
                refine ⟨67442975528770839367512269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44961983685847226245008179 67442975528770839367512269)
                ·
                  refine ⟨25291115823289064762817101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67442975528770839367512269 25291115823289064762817101)
                  ·
                    refine ⟨9484168433733399286056413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25291115823289064762817101 9484168433733399286056413)
                    ·
                      refine ⟨3556563162650024732271155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9484168433733399286056413 3556563162650024732271155)
                      ·
                        rfl

theorem cell23_6926382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_6926382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926382 prefixEnd_6926382 := by exact prefixLift 6926382
  have htrace : WordTrace (prefixWord ++ tailWord_6926382) baseStart_6926382 baseEnd_6926382 := by
    simpa [prefixWord, tailWord_6926382, baseEnd_6926382] using wordTrace_append hprefix tailTrace_6926382
  have hstable : (prefixWord ++ tailWord_6926382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926382).length < 2 ^ (prefixWord ++ tailWord_6926382).sum := by decide
  have hdescent : baseEnd_6926382 < baseStart_6926382 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926425 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 3]
def baseStart_6926425 : Nat := 118140960795 + 6926425 * 2 ^ 59
def prefixEnd_6926425 : Nat := 4983230072969 + 3 ^ 40 * 6926425 * 2
def baseEnd_6926425 : Nat := 3556585242318168064033457

theorem tailTrace_6926425 : CollatzResearch.WordTrace tailWord_6926425 prefixEnd_6926425 3556585242318168064033457 := by
  unfold tailWord_6926425
  simp only [CollatzResearch.WordTrace]
  refine ⟨252627473931752639056508729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168418315954501759371005819 252627473931752639056508729)
  ·
    refine ⟨189470605448814479292381547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252627473931752639056508729 189470605448814479292381547)
    ·
      refine ⟨284205908173221718938572321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189470605448814479292381547 284205908173221718938572321)
      ·
        refine ⟨213154431129916289203929241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284205908173221718938572321 213154431129916289203929241)
        ·
          refine ⟨159865823347437216902946931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213154431129916289203929241 159865823347437216902946931)
          ·
            refine ⟨239798735021155825354420397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159865823347437216902946931 239798735021155825354420397)
            ·
              refine ⟨89924525632933434507907649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239798735021155825354420397 89924525632933434507907649)
              ·
                refine ⟨67443394224700075880930737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89924525632933434507907649 67443394224700075880930737)
                ·
                  refine ⟨50582545668525056910698053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67443394224700075880930737 50582545668525056910698053)
                  ·
                    refine ⟨9484227312848448170755885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50582545668525056910698053 9484227312848448170755885)
                    ·
                      refine ⟨3556585242318168064033457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9484227312848448170755885 3556585242318168064033457)
                      ·
                        rfl

theorem cell23_6926425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_6926425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926425 prefixEnd_6926425 := by exact prefixLift 6926425
  have htrace : WordTrace (prefixWord ++ tailWord_6926425) baseStart_6926425 baseEnd_6926425 := by
    simpa [prefixWord, tailWord_6926425, baseEnd_6926425] using wordTrace_append hprefix tailTrace_6926425
  have hstable : (prefixWord ++ tailWord_6926425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926425).length < 2 ^ (prefixWord ++ tailWord_6926425).sum := by decide
  have hdescent : baseEnd_6926425 < baseStart_6926425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926439 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 4, 2, 2]
def baseStart_6926439 : Nat := 118140960795 + 6926439 * 2 ^ 59
def prefixEnd_6926439 : Nat := 4983230072969 + 3 ^ 40 * 6926439 * 2
def baseEnd_6926439 : Nat := 3556592431047331009258393

theorem tailTrace_6926439 : CollatzResearch.WordTrace tailWord_6926439 prefixEnd_6926439 3556592431047331009258393 := by
  unfold tailWord_6926439
  simp only [CollatzResearch.WordTrace]
  refine ⟨252627984553701919447518371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168418656369134612965012247 252627984553701919447518371)
  ·
    refine ⟨378941976830552879171277557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252627984553701919447518371 378941976830552879171277557)
    ·
      refine ⟨35525810327864332422307271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 378941976830552879171277557 35525810327864332422307271)
      ·
        refine ⟨53288715491796498633460907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35525810327864332422307271 53288715491796498633460907)
        ·
          refine ⟨79933073237694747950191361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53288715491796498633460907 79933073237694747950191361)
          ·
            refine ⟨59949804928271060962643521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79933073237694747950191361 59949804928271060962643521)
            ·
              refine ⟨44962353696203295721982641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59949804928271060962643521 44962353696203295721982641)
              ·
                refine ⟨33721765272152471791486981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44962353696203295721982641 33721765272152471791486981)
                ·
                  refine ⟨6322830988528588460903809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33721765272152471791486981 6322830988528588460903809)
                  ·
                    refine ⟨4742123241396441345677857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6322830988528588460903809 4742123241396441345677857)
                    ·
                      refine ⟨3556592431047331009258393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742123241396441345677857 3556592431047331009258393)
                      ·
                        rfl

theorem cell23_6926439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_6926439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926439 prefixEnd_6926439 := by exact prefixLift 6926439
  have htrace : WordTrace (prefixWord ++ tailWord_6926439) baseStart_6926439 baseEnd_6926439 := by
    simpa [prefixWord, tailWord_6926439, baseEnd_6926439] using wordTrace_append hprefix tailTrace_6926439
  have hstable : (prefixWord ++ tailWord_6926439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926439).length < 2 ^ (prefixWord ++ tailWord_6926439).sum := by decide
  have hdescent : baseEnd_6926439 < baseStart_6926439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926445 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 9]
def baseStart_6926445 : Nat := 118140960795 + 6926445 * 2 ^ 59
def prefixEnd_6926445 : Nat := 4983230072969 + 3 ^ 40 * 6926445 * 2
def baseEnd_6926445 : Nat := 395177279103473109531485

theorem tailTrace_6926445 : CollatzResearch.WordTrace tailWord_6926445 prefixEnd_6926445 395177279103473109531485 := by
  unfold tailWord_6926445
  simp only [CollatzResearch.WordTrace]
  refine ⟨252628203391680182472236789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168418802261120121648157859 252628203391680182472236789)
  ·
    refine ⟨23683894067970017106772199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252628203391680182472236789 23683894067970017106772199)
    ·
      refine ⟨35525841101955025660158299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23683894067970017106772199 35525841101955025660158299)
      ·
        refine ⟨53288761652932538490237449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35525841101955025660158299 53288761652932538490237449)
        ·
          refine ⟨39966571239699403867678087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53288761652932538490237449 39966571239699403867678087)
          ·
            refine ⟨59949856859549105801517131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39966571239699403867678087 59949856859549105801517131)
            ·
              refine ⟨89924785289323658702275697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59949856859549105801517131 89924785289323658702275697)
              ·
                refine ⟨67443588966992744026706773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89924785289323658702275697 67443588966992744026706773)
                ·
                  refine ⟨395177279103473109531485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67443588966992744026706773 395177279103473109531485)
                  ·
                    rfl

theorem cell23_6926445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 9].length) (baseStart_6926445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926445 prefixEnd_6926445 := by exact prefixLift 6926445
  have htrace : WordTrace (prefixWord ++ tailWord_6926445) baseStart_6926445 baseEnd_6926445 := by
    simpa [prefixWord, tailWord_6926445, baseEnd_6926445] using wordTrace_append hprefix tailTrace_6926445
  have hstable : (prefixWord ++ tailWord_6926445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926445).length < 2 ^ (prefixWord ++ tailWord_6926445).sum := by decide
  have hdescent : baseEnd_6926445 < baseStart_6926445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926492 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6926492 : Nat := 118140960795 + 6926492 * 2 ^ 59
def prefixEnd_6926492 : Nat := 4983230072969 + 3 ^ 40 * 6926492 * 2
def baseEnd_6926492 : Nat := 1185539881840673100631883

theorem tailTrace_6926492 : CollatzResearch.WordTrace tailWord_6926492 prefixEnd_6926492 1185539881840673100631883 := by
  unfold tailWord_6926492
  simp only [CollatzResearch.WordTrace]
  refine ⟨126314958811254954749598865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168419945081673272999465153 126314958811254954749598865)
  ·
    refine ⟨94736219108441216062199149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126314958811254954749598865 94736219108441216062199149)
    ·
      refine ⟨35526082165665456023324681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94736219108441216062199149 35526082165665456023324681)
      ·
        refine ⟨26644561624249092017493511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35526082165665456023324681 26644561624249092017493511)
        ·
          refine ⟨39966842436373638026240267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26644561624249092017493511 39966842436373638026240267)
          ·
            refine ⟨59950263654560457039360401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39966842436373638026240267 59950263654560457039360401)
            ·
              refine ⟨44962697740920342779520301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59950263654560457039360401 44962697740920342779520301)
              ·
                refine ⟨16861011652845128542320113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44962697740920342779520301 16861011652845128542320113)
                ·
                  refine ⟨12645758739633846406740085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16861011652845128542320113 12645758739633846406740085)
                  ·
                    refine ⟨1185539881840673100631883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12645758739633846406740085 1185539881840673100631883)
                    ·
                      rfl

theorem cell23_6926492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6926492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926492 prefixEnd_6926492 := by exact prefixLift 6926492
  have htrace : WordTrace (prefixWord ++ tailWord_6926492) baseStart_6926492 baseEnd_6926492 := by
    simpa [prefixWord, tailWord_6926492, baseEnd_6926492] using wordTrace_append hprefix tailTrace_6926492
  have hstable : (prefixWord ++ tailWord_6926492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926492).length < 2 ^ (prefixWord ++ tailWord_6926492).sum := by decide
  have hdescent : baseEnd_6926492 < baseStart_6926492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926509 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_6926509 : Nat := 118140960795 + 6926509 * 2 ^ 59
def prefixEnd_6926509 : Nat := 4983230072969 + 3 ^ 40 * 6926509 * 2
def baseEnd_6926509 : Nat := 1185542791564381911794357

theorem tailTrace_6926509 : CollatzResearch.WordTrace tailWord_6926509 prefixEnd_6926509 1185542791564381911794357 := by
  unfold tailWord_6926509
  simp only [CollatzResearch.WordTrace]
  refine ⟨252630537663448321402566581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168420358442298880935044387 252630537663448321402566581)
  ·
    refine ⟨23684112905948280131490617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252630537663448321402566581 23684112905948280131490617)
    ·
      refine ⟨17763084679461210098617963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23684112905948280131490617 17763084679461210098617963)
      ·
        refine ⟨26644627019191815147926945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17763084679461210098617963 26644627019191815147926945)
        ·
          refine ⟨19983470264393861360945209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26644627019191815147926945 19983470264393861360945209)
          ·
            refine ⟨14987602698295396020708907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19983470264393861360945209 14987602698295396020708907)
            ·
              refine ⟨22481404047443094031063361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14987602698295396020708907 22481404047443094031063361)
              ·
                refine ⟨16861053035582320523297521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22481404047443094031063361 16861053035582320523297521)
                ·
                  refine ⟨12645789776686740392473141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16861053035582320523297521 12645789776686740392473141)
                  ·
                    refine ⟨1185542791564381911794357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12645789776686740392473141 1185542791564381911794357)
                    ·
                      rfl

theorem cell23_6926509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_6926509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926509 prefixEnd_6926509 := by exact prefixLift 6926509
  have htrace : WordTrace (prefixWord ++ tailWord_6926509) baseStart_6926509 baseEnd_6926509 := by
    simpa [prefixWord, tailWord_6926509, baseEnd_6926509] using wordTrace_append hprefix tailTrace_6926509
  have hstable : (prefixWord ++ tailWord_6926509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926509).length < 2 ^ (prefixWord ++ tailWord_6926509).sum := by decide
  have hdescent : baseEnd_6926509 < baseStart_6926509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926573 : List Nat := [1, 5, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_6926573 : Nat := 118140960795 + 6926573 * 2 ^ 59
def prefixEnd_6926573 : Nat := 4983230072969 + 3 ^ 40 * 6926573 * 2
def baseEnd_6926573 : Nat := 1185553745818344494994259

theorem tailTrace_6926573 : CollatzResearch.WordTrace tailWord_6926573 prefixEnd_6926573 1185553745818344494994259 := by
  unfold tailWord_6926573
  simp only [CollatzResearch.WordTrace]
  refine ⟨252632871935216460332896373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168421914623477640221930915 252632871935216460332896373)
  ·
    refine ⟨23684331743926543156209035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252632871935216460332896373 23684331743926543156209035)
    ·
      refine ⟨35526497615889814734313553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23684331743926543156209035 35526497615889814734313553)
      ·
        refine ⟨26644873211917361050735165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35526497615889814734313553 26644873211917361050735165)
        ·
          refine ⟨9991827454469010394025687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26644873211917361050735165 9991827454469010394025687)
          ·
            refine ⟨14987741181703515591038531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9991827454469010394025687 14987741181703515591038531)
            ·
              refine ⟨22481611772555273386557797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14987741181703515591038531 22481611772555273386557797)
              ·
                refine ⟨4215302207354113759979587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22481611772555273386557797 4215302207354113759979587)
                ·
                  refine ⟨6322953311031170639969381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215302207354113759979587 6322953311031170639969381)
                  ·
                    refine ⟨1185553745818344494994259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6322953311031170639969381 1185553745818344494994259)
                    ·
                      rfl

theorem cell23_6926573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_6926573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926573 prefixEnd_6926573 := by exact prefixLift 6926573
  have htrace : WordTrace (prefixWord ++ tailWord_6926573) baseStart_6926573 baseEnd_6926573 := by
    simpa [prefixWord, tailWord_6926573, baseEnd_6926573] using wordTrace_append hprefix tailTrace_6926573
  have hstable : (prefixWord ++ tailWord_6926573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926573).length < 2 ^ (prefixWord ++ tailWord_6926573).sum := by decide
  have hdescent : baseEnd_6926573 < baseStart_6926573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926579 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 3]
def baseStart_6926579 : Nat := 118140960795 + 6926579 * 2 ^ 59
def prefixEnd_6926579 : Nat := 4983230072969 + 3 ^ 40 * 6926579 * 2
def baseEnd_6926579 : Nat := 3556664318338960461507749

theorem tailTrace_6926579 : CollatzResearch.WordTrace tailWord_6926579 prefixEnd_6926579 3556664318338960461507749 := by
  unfold tailWord_6926579
  simp only [CollatzResearch.WordTrace]
  refine ⟨252633090773194723357614791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168422060515463148905076527 252633090773194723357614791)
  ·
    refine ⟨378949636159792085036422187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252633090773194723357614791 378949636159792085036422187)
    ·
      refine ⟨568424454239688127554633281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378949636159792085036422187 568424454239688127554633281)
      ·
        refine ⟨426318340679766095665974961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568424454239688127554633281 426318340679766095665974961)
        ·
          refine ⟨319738755509824571749481221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426318340679766095665974961 319738755509824571749481221)
          ·
            refine ⟨59951016658092107203027729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319738755509824571749481221 59951016658092107203027729)
            ·
              refine ⟨44963262493569080402270797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59951016658092107203027729 44963262493569080402270797)
              ·
                refine ⟨16861223435088405150851549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44963262493569080402270797 16861223435088405150851549)
                ·
                  refine ⟨6322958788158151931569331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16861223435088405150851549 6322958788158151931569331)
                  ·
                    refine ⟨9484438182237227897353997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6322958788158151931569331 9484438182237227897353997)
                    ·
                      refine ⟨3556664318338960461507749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9484438182237227897353997 3556664318338960461507749)
                      ·
                        rfl

theorem cell23_6926579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 3].length) (baseStart_6926579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926579 prefixEnd_6926579 := by exact prefixLift 6926579
  have htrace : WordTrace (prefixWord ++ tailWord_6926579) baseStart_6926579 baseEnd_6926579 := by
    simpa [prefixWord, tailWord_6926579, baseEnd_6926579] using wordTrace_append hprefix tailTrace_6926579
  have hstable : (prefixWord ++ tailWord_6926579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926579).length < 2 ^ (prefixWord ++ tailWord_6926579).sum := by decide
  have hdescent : baseEnd_6926579 < baseStart_6926579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926589 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_6926589 : Nat := 118140960795 + 6926589 * 2 ^ 59
def prefixEnd_6926589 : Nat := 4983230072969 + 3 ^ 40 * 6926589 * 2
def baseEnd_6926589 : Nat := 3556669453145505422382703

theorem tailTrace_6926589 : CollatzResearch.WordTrace tailWord_6926589 prefixEnd_6926589 3556669453145505422382703 := by
  unfold tailWord_6926589
  simp only [CollatzResearch.WordTrace]
  refine ⟨252633455503158495065478821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168422303668772330043652547 252633455503158495065478821)
  ·
    refine ⟨47368772906842217824777279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252633455503158495065478821 47368772906842217824777279)
    ·
      refine ⟨71053159360263326737165919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47368772906842217824777279 71053159360263326737165919)
      ·
        refine ⟨106579739040394990105748879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71053159360263326737165919 106579739040394990105748879)
        ·
          refine ⟨159869608560592485158623319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106579739040394990105748879 159869608560592485158623319)
          ·
            refine ⟨239804412840888727737934979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159869608560592485158623319 239804412840888727737934979)
            ·
              refine ⟨359706619261333091606902469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239804412840888727737934979 359706619261333091606902469)
              ·
                refine ⟨67444991111499954676294213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359706619261333091606902469 67444991111499954676294213)
                ·
                  refine ⟨12645935833406241501805165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67444991111499954676294213 12645935833406241501805165)
                  ·
                    refine ⟨4742225937527340563176937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12645935833406241501805165 4742225937527340563176937)
                    ·
                      refine ⟨3556669453145505422382703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742225937527340563176937 3556669453145505422382703)
                      ·
                        rfl

theorem cell23_6926589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_6926589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926589 prefixEnd_6926589 := by exact prefixLift 6926589
  have htrace : WordTrace (prefixWord ++ tailWord_6926589) baseStart_6926589 baseEnd_6926589 := by
    simpa [prefixWord, tailWord_6926589, baseEnd_6926589] using wordTrace_append hprefix tailTrace_6926589
  have hstable : (prefixWord ++ tailWord_6926589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926589).length < 2 ^ (prefixWord ++ tailWord_6926589).sum := by decide
  have hdescent : baseEnd_6926589 < baseStart_6926589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926636 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 3, 2, 2]
def baseStart_6926636 : Nat := 118140960795 + 6926636 * 2 ^ 59
def prefixEnd_6926636 : Nat := 4983230072969 + 3 ^ 40 * 6926636 * 2
def baseEnd_6926636 : Nat := 3556693586736266738494987

theorem tailTrace_6926636 : CollatzResearch.WordTrace tailWord_6926636 prefixEnd_6926636 3556693586736266738494987 := by
  unfold tailWord_6926636
  simp only [CollatzResearch.WordTrace]
  refine ⟨126317584866994111046219881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168423446489325481394959841 126317584866994111046219881)
  ·
    refine ⟨94738188650245583284664911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126317584866994111046219881 94738188650245583284664911)
    ·
      refine ⟨142107282975368374926997367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94738188650245583284664911 142107282975368374926997367)
      ·
        refine ⟨213160924463052562390496051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142107282975368374926997367 213160924463052562390496051)
        ·
          refine ⟨319741386694578843585744077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213160924463052562390496051 319741386694578843585744077)
          ·
            refine ⟨119903020010467066344654029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319741386694578843585744077 119903020010467066344654029)
            ·
              refine ⟨44963632503925149879245261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119903020010467066344654029 44963632503925149879245261)
              ·
                refine ⟨16861362188971931204716973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44963632503925149879245261 16861362188971931204716973)
                ·
                  refine ⟨6323010820864474201768865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16861362188971931204716973 6323010820864474201768865)
                  ·
                    refine ⟨4742258115648355651326649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323010820864474201768865 4742258115648355651326649)
                    ·
                      refine ⟨3556693586736266738494987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742258115648355651326649 3556693586736266738494987)
                      ·
                        rfl

theorem cell23_6926636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 3, 2, 2].length) (baseStart_6926636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926636 prefixEnd_6926636 := by exact prefixLift 6926636
  have htrace : WordTrace (prefixWord ++ tailWord_6926636) baseStart_6926636 baseEnd_6926636 := by
    simpa [prefixWord, tailWord_6926636, baseEnd_6926636] using wordTrace_append hprefix tailTrace_6926636
  have hstable : (prefixWord ++ tailWord_6926636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926636).length < 2 ^ (prefixWord ++ tailWord_6926636).sum := by decide
  have hdescent : baseEnd_6926636 < baseStart_6926636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926649 : List Nat := [1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6926649 : Nat := 118140960795 + 6926649 * 2 ^ 59
def prefixEnd_6926649 : Nat := 4983230072969 + 3 ^ 40 * 6926649 * 2
def baseEnd_6926649 : Nat := 3556700261984775187632427

theorem tailTrace_6926649 : CollatzResearch.WordTrace tailWord_6926649 prefixEnd_6926649 3556700261984775187632427 := by
  unfold tailWord_6926649
  simp only [CollatzResearch.WordTrace]
  refine ⟨252635643882941125312663001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168423762588627416875108667 252635643882941125312663001)
  ·
    refine ⟨189476732912205843984497251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252635643882941125312663001 189476732912205843984497251)
    ·
      refine ⟨284215099368308765976745877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189476732912205843984497251 284215099368308765976745877)
      ·
        refine ⟨13322582782889473405159963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 284215099368308765976745877 13322582782889473405159963)
        ·
          refine ⟨19983874174334210107739945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13322582782889473405159963 19983874174334210107739945)
          ·
            refine ⟨14987905630750657580804959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19983874174334210107739945 14987905630750657580804959)
            ·
              refine ⟨22481858446125986371207439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14987905630750657580804959 22481858446125986371207439)
              ·
                refine ⟨33722787669188979556811159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22481858446125986371207439 33722787669188979556811159)
                ·
                  refine ⟨50584181503783469335216739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33722787669188979556811159 50584181503783469335216739)
                  ·
                    refine ⟨75876272255675204002825109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50584181503783469335216739 75876272255675204002825109)
                    ·
                      refine ⟨3556700261984775187632427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75876272255675204002825109 3556700261984775187632427)
                      ·
                        rfl

theorem cell23_6926649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6926649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926649 prefixEnd_6926649 := by exact prefixLift 6926649
  have htrace : WordTrace (prefixWord ++ tailWord_6926649) baseStart_6926649 baseEnd_6926649 := by
    simpa [prefixWord, tailWord_6926649, baseEnd_6926649] using wordTrace_append hprefix tailTrace_6926649
  have hstable : (prefixWord ++ tailWord_6926649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926649).length < 2 ^ (prefixWord ++ tailWord_6926649).sum := by decide
  have hdescent : baseEnd_6926649 < baseStart_6926649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926682 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_6926682 : Nat := 118140960795 + 6926682 * 2 ^ 59
def prefixEnd_6926682 : Nat := 4983230072969 + 3 ^ 40 * 6926682 * 2
def baseEnd_6926682 : Nat := 3556717206846373558519775

theorem tailTrace_6926682 : CollatzResearch.WordTrace tailWord_6926682 prefixEnd_6926682 3556717206846373558519775 := by
  unfold tailWord_6926682
  simp only [CollatzResearch.WordTrace]
  refine ⟨63159211872955392987153575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168424564994547714632409533 63159211872955392987153575)
  ·
    refine ⟨94738817809433089480730363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63159211872955392987153575 94738817809433089480730363)
    ·
      refine ⟨142108226714149634221095545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94738817809433089480730363 142108226714149634221095545)
      ·
        refine ⟨106581170035612225665821659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142108226714149634221095545 106581170035612225665821659)
        ·
          refine ⟨159871755053418338498732489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106581170035612225665821659 159871755053418338498732489)
          ·
            refine ⟨119903816290063753874049367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159871755053418338498732489 119903816290063753874049367)
            ·
              refine ⟨179855724435095630811074051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119903816290063753874049367 179855724435095630811074051)
              ·
                refine ⟨269783586652643446216611077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179855724435095630811074051 269783586652643446216611077)
                ·
                  refine ⟨50584422497370646165614577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269783586652643446216611077 50584422497370646165614577)
                  ·
                    refine ⟨37938316873027984624210933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50584422497370646165614577 37938316873027984624210933)
                    ·
                      refine ⟨3556717206846373558519775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37938316873027984624210933 3556717206846373558519775)
                      ·
                        rfl

theorem cell23_6926682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_6926682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926682 prefixEnd_6926682 := by exact prefixLift 6926682
  have htrace : WordTrace (prefixWord ++ tailWord_6926682) baseStart_6926682 baseEnd_6926682 := by
    simpa [prefixWord, tailWord_6926682, baseEnd_6926682] using wordTrace_append hprefix tailTrace_6926682
  have hstable : (prefixWord ++ tailWord_6926682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926682).length < 2 ^ (prefixWord ++ tailWord_6926682).sum := by decide
  have hdescent : baseEnd_6926682 < baseStart_6926682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926729 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 5]
def baseStart_6926729 : Nat := 118140960795 + 6926729 * 2 ^ 59
def prefixEnd_6926729 : Nat := 4983230072969 + 3 ^ 40 * 6926729 * 2
def baseEnd_6926729 : Nat := 3556741340437134874632059

theorem tailTrace_6926729 : CollatzResearch.WordTrace tailWord_6926729 prefixEnd_6926729 3556741340437134874632059 := by
  unfold tailWord_6926729
  simp only [CollatzResearch.WordTrace]
  refine ⟨252638561722651298975575241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168425707815100865983716827 252638561722651298975575241)
  ·
    refine ⟨189478921291988474231681431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252638561722651298975575241 189478921291988474231681431)
    ·
      refine ⟨284218381937982711347522147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189478921291988474231681431 284218381937982711347522147)
      ·
        refine ⟨426327572906974067021283221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284218381937982711347522147 426327572906974067021283221)
        ·
          refine ⟨19984104980014409391622651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 426327572906974067021283221 19984104980014409391622651)
          ·
            refine ⟨29976157470021614087433977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19984104980014409391622651 29976157470021614087433977)
            ·
              refine ⟨22482118102516210565575483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29976157470021614087433977 22482118102516210565575483)
              ·
                refine ⟨33723177153774315848363225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22482118102516210565575483 33723177153774315848363225)
                ·
                  refine ⟨25292382865330736886272419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33723177153774315848363225 25292382865330736886272419)
                  ·
                    refine ⟨37938574297996105329408629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25292382865330736886272419 37938574297996105329408629)
                    ·
                      refine ⟨3556741340437134874632059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37938574297996105329408629 3556741340437134874632059)
                      ·
                        rfl

theorem cell23_6926729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 5].length) (baseStart_6926729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926729 prefixEnd_6926729 := by exact prefixLift 6926729
  have htrace : WordTrace (prefixWord ++ tailWord_6926729) baseStart_6926729 baseEnd_6926729 := by
    simpa [prefixWord, tailWord_6926729, baseEnd_6926729] using wordTrace_append hprefix tailTrace_6926729
  have hstable : (prefixWord ++ tailWord_6926729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926729).length < 2 ^ (prefixWord ++ tailWord_6926729).sum := by decide
  have hdescent : baseEnd_6926729 < baseStart_6926729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926743 : List Nat := [1, 1, 3, 3, 1, 1, 3, 4, 2, 2, 2]
def baseStart_6926743 : Nat := 118140960795 + 6926743 * 2 ^ 59
def prefixEnd_6926743 : Nat := 4983230072969 + 3 ^ 40 * 6926743 * 2
def baseEnd_6926743 : Nat := 3556748529166297819856995

theorem tailTrace_6926743 : CollatzResearch.WordTrace tailWord_6926743 prefixEnd_6926743 3556748529166297819856995 := by
  unfold tailWord_6926743
  simp only [CollatzResearch.WordTrace]
  refine ⟨252639072344600579366584883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168426048229733719577723255 252639072344600579366584883)
  ·
    refine ⟨378958608516900869049877325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252639072344600579366584883 378958608516900869049877325)
    ·
      refine ⟨142109478193837825893703997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378958608516900869049877325 142109478193837825893703997)
      ·
        refine ⟨53291054322689184710138999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142109478193837825893703997 53291054322689184710138999)
        ·
          refine ⟨79936581484033777065208499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53291054322689184710138999 79936581484033777065208499)
          ·
            refine ⟨119904872226050665597812749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79936581484033777065208499 119904872226050665597812749)
            ·
              refine ⟨44964327084768999599179781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119904872226050665597812749 44964327084768999599179781)
              ·
                refine ⟨8430811328394187424846209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44964327084768999599179781 8430811328394187424846209)
                ·
                  refine ⟨6323108496295640568634657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8430811328394187424846209 6323108496295640568634657)
                  ·
                    refine ⟨4742331372221730426475993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323108496295640568634657 4742331372221730426475993)
                    ·
                      refine ⟨3556748529166297819856995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742331372221730426475993 3556748529166297819856995)
                      ·
                        rfl

theorem cell23_6926743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_6926743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926743 prefixEnd_6926743 := by exact prefixLift 6926743
  have htrace : WordTrace (prefixWord ++ tailWord_6926743) baseStart_6926743 baseEnd_6926743 := by
    simpa [prefixWord, tailWord_6926743, baseEnd_6926743] using wordTrace_append hprefix tailTrace_6926743
  have hstable : (prefixWord ++ tailWord_6926743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926743).length < 2 ^ (prefixWord ++ tailWord_6926743).sum := by decide
  have hdescent : baseEnd_6926743 < baseStart_6926743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926760 : List Nat := [2, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_6926760 : Nat := 118140960795 + 6926760 * 2 ^ 59
def prefixEnd_6926760 : Nat := 4983230072969 + 3 ^ 40 * 6926760 * 2
def baseEnd_6926760 : Nat := 3556757258337424253344417

theorem tailTrace_6926760 : CollatzResearch.WordTrace tailWord_6926760 prefixEnd_6926760 3556757258337424253344417 := by
  unfold tailWord_6926760
  simp only [CollatzResearch.WordTrace]
  refine ⟨126319846192769495634976867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168426461590359327513302489 126319846192769495634976867)
  ·
    refine ⟨189479769289154243452465301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126319846192769495634976867 189479769289154243452465301)
    ·
      refine ⟨8881864185429105161834311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189479769289154243452465301 8881864185429105161834311)
      ·
        refine ⟨13322796278143657742751467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8881864185429105161834311 13322796278143657742751467)
        ·
          refine ⟨19984194417215486614127201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13322796278143657742751467 19984194417215486614127201)
          ·
            refine ⟨14988145812911614960595401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19984194417215486614127201 14988145812911614960595401)
            ·
              refine ⟨11241109359683711220446551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14988145812911614960595401 11241109359683711220446551)
              ·
                refine ⟨16861664039525566830669827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11241109359683711220446551 16861664039525566830669827)
                ·
                  refine ⟨25292496059288350246004741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16861664039525566830669827 25292496059288350246004741)
                  ·
                    refine ⟨4742343011116565671125889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25292496059288350246004741 4742343011116565671125889)
                    ·
                      refine ⟨3556757258337424253344417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742343011116565671125889 3556757258337424253344417)
                      ·
                        rfl

theorem cell23_6926760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_6926760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926760 prefixEnd_6926760 := by exact prefixLift 6926760
  have htrace : WordTrace (prefixWord ++ tailWord_6926760) baseStart_6926760 baseEnd_6926760 := by
    simpa [prefixWord, tailWord_6926760, baseEnd_6926760] using wordTrace_append hprefix tailTrace_6926760
  have hstable : (prefixWord ++ tailWord_6926760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926760).length < 2 ^ (prefixWord ++ tailWord_6926760).sum := by decide
  have hdescent : baseEnd_6926760 < baseStart_6926760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926799 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_6926799 : Nat := 118140960795 + 6926799 * 2 ^ 59
def prefixEnd_6926799 : Nat := 4983230072969 + 3 ^ 40 * 6926799 * 2
def baseEnd_6926799 : Nat := 3556777284082949600756737

theorem tailTrace_6926799 : CollatzResearch.WordTrace tailWord_6926799 prefixEnd_6926799 3556777284082949600756737 := by
  unfold tailWord_6926799
  simp only [CollatzResearch.WordTrace]
  refine ⟨252641114832397700930623451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168427409888265133953748967 252641114832397700930623451)
  ·
    refine ⟨378961672248596551395935177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252641114832397700930623451 378961672248596551395935177)
    ·
      refine ⟨284221254186447413546951383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378961672248596551395935177 284221254186447413546951383)
      ·
        refine ⟨426331881279671120320427075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284221254186447413546951383 426331881279671120320427075)
        ·
          refine ⟨639497821919506680480640613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426331881279671120320427075 639497821919506680480640613)
          ·
            refine ⟨119905841609907502590120115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 639497821919506680480640613 119905841609907502590120115)
            ·
              refine ⟨179858762414861253885180173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119905841609907502590120115 179858762414861253885180173)
              ·
                refine ⟨67447035905572970206942565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179858762414861253885180173 67447035905572970206942565)
                ·
                  refine ⟨12646319232294931913801731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67447035905572970206942565 12646319232294931913801731)
                  ·
                    refine ⟨18969478848442397870702597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12646319232294931913801731 18969478848442397870702597)
                    ·
                      refine ⟨3556777284082949600756737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18969478848442397870702597 3556777284082949600756737)
                      ·
                        rfl

theorem cell23_6926799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_6926799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926799 prefixEnd_6926799 := by exact prefixLift 6926799
  have htrace : WordTrace (prefixWord ++ tailWord_6926799) baseStart_6926799 baseEnd_6926799 := by
    simpa [prefixWord, tailWord_6926799, baseEnd_6926799] using wordTrace_append hprefix tailTrace_6926799
  have hstable : (prefixWord ++ tailWord_6926799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926799).length < 2 ^ (prefixWord ++ tailWord_6926799).sum := by decide
  have hdescent : baseEnd_6926799 < baseStart_6926799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926806 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6926806 : Nat := 118140960795 + 6926806 * 2 ^ 59
def prefixEnd_6926806 : Nat := 4983230072969 + 3 ^ 40 * 6926806 * 2
def baseEnd_6926806 : Nat := 3556780878447531073369205

theorem tailTrace_6926806 : CollatzResearch.WordTrace tailWord_6926806 prefixEnd_6926806 3556780878447531073369205 := by
  unfold tailWord_6926806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15790085633960771320383017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168427580095581560750752181 15790085633960771320383017)
  ·
    refine ⟨11842564225470578490287263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15790085633960771320383017 11842564225470578490287263)
    ·
      refine ⟨17763846338205867735430895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11842564225470578490287263 17763846338205867735430895)
      ·
        refine ⟨26645769507308801603146343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17763846338205867735430895 26645769507308801603146343)
        ·
          refine ⟨39968654260963202404719515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26645769507308801603146343 39968654260963202404719515)
          ·
            refine ⟨59952981391444803607079273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39968654260963202404719515 59952981391444803607079273)
            ·
              refine ⟨44964736043583602705309455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59952981391444803607079273 44964736043583602705309455)
              ·
                refine ⟨67447104065375404057964183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44964736043583602705309455 67447104065375404057964183)
                ·
                  refine ⟨101170656098063106086946275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67447104065375404057964183 101170656098063106086946275)
                  ·
                    refine ⟨151755984147094659130419413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101170656098063106086946275 151755984147094659130419413)
                    ·
                      refine ⟨3556780878447531073369205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151755984147094659130419413 3556780878447531073369205)
                      ·
                        rfl

theorem cell23_6926806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6926806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926806 prefixEnd_6926806 := by exact prefixLift 6926806
  have htrace : WordTrace (prefixWord ++ tailWord_6926806) baseStart_6926806 baseEnd_6926806 := by
    simpa [prefixWord, tailWord_6926806, baseEnd_6926806] using wordTrace_append hprefix tailTrace_6926806
  have hstable : (prefixWord ++ tailWord_6926806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926806).length < 2 ^ (prefixWord ++ tailWord_6926806).sum := by decide
  have hdescent : baseEnd_6926806 < baseStart_6926806 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926816 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2]
def baseStart_6926816 : Nat := 118140960795 + 6926816 * 2 ^ 59
def prefixEnd_6926816 : Nat := 4983230072969 + 3 ^ 40 * 6926816 * 2
def baseEnd_6926816 : Nat := 3556786013254076034244159

theorem tailTrace_6926816 : CollatzResearch.WordTrace tailWord_6926816 prefixEnd_6926816 3556786013254076034244159 := by
  unfold tailWord_6926816
  simp only [CollatzResearch.WordTrace]
  refine ⟨126320867436668056416996151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168427823248890741889328201 126320867436668056416996151)
  ·
    refine ⟨189481301155002084625494227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126320867436668056416996151 189481301155002084625494227)
    ·
      refine ⟨284221951732503126938241341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189481301155002084625494227 284221951732503126938241341)
      ·
        refine ⟨106583231899688672601840503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284221951732503126938241341 106583231899688672601840503)
        ·
          refine ⟨159874847849533008902760755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106583231899688672601840503 159874847849533008902760755)
          ·
            refine ⟨239812271774299513354141133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159874847849533008902760755 239812271774299513354141133)
            ·
              refine ⟨89929601915362317507802925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239812271774299513354141133 89929601915362317507802925)
              ·
                refine ⟨33723600718260869065426097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89929601915362317507802925 33723600718260869065426097)
                ·
                  refine ⟨25292700538695651799069573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33723600718260869065426097 25292700538695651799069573)
                  ·
                    refine ⟨4742381351005434712325545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25292700538695651799069573 4742381351005434712325545)
                    ·
                      refine ⟨3556786013254076034244159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742381351005434712325545 3556786013254076034244159)
                      ·
                        rfl

theorem cell23_6926816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_6926816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926816 prefixEnd_6926816 := by exact prefixLift 6926816
  have htrace : WordTrace (prefixWord ++ tailWord_6926816) baseStart_6926816 baseEnd_6926816 := by
    simpa [prefixWord, tailWord_6926816, baseEnd_6926816] using wordTrace_append hprefix tailTrace_6926816
  have hstable : (prefixWord ++ tailWord_6926816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926816).length < 2 ^ (prefixWord ++ tailWord_6926816).sum := by decide
  have hdescent : baseEnd_6926816 < baseStart_6926816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926850 : List Nat := [3, 4, 1, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6926850 : Nat := 118140960795 + 6926850 * 2 ^ 59
def prefixEnd_6926850 : Nat := 4983230072969 + 3 ^ 40 * 6926850 * 2
def baseEnd_6926850 : Nat := 3556803471596328901219003

theorem tailTrace_6926850 : CollatzResearch.WordTrace tailWord_6926850 prefixEnd_6926850 3556803471596328901219003 := by
  unfold tailWord_6926850
  simp only [CollatzResearch.WordTrace]
  refine ⟨63160743738803234160182501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168428649970141957760486669 63160743738803234160182501)
  ·
    refine ⟨11842639451025606405034219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63160743738803234160182501 11842639451025606405034219)
    ·
      refine ⟨17763959176538409607551329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11842639451025606405034219 17763959176538409607551329)
      ·
        refine ⟨13322969382403807205663497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17763959176538409607551329 13322969382403807205663497)
        ·
          refine ⟨9992227036802855404247623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13322969382403807205663497 9992227036802855404247623)
          ·
            refine ⟨14988340555204283106371435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992227036802855404247623 14988340555204283106371435)
            ·
              refine ⟨22482510832806424659557153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14988340555204283106371435 22482510832806424659557153)
              ·
                refine ⟨16861883124604818494667865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22482510832806424659557153 16861883124604818494667865)
                ·
                  refine ⟨12646412343453613871000899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16861883124604818494667865 12646412343453613871000899)
                  ·
                    refine ⟨18969618515180420806501349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12646412343453613871000899 18969618515180420806501349)
                    ·
                      refine ⟨3556803471596328901219003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18969618515180420806501349 3556803471596328901219003)
                      ·
                        rfl

theorem cell23_6926850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6926850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926850 prefixEnd_6926850 := by exact prefixLift 6926850
  have htrace : WordTrace (prefixWord ++ tailWord_6926850) baseStart_6926850 baseEnd_6926850 := by
    simpa [prefixWord, tailWord_6926850, baseEnd_6926850] using wordTrace_append hprefix tailTrace_6926850
  have hstable : (prefixWord ++ tailWord_6926850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926850).length < 2 ^ (prefixWord ++ tailWord_6926850).sum := by decide
  have hdescent : baseEnd_6926850 < baseStart_6926850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926887 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6926887 : Nat := 118140960795 + 6926887 * 2 ^ 59
def prefixEnd_6926887 : Nat := 4983230072969 + 3 ^ 40 * 6926887 * 2
def baseEnd_6926887 : Nat := 3556822470380545256456333

theorem tailTrace_6926887 : CollatzResearch.WordTrace tailWord_6926887 prefixEnd_6926887 3556822470380545256456333 := by
  unfold tailWord_6926887
  simp only [CollatzResearch.WordTrace]
  refine ⟨252644324456078891959826915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168429549637385927973217943 252644324456078891959826915)
  ·
    refine ⟨378966486684118337939740373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252644324456078891959826915 378966486684118337939740373)
    ·
      refine ⟨8882027031659023545462665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 378966486684118337939740373 8882027031659023545462665)
      ·
        refine ⟨6661520273744267659096999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8882027031659023545462665 6661520273744267659096999)
        ·
          refine ⟨9992280410616401488645499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661520273744267659096999 9992280410616401488645499)
          ·
            refine ⟨14988420615924602232968249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992280410616401488645499 14988420615924602232968249)
            ·
              refine ⟨11241315461943451674726187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14988420615924602232968249 11241315461943451674726187)
              ·
                refine ⟨16861973192915177512089281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11241315461943451674726187 16861973192915177512089281)
                ·
                  refine ⟨12646479894686383134066961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16861973192915177512089281 12646479894686383134066961)
                  ·
                    refine ⟨9484859921014787350550221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12646479894686383134066961 9484859921014787350550221)
                    ·
                      refine ⟨3556822470380545256456333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9484859921014787350550221 3556822470380545256456333)
                      ·
                        rfl

theorem cell23_6926887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6926887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926887 prefixEnd_6926887 := by exact prefixLift 6926887
  have htrace : WordTrace (prefixWord ++ tailWord_6926887) baseStart_6926887 baseEnd_6926887 := by
    simpa [prefixWord, tailWord_6926887, baseEnd_6926887] using wordTrace_append hprefix tailTrace_6926887
  have hstable : (prefixWord ++ tailWord_6926887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926887).length < 2 ^ (prefixWord ++ tailWord_6926887).sum := by decide
  have hdescent : baseEnd_6926887 < baseStart_6926887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926903 : List Nat := [1, 1, 3, 1, 2, 3, 5, 1, 1, 5]
def baseStart_6926903 : Nat := 118140960795 + 6926903 * 2 ^ 59
def prefixEnd_6926903 : Nat := 4983230072969 + 3 ^ 40 * 6926903 * 2
def baseEnd_6926903 : Nat := 1185610228690339064618753

theorem tailTrace_6926903 : CollatzResearch.WordTrace tailWord_6926903 prefixEnd_6926903 1185610228690339064618753 := by
  unfold tailWord_6926903
  simp only [CollatzResearch.WordTrace]
  refine ⟨252644908024020926692409363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168429938682680617794939575 252644908024020926692409363)
  ·
    refine ⟨378967362036031390038614045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252644908024020926692409363 378967362036031390038614045)
    ·
      refine ⟨142112760763511771264480267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378967362036031390038614045 142112760763511771264480267)
      ·
        refine ⟨213169141145267656896720401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142112760763511771264480267 213169141145267656896720401)
        ·
          refine ⟨159876855858950742672540301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213169141145267656896720401 159876855858950742672540301)
          ·
            refine ⟨59953820947106528502202613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159876855858950742672540301 59953820947106528502202613)
            ·
              refine ⟨5620670713791237047081495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59953820947106528502202613 5620670713791237047081495)
              ·
                refine ⟨8431006070686855570622243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620670713791237047081495 8431006070686855570622243)
                ·
                  refine ⟨12646509106030283355933365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8431006070686855570622243 12646509106030283355933365)
                  ·
                    refine ⟨1185610228690339064618753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12646509106030283355933365 1185610228690339064618753)
                    ·
                      rfl

theorem cell23_6926903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 1, 5].length) (baseStart_6926903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926903 prefixEnd_6926903 := by exact prefixLift 6926903
  have htrace : WordTrace (prefixWord ++ tailWord_6926903) baseStart_6926903 baseEnd_6926903 := by
    simpa [prefixWord, tailWord_6926903, baseEnd_6926903] using wordTrace_append hprefix tailTrace_6926903
  have hstable : (prefixWord ++ tailWord_6926903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926903).length < 2 ^ (prefixWord ++ tailWord_6926903).sum := by decide
  have hdescent : baseEnd_6926903 < baseStart_6926903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926917 : List Nat := [1, 3, 1, 1, 1, 5, 4, 2, 1, 1, 3]
def baseStart_6926917 : Nat := 118140960795 + 6926917 * 2 ^ 59
def prefixEnd_6926917 : Nat := 4983230072969 + 3 ^ 40 * 6926917 * 2
def baseEnd_6926917 : Nat := 3556837874800180139081195

theorem tailTrace_6926917 : CollatzResearch.WordTrace tailWord_6926917 prefixEnd_6926917 3556837874800180139081195 := by
  unfold tailWord_6926917
  simp only [CollatzResearch.WordTrace]
  refine ⟨252645418645970207083419005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168430279097313471388946003 252645418645970207083419005)
  ·
    refine ⟨94742031992238827656282127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252645418645970207083419005 94742031992238827656282127)
    ·
      refine ⟨142113047988358241484423191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94742031992238827656282127 142113047988358241484423191)
      ·
        refine ⟨213169571982537362226634787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142113047988358241484423191 213169571982537362226634787)
        ·
          refine ⟨319754357973806043339952181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213169571982537362226634787 319754357973806043339952181)
          ·
            refine ⟨29976971060044316563120517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 319754357973806043339952181 29976971060044316563120517)
            ·
              refine ⟨5620682073758309355585097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29976971060044316563120517 5620682073758309355585097)
              ·
                refine ⟨4215511555318732016688823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620682073758309355585097 4215511555318732016688823)
                ·
                  refine ⟨6323267332978098025033235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215511555318732016688823 6323267332978098025033235)
                  ·
                    refine ⟨9484900999467147037549853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6323267332978098025033235 9484900999467147037549853)
                    ·
                      refine ⟨3556837874800180139081195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9484900999467147037549853 3556837874800180139081195)
                      ·
                        rfl

theorem cell23_6926917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 1, 1, 3].length) (baseStart_6926917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926917 prefixEnd_6926917 := by exact prefixLift 6926917
  have htrace : WordTrace (prefixWord ++ tailWord_6926917) baseStart_6926917 baseEnd_6926917 := by
    simpa [prefixWord, tailWord_6926917, baseEnd_6926917] using wordTrace_append hprefix tailTrace_6926917
  have hstable : (prefixWord ++ tailWord_6926917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926917).length < 2 ^ (prefixWord ++ tailWord_6926917).sum := by decide
  have hdescent : baseEnd_6926917 < baseStart_6926917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926926 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6926926 : Nat := 118140960795 + 6926926 * 2 ^ 59
def prefixEnd_6926926 : Nat := 4983230072969 + 3 ^ 40 * 6926926 * 2
def baseEnd_6926926 : Nat := 3556842496126070603868653

theorem tailTrace_6926926 : CollatzResearch.WordTrace tailWord_6926926 prefixEnd_6926926 3556842496126070603868653 := by
  unfold tailWord_6926926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580718362867200202562079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168430497935291734413664421 31580718362867200202562079)
  ·
    refine ⟨47371077544300800303843119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31580718362867200202562079 47371077544300800303843119)
    ·
      refine ⟨71056616316451200455764679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47371077544300800303843119 71056616316451200455764679)
      ·
        refine ⟨106584924474676800683647019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71056616316451200455764679 106584924474676800683647019)
        ·
          refine ⟨159877386712015201025470529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106584924474676800683647019 159877386712015201025470529)
          ·
            refine ⟨119908040034011400769102897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159877386712015201025470529 119908040034011400769102897)
            ·
              refine ⟨89931030025508550576827173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119908040034011400769102897 89931030025508550576827173)
              ·
                refine ⟨16862068129782853233155095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89931030025508550576827173 16862068129782853233155095)
                ·
                  refine ⟨25293102194674279849732643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16862068129782853233155095 25293102194674279849732643)
                  ·
                    refine ⟨37939653292011419774598965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25293102194674279849732643 37939653292011419774598965)
                    ·
                      refine ⟨3556842496126070603868653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37939653292011419774598965 3556842496126070603868653)
                      ·
                        rfl

theorem cell23_6926926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6926926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926926 prefixEnd_6926926 := by exact prefixLift 6926926
  have htrace : WordTrace (prefixWord ++ tailWord_6926926) baseStart_6926926 baseEnd_6926926 := by
    simpa [prefixWord, tailWord_6926926, baseEnd_6926926] using wordTrace_append hprefix tailTrace_6926926
  have hstable : (prefixWord ++ tailWord_6926926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926926).length < 2 ^ (prefixWord ++ tailWord_6926926).sum := by decide
  have hdescent : baseEnd_6926926 < baseStart_6926926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926933 : List Nat := [1, 3, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_6926933 : Nat := 118140960795 + 6926933 * 2 ^ 59
def prefixEnd_6926933 : Nat := 4983230072969 + 3 ^ 40 * 6926933 * 2
def baseEnd_6926933 : Nat := 1185615363496884025493707

theorem tailTrace_6926933 : CollatzResearch.WordTrace tailWord_6926933 prefixEnd_6926933 1185615363496884025493707 := by
  unfold tailWord_6926933
  simp only [CollatzResearch.WordTrace]
  refine ⟨252646002213912241816001453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168430668142608161210667635 252646002213912241816001453)
  ·
    refine ⟨94742250830217090681000545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252646002213912241816001453 94742250830217090681000545)
    ·
      refine ⟨71056688122662818010750409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94742250830217090681000545 71056688122662818010750409)
      ·
        refine ⟨53292516091997113508062807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71056688122662818010750409 53292516091997113508062807)
        ·
          refine ⟨79938774137995670262094211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53292516091997113508062807 79938774137995670262094211)
          ·
            refine ⟨119908161206993505393141317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79938774137995670262094211 119908161206993505393141317)
            ·
              refine ⟨22482780226311282261213997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119908161206993505393141317 22482780226311282261213997)
              ·
                refine ⟨8431042584866730847955249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22482780226311282261213997 8431042584866730847955249)
                ·
                  refine ⟨6323281938650048135966437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8431042584866730847955249 6323281938650048135966437)
                  ·
                    refine ⟨1185615363496884025493707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6323281938650048135966437 1185615363496884025493707)
                    ·
                      rfl

theorem cell23_6926933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_6926933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926933 prefixEnd_6926933 := by exact prefixLift 6926933
  have htrace : WordTrace (prefixWord ++ tailWord_6926933) baseStart_6926933 baseEnd_6926933 := by
    simpa [prefixWord, tailWord_6926933, baseEnd_6926933] using wordTrace_append hprefix tailTrace_6926933
  have hstable : (prefixWord ++ tailWord_6926933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926933).length < 2 ^ (prefixWord ++ tailWord_6926933).sum := by decide
  have hdescent : baseEnd_6926933 < baseStart_6926933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926936 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_6926936 : Nat := 118140960795 + 6926936 * 2 ^ 59
def prefixEnd_6926936 : Nat := 4983230072969 + 3 ^ 40 * 6926936 * 2
def baseEnd_6926936 : Nat := 3556847630932615564743607

theorem tailTrace_6926936 : CollatzResearch.WordTrace tailWord_6926936 prefixEnd_6926936 3556847630932615564743607 := by
  unfold tailWord_6926936
  simp only [CollatzResearch.WordTrace]
  refine ⟨126323055816450686664180331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168430741088600915552240441 126323055816450686664180331)
  ·
    refine ⟨189484583724676029996270497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126323055816450686664180331 189484583724676029996270497)
    ·
      refine ⟨142113437793507022497202873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189484583724676029996270497 142113437793507022497202873)
      ·
        refine ⟨106585078345130266872902155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142113437793507022497202873 106585078345130266872902155)
        ·
          refine ⟨159877617517695400309353233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106585078345130266872902155 159877617517695400309353233)
          ·
            refine ⟨119908213138271550232014925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159877617517695400309353233 119908213138271550232014925)
            ·
              refine ⟨44965579926851831337005597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119908213138271550232014925 44965579926851831337005597)
              ·
                refine ⟨16862092472569436751377099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44965579926851831337005597 16862092472569436751377099)
                ·
                  refine ⟨25293138708854155127065649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16862092472569436751377099 25293138708854155127065649)
                  ·
                    refine ⟨18969854031640616345299237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25293138708854155127065649 18969854031640616345299237)
                    ·
                      refine ⟨3556847630932615564743607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18969854031640616345299237 3556847630932615564743607)
                      ·
                        rfl

theorem cell23_6926936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_6926936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926936 prefixEnd_6926936 := by exact prefixLift 6926936
  have htrace : WordTrace (prefixWord ++ tailWord_6926936) baseStart_6926936 baseEnd_6926936 := by
    simpa [prefixWord, tailWord_6926936, baseEnd_6926936] using wordTrace_append hprefix tailTrace_6926936
  have hstable : (prefixWord ++ tailWord_6926936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926936).length < 2 ^ (prefixWord ++ tailWord_6926936).sum := by decide
  have hdescent : baseEnd_6926936 < baseStart_6926936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926957 : List Nat := [1, 5, 1, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_6926957 : Nat := 118140960795 + 6926957 * 2 ^ 59
def prefixEnd_6926957 : Nat := 4983230072969 + 3 ^ 40 * 6926957 * 2
def baseEnd_6926957 : Nat := 3556858414026359982581011

theorem tailTrace_6926957 : CollatzResearch.WordTrace tailWord_6926957 prefixEnd_6926957 3556858414026359982581011 := by
  unfold tailWord_6926957
  simp only [CollatzResearch.WordTrace]
  refine ⟨252646877565825293914875125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168431251710550195943250083 252646877565825293914875125)
  ·
    refine ⟨23685644771796121304519543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252646877565825293914875125 23685644771796121304519543)
    ·
      refine ⟨35528467157694181956779315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23685644771796121304519543 35528467157694181956779315)
      ·
        refine ⟨53292700736541272935168973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35528467157694181956779315 53292700736541272935168973)
        ·
          refine ⟨19984762776202977350688365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53292700736541272935168973 19984762776202977350688365)
          ·
            refine ⟨7494286041076116506508137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19984762776202977350688365 7494286041076116506508137)
            ·
              refine ⟨5620714530807087379881103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494286041076116506508137 5620714530807087379881103)
              ·
                refine ⟨8431071796210631069821655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620714530807087379881103 8431071796210631069821655)
                ·
                  refine ⟨12646607694315946604732483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8431071796210631069821655 12646607694315946604732483)
                  ·
                    refine ⟨18969911541473919907098725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12646607694315946604732483 18969911541473919907098725)
                    ·
                      refine ⟨3556858414026359982581011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18969911541473919907098725 3556858414026359982581011)
                      ·
                        rfl

theorem cell23_6926957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_6926957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926957 prefixEnd_6926957 := by exact prefixLift 6926957
  have htrace : WordTrace (prefixWord ++ tailWord_6926957) baseStart_6926957 baseEnd_6926957 := by
    simpa [prefixWord, tailWord_6926957, baseEnd_6926957] using wordTrace_append hprefix tailTrace_6926957
  have hstable : (prefixWord ++ tailWord_6926957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926957).length < 2 ^ (prefixWord ++ tailWord_6926957).sum := by decide
  have hdescent : baseEnd_6926957 < baseStart_6926957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6926960 : List Nat := [2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3]
def baseStart_6926960 : Nat := 118140960795 + 6926960 * 2 ^ 59
def prefixEnd_6926960 : Nat := 4983230072969 + 3 ^ 40 * 6926960 * 2
def baseEnd_6926960 : Nat := 3556859954468323470843497

theorem tailTrace_6926960 : CollatzResearch.WordTrace tailWord_6926960 prefixEnd_6926960 3556859954468323470843497 := by
  unfold tailWord_6926960
  simp only [CollatzResearch.WordTrace]
  refine ⟨126323493492407212713617167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168431324656542950284822889 126323493492407212713617167)
  ·
    refine ⟨189485240238610819070425751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126323493492407212713617167 189485240238610819070425751)
    ·
      refine ⟨284227860357916228605638627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189485240238610819070425751 284227860357916228605638627)
      ·
        refine ⟨426341790536874342908457941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284227860357916228605638627 426341790536874342908457941)
        ·
          refine ⟨9992385715707992411916983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 426341790536874342908457941 9992385715707992411916983)
          ·
            refine ⟨14988578573561988617875475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9992385715707992411916983 14988578573561988617875475)
            ·
              refine ⟨22482867860342982926813213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14988578573561988617875475 22482867860342982926813213)
              ·
                refine ⟨8431075447628618597554955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22482867860342982926813213 8431075447628618597554955)
                ·
                  refine ⟨12646613171442927896332433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8431075447628618597554955 12646613171442927896332433)
                  ·
                    refine ⟨9484959878582195922249325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12646613171442927896332433 9484959878582195922249325)
                    ·
                      refine ⟨3556859954468323470843497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9484959878582195922249325 3556859954468323470843497)
                      ·
                        rfl

theorem cell23_6926960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_6926960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6926960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6926960 prefixEnd_6926960 := by exact prefixLift 6926960
  have htrace : WordTrace (prefixWord ++ tailWord_6926960) baseStart_6926960 baseEnd_6926960 := by
    simpa [prefixWord, tailWord_6926960, baseEnd_6926960] using wordTrace_append hprefix tailTrace_6926960
  have hstable : (prefixWord ++ tailWord_6926960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6926960).length < 2 ^ (prefixWord ++ tailWord_6926960).sum := by decide
  have hdescent : baseEnd_6926960 < baseStart_6926960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6926960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927013 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 3, 4, 2]
def baseStart_6927013 : Nat := 118140960795 + 6927013 * 2 ^ 59
def prefixEnd_6927013 : Nat := 4983230072969 + 3 ^ 40 * 6927013 * 2
def baseEnd_6927013 : Nat := 3556887168943011763480753

theorem tailTrace_6927013 : CollatzResearch.WordTrace tailWord_6927013 prefixEnd_6927013 3556887168943011763480753 := by
  unfold tailWord_6927013
  simp only [CollatzResearch.WordTrace]
  refine ⟨252648920053622415478913693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168432613369081610319275795 252648920053622415478913693)
  ·
    refine ⟨94743345020108405804592635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252648920053622415478913693 94743345020108405804592635)
    ·
      refine ⟨142115017530162608706888953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94743345020108405804592635 142115017530162608706888953)
      ·
        refine ⟨106586263147621956530166715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142115017530162608706888953 106586263147621956530166715)
        ·
          refine ⟨159879394721432934795250073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106586263147621956530166715 159879394721432934795250073)
          ·
            refine ⟨119909546041074701096437555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159879394721432934795250073 119909546041074701096437555)
            ·
              refine ⟨179864319061612051644656333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119909546041074701096437555 179864319061612051644656333)
              ·
                refine ⟨67449119648104519366746125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179864319061612051644656333 67449119648104519366746125)
                ·
                  refine ⟨25293419868039194762529797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67449119648104519366746125 25293419868039194762529797)
                  ·
                    refine ⟨4742516225257349017974337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25293419868039194762529797 4742516225257349017974337)
                    ·
                      refine ⟨3556887168943011763480753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742516225257349017974337 3556887168943011763480753)
                      ·
                        rfl

theorem cell23_6927013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_6927013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927013 prefixEnd_6927013 := by exact prefixLift 6927013
  have htrace : WordTrace (prefixWord ++ tailWord_6927013) baseStart_6927013 baseEnd_6927013 := by
    simpa [prefixWord, tailWord_6927013, baseEnd_6927013] using wordTrace_append hprefix tailTrace_6927013
  have hstable : (prefixWord ++ tailWord_6927013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927013).length < 2 ^ (prefixWord ++ tailWord_6927013).sum := by decide
  have hdescent : baseEnd_6927013 < baseStart_6927013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927087 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 5]
def baseStart_6927087 : Nat := 118140960795 + 6927087 * 2 ^ 59
def prefixEnd_6927087 : Nat := 4983230072969 + 3 ^ 40 * 6927087 * 2
def baseEnd_6927087 : Nat := 395213907390160497106157

theorem tailTrace_6927087 : CollatzResearch.WordTrace tailWord_6927087 prefixEnd_6927087 395213907390160497106157 := by
  unfold tailWord_6927087
  simp only [CollatzResearch.WordTrace]
  refine ⟨252651619055354326117107515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168434412703569550744738343 252651619055354326117107515)
  ·
    refine ⟨378977428583031489175661273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252651619055354326117107515 378977428583031489175661273)
    ·
      refine ⟨284233071437273616881745955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 378977428583031489175661273 284233071437273616881745955)
      ·
        refine ⟨426349607155910425322618933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284233071437273616881745955 426349607155910425322618933)
        ·
          refine ⟨39970275670866602373995525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426349607155910425322618933 39970275670866602373995525)
          ·
            refine ⟨7494426688287487945124161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39970275670866602373995525 7494426688287487945124161)
            ·
              refine ⟨5620820016215615958843121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494426688287487945124161 5620820016215615958843121)
              ·
                refine ⟨4215615012161711969132341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5620820016215615958843121 4215615012161711969132341)
                ·
                  refine ⟨395213907390160497106157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4215615012161711969132341 395213907390160497106157)
                  ·
                    rfl

theorem cell23_6927087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 5].length) (baseStart_6927087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927087 prefixEnd_6927087 := by exact prefixLift 6927087
  have htrace : WordTrace (prefixWord ++ tailWord_6927087) baseStart_6927087 baseEnd_6927087 := by
    simpa [prefixWord, tailWord_6927087, baseEnd_6927087] using wordTrace_append hprefix tailTrace_6927087
  have hstable : (prefixWord ++ tailWord_6927087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927087).length < 2 ^ (prefixWord ++ tailWord_6927087).sum := by decide
  have hdescent : baseEnd_6927087 < baseStart_6927087 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927090 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_6927090 : Nat := 118140960795 + 6927090 * 2 ^ 59
def prefixEnd_6927090 : Nat := 4983230072969 + 3 ^ 40 * 6927090 * 2
def baseEnd_6927090 : Nat := 3556926706953407962217899

theorem tailTrace_6927090 : CollatzResearch.WordTrace tailWord_6927090 prefixEnd_6927090 3556926706953407962217899 := by
  unfold tailWord_6927090
  simp only [CollatzResearch.WordTrace]
  refine ⟨63162932118585864407366681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168434485649562305086311149 63162932118585864407366681)
  ·
    refine ⟨47372199088939398305525011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63162932118585864407366681 47372199088939398305525011)
    ·
      refine ⟨71058298633409097458287517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47372199088939398305525011 71058298633409097458287517)
      ·
        refine ⟨26646861987528411546857819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71058298633409097458287517 26646861987528411546857819)
        ·
          refine ⟨39970292981292617320286729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26646861987528411546857819 39970292981292617320286729)
          ·
            refine ⟨29977719735969462990215047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39970292981292617320286729 29977719735969462990215047)
            ·
              refine ⟨44966579603954194485322571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29977719735969462990215047 44966579603954194485322571)
              ·
                refine ⟨67449869405931291727983857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44966579603954194485322571 67449869405931291727983857)
                ·
                  refine ⟨50587402054448468795987893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67449869405931291727983857 50587402054448468795987893)
                  ·
                    refine ⟨4742568942604543949623865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50587402054448468795987893 4742568942604543949623865)
                    ·
                      refine ⟨3556926706953407962217899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742568942604543949623865 3556926706953407962217899)
                      ·
                        rfl

theorem cell23_6927090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_6927090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927090 prefixEnd_6927090 := by exact prefixLift 6927090
  have htrace : WordTrace (prefixWord ++ tailWord_6927090) baseStart_6927090 baseEnd_6927090 := by
    simpa [prefixWord, tailWord_6927090, baseEnd_6927090] using wordTrace_append hprefix tailTrace_6927090
  have hstable : (prefixWord ++ tailWord_6927090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927090).length < 2 ^ (prefixWord ++ tailWord_6927090).sum := by decide
  have hdescent : baseEnd_6927090 < baseStart_6927090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927113 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 5, 4]
def baseStart_6927113 : Nat := 118140960795 + 6927113 * 2 ^ 59
def prefixEnd_6927113 : Nat := 4983230072969 + 3 ^ 40 * 6927113 * 2
def baseEnd_6927113 : Nat := 1185646172336153790743431

theorem tailTrace_6927113 : CollatzResearch.WordTrace tailWord_6927113 prefixEnd_6927113 1185646172336153790743431 := by
  unfold tailWord_6927113
  simp only [CollatzResearch.WordTrace]
  refine ⟨252652567353260132557553993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168435044902173421705035995 252652567353260132557553993)
  ·
    refine ⟨189489425514945099418165495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252652567353260132557553993 189489425514945099418165495)
    ·
      refine ⟨284234138272417649127248243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189489425514945099418165495 284234138272417649127248243)
      ·
        refine ⟨426351207408626473690872365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284234138272417649127248243 426351207408626473690872365)
        ·
          refine ⟨159881702778234927634077137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426351207408626473690872365 159881702778234927634077137)
          ·
            refine ⟨119911277083676195725557853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159881702778234927634077137 119911277083676195725557853)
            ·
              refine ⟨44966728906378573397084195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119911277083676195725557853 44966728906378573397084195)
              ·
                refine ⟨67450093359567860095626293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44966728906378573397084195 67450093359567860095626293)
                ·
                  refine ⟨6323446252459486883964965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67450093359567860095626293 6323446252459486883964965)
                  ·
                    refine ⟨1185646172336153790743431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6323446252459486883964965 1185646172336153790743431)
                    ·
                      rfl

theorem cell23_6927113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 4].length) (baseStart_6927113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927113 prefixEnd_6927113 := by exact prefixLift 6927113
  have htrace : WordTrace (prefixWord ++ tailWord_6927113) baseStart_6927113 baseEnd_6927113 := by
    simpa [prefixWord, tailWord_6927113, baseEnd_6927113] using wordTrace_append hprefix tailTrace_6927113
  have hstable : (prefixWord ++ tailWord_6927113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927113).length < 2 ^ (prefixWord ++ tailWord_6927113).sum := by decide
  have hdescent : baseEnd_6927113 < baseStart_6927113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927123 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3]
def baseStart_6927123 : Nat := 118140960795 + 6927123 * 2 ^ 59
def prefixEnd_6927123 : Nat := 4983230072969 + 3 ^ 40 * 6927123 * 2
def baseEnd_6927123 : Nat := 3556943651815006333105247

theorem tailTrace_6927123 : CollatzResearch.WordTrace tailWord_6927123 prefixEnd_6927123 3556943651815006333105247 := by
  unfold tailWord_6927123
  simp only [CollatzResearch.WordTrace]
  refine ⟨252652932083223904265418023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168435288055482602843612015 252652932083223904265418023)
  ·
    refine ⟨378979398124835856398127035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252652932083223904265418023 378979398124835856398127035)
    ·
      refine ⟨568469097187253784597190553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378979398124835856398127035 568469097187253784597190553)
      ·
        refine ⟨426351822890440338447892915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568469097187253784597190553 426351822890440338447892915)
        ·
          refine ⟨639527734335660507671839373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426351822890440338447892915 639527734335660507671839373)
          ·
            refine ⟨239822900375872690376939765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639527734335660507671839373 239822900375872690376939765)
            ·
              refine ⟨22483396910238064722838103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239822900375872690376939765 22483396910238064722838103)
              ·
                refine ⟨33725095365357097084257155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22483396910238064722838103 33725095365357097084257155)
                ·
                  refine ⟨50587643048035645626385733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33725095365357097084257155 50587643048035645626385733)
                  ·
                    refine ⟨9485183071506683554947325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50587643048035645626385733 9485183071506683554947325)
                    ·
                      refine ⟨3556943651815006333105247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485183071506683554947325 3556943651815006333105247)
                      ·
                        rfl

theorem cell23_6927123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_6927123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927123 prefixEnd_6927123 := by exact prefixLift 6927123
  have htrace : WordTrace (prefixWord ++ tailWord_6927123) baseStart_6927123 baseEnd_6927123 := by
    simpa [prefixWord, tailWord_6927123, baseEnd_6927123] using wordTrace_append hprefix tailTrace_6927123
  have hstable : (prefixWord ++ tailWord_6927123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927123).length < 2 ^ (prefixWord ++ tailWord_6927123).sum := by decide
  have hdescent : baseEnd_6927123 < baseStart_6927123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927160 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 6]
def baseStart_6927160 : Nat := 118140960795 + 6927160 * 2 ^ 59
def prefixEnd_6927160 : Nat := 4983230072969 + 3 ^ 40 * 6927160 * 2
def baseEnd_6927160 : Nat := 395218072288802520926953

theorem tailTrace_6927160 : CollatzResearch.WordTrace tailWord_6927160 prefixEnd_6927160 395218072288802520926953 := by
  unfold tailWord_6927160
  simp only [CollatzResearch.WordTrace]
  refine ⟨126327140792044929792257467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168436187722726573056343289 126327140792044929792257467)
  ·
    refine ⟨189490711188067394688386201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126327140792044929792257467 189490711188067394688386201)
    ·
      refine ⟨142118033391050546016289651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189490711188067394688386201 142118033391050546016289651)
      ·
        refine ⟨213177050086575819024434477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142118033391050546016289651 213177050086575819024434477)
        ·
          refine ⟨79941393782465932134162929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213177050086575819024434477 79941393782465932134162929)
          ·
            refine ⟨59956045336849449100622197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79941393782465932134162929 59956045336849449100622197)
            ·
              refine ⟨5620879250329635853183331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59956045336849449100622197 5620879250329635853183331)
              ·
                refine ⟨8431318875494453779774997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620879250329635853183331 8431318875494453779774997)
                ·
                  refine ⟨395218072288802520926953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8431318875494453779774997 395218072288802520926953)
                  ·
                    rfl

theorem cell23_6927160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 6].length) (baseStart_6927160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927160 prefixEnd_6927160 := by exact prefixLift 6927160
  have htrace : WordTrace (prefixWord ++ tailWord_6927160) baseStart_6927160 baseEnd_6927160 := by
    simpa [prefixWord, tailWord_6927160, baseEnd_6927160] using wordTrace_append hprefix tailTrace_6927160
  have hstable : (prefixWord ++ tailWord_6927160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927160).length < 2 ^ (prefixWord ++ tailWord_6927160).sum := by decide
  have hdescent : baseEnd_6927160 < baseStart_6927160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927204 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_6927204 : Nat := 118140960795 + 6927204 * 2 ^ 59
def prefixEnd_6927204 : Nat := 4983230072969 + 3 ^ 40 * 6927204 * 2
def baseEnd_6927204 : Nat := 3556985243748020516192375

theorem tailTrace_6927204 : CollatzResearch.WordTrace tailWord_6927204 prefixEnd_6927204 3556985243748020516192375 := by
  unfold tailWord_6927204
  simp only [CollatzResearch.WordTrace]
  refine ⟨126327943197965227549558333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168437257597286970066077777 126327943197965227549558333)
  ·
    refine ⟨47372978699236960331084375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126327943197965227549558333 47372978699236960331084375)
    ·
      refine ⟨71059468048855440496626563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47372978699236960331084375 71059468048855440496626563)
      ·
        refine ⟨106589202073283160744939845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71059468048855440496626563 106589202073283160744939845)
        ·
          refine ⟨19985475388740592639676221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106589202073283160744939845 19985475388740592639676221)
          ·
            refine ⟨7494553270777722239878583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19985475388740592639676221 7494553270777722239878583)
            ·
              refine ⟨11241829906166583359817875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7494553270777722239878583 11241829906166583359817875)
              ·
                refine ⟨16862744859249875039726813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11241829906166583359817875 16862744859249875039726813)
                ·
                  refine ⟨6323529322218703139897555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16862744859249875039726813 6323529322218703139897555)
                  ·
                    refine ⟨9485293983328054709846333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6323529322218703139897555 9485293983328054709846333)
                    ·
                      refine ⟨3556985243748020516192375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485293983328054709846333 3556985243748020516192375)
                      ·
                        rfl

theorem cell23_6927204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_6927204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927204 prefixEnd_6927204 := by exact prefixLift 6927204
  have htrace : WordTrace (prefixWord ++ tailWord_6927204) baseStart_6927204 baseEnd_6927204 := by
    simpa [prefixWord, tailWord_6927204, baseEnd_6927204] using wordTrace_append hprefix tailTrace_6927204
  have hstable : (prefixWord ++ tailWord_6927204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927204).length < 2 ^ (prefixWord ++ tailWord_6927204).sum := by decide
  have hdescent : baseEnd_6927204 < baseStart_6927204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927223 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_6927223 : Nat := 118140960795 + 6927223 * 2 ^ 59
def prefixEnd_6927223 : Nat := 4983230072969 + 3 ^ 40 * 6927223 * 2
def baseEnd_6927223 : Nat := 3556994999880455941854787

theorem tailTrace_6927223 : CollatzResearch.WordTrace tailWord_6927223 prefixEnd_6927223 3556994999880455941854787 := by
  unfold tailWord_6927223
  simp only [CollatzResearch.WordTrace]
  refine ⟨252656579382861621344058323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168437719588574414229372215 252656579382861621344058323)
  ·
    refine ⟨378984869074292432016087485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252656579382861621344058323 378984869074292432016087485)
    ·
      refine ⟨142119325902859662006032807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378984869074292432016087485 142119325902859662006032807)
      ·
        refine ⟨213178988854289493009049211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142119325902859662006032807 213178988854289493009049211)
        ·
          refine ⟨319768483281434239513573817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213178988854289493009049211 319768483281434239513573817)
          ·
            refine ⟨239826362461075679635180363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319768483281434239513573817 239826362461075679635180363)
            ·
              refine ⟨359739543691613519452770545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239826362461075679635180363 359739543691613519452770545)
              ·
                refine ⟨269804657768710139589577909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359739543691613519452770545 269804657768710139589577909)
                ·
                  refine ⟨25294186665816575586522929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269804657768710139589577909 25294186665816575586522929)
                  ·
                    refine ⟨18970639999362431689892197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25294186665816575586522929 18970639999362431689892197)
                    ·
                      refine ⟨3556994999880455941854787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18970639999362431689892197 3556994999880455941854787)
                      ·
                        rfl

theorem cell23_6927223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_6927223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927223 prefixEnd_6927223 := by exact prefixLift 6927223
  have htrace : WordTrace (prefixWord ++ tailWord_6927223) baseStart_6927223 baseEnd_6927223 := by
    simpa [prefixWord, tailWord_6927223, baseEnd_6927223] using wordTrace_append hprefix tailTrace_6927223
  have hstable : (prefixWord ++ tailWord_6927223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927223).length < 2 ^ (prefixWord ++ tailWord_6927223).sum := by decide
  have hdescent : baseEnd_6927223 < baseStart_6927223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927227 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 3, 2, 2]
def baseStart_6927227 : Nat := 118140960795 + 6927227 * 2 ^ 59
def prefixEnd_6927227 : Nat := 4983230072969 + 3 ^ 40 * 6927227 * 2
def baseEnd_6927227 : Nat := 3556997053803073926204769

theorem tailTrace_6927227 : CollatzResearch.WordTrace tailWord_6927227 prefixEnd_6927227 3556997053803073926204769 := by
  unfold tailWord_6927227
  simp only [CollatzResearch.WordTrace]
  refine ⟨252656725274847130027203935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168437816849898086684802623 252656725274847130027203935)
  ·
    refine ⟨378985087912270695040805903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252656725274847130027203935 378985087912270695040805903)
    ·
      refine ⟨568477631868406042561208855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378985087912270695040805903 568477631868406042561208855)
      ·
        refine ⟨852716447802609063841813283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568477631868406042561208855 852716447802609063841813283)
        ·
          refine ⟨1279074671703913595762719925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852716447802609063841813283 1279074671703913595762719925)
          ·
            refine ⟨119913250472241899602754993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1279074671703913595762719925 119913250472241899602754993)
            ·
              refine ⟨89934937854181424702066245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119913250472241899602754993 89934937854181424702066245)
              ·
                refine ⟨16862800847659017131637421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89934937854181424702066245 16862800847659017131637421)
                ·
                  refine ⟨6323550317872131424364033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16862800847659017131637421 6323550317872131424364033)
                  ·
                    refine ⟨4742662738404098568273025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323550317872131424364033 4742662738404098568273025)
                    ·
                      refine ⟨3556997053803073926204769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742662738404098568273025 3556997053803073926204769)
                      ·
                        rfl

theorem cell23_6927227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2, 2].length) (baseStart_6927227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927227 prefixEnd_6927227 := by exact prefixLift 6927227
  have htrace : WordTrace (prefixWord ++ tailWord_6927227) baseStart_6927227 baseEnd_6927227 := by
    simpa [prefixWord, tailWord_6927227, baseEnd_6927227] using wordTrace_append hprefix tailTrace_6927227
  have hstable : (prefixWord ++ tailWord_6927227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927227).length < 2 ^ (prefixWord ++ tailWord_6927227).sum := by decide
  have hdescent : baseEnd_6927227 < baseStart_6927227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927240 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6927240 : Nat := 118140960795 + 6927240 * 2 ^ 59
def prefixEnd_6927240 : Nat := 4983230072969 + 3 ^ 40 * 6927240 * 2
def baseEnd_6927240 : Nat := 3557003729051582375342209

theorem tailTrace_6927240 : CollatzResearch.WordTrace tailWord_6927240 prefixEnd_6927240 3557003729051582375342209 := by
  unfold tailWord_6927240
  simp only [CollatzResearch.WordTrace]
  refine ⟨126328599711900016623713587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168438132949200022164951449 126328599711900016623713587)
  ·
    refine ⟨189492899567850024935570381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126328599711900016623713587 189492899567850024935570381)
    ·
      refine ⟨71059837337943759350838893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189492899567850024935570381 71059837337943759350838893)
      ·
        refine ⟨26647439001728909756564585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71059837337943759350838893 26647439001728909756564585)
        ·
          refine ⟨19985579251296682317423439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26647439001728909756564585 19985579251296682317423439)
          ·
            refine ⟨29978368876945023476135159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19985579251296682317423439 29978368876945023476135159)
            ·
              refine ⟨44967553315417535214202739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29978368876945023476135159 44967553315417535214202739)
              ·
                refine ⟨67451329973126302821304109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44967553315417535214202739 67451329973126302821304109)
                ·
                  refine ⟨25294248739922363557989041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67451329973126302821304109 25294248739922363557989041)
                  ·
                    refine ⟨18970686554941772668491781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25294248739922363557989041 18970686554941772668491781)
                    ·
                      refine ⟨3557003729051582375342209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18970686554941772668491781 3557003729051582375342209)
                      ·
                        rfl

theorem cell23_6927240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6927240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927240 prefixEnd_6927240 := by exact prefixLift 6927240
  have htrace : WordTrace (prefixWord ++ tailWord_6927240) baseStart_6927240 baseEnd_6927240 := by
    simpa [prefixWord, tailWord_6927240, baseEnd_6927240] using wordTrace_append hprefix tailTrace_6927240
  have hstable : (prefixWord ++ tailWord_6927240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927240).length < 2 ^ (prefixWord ++ tailWord_6927240).sum := by decide
  have hdescent : baseEnd_6927240 < baseStart_6927240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927250 : List Nat := [3, 2, 3, 2, 2, 11]
def baseStart_6927250 : Nat := 118140960795 + 6927250 * 2 ^ 59
def prefixEnd_6927250 : Nat := 4983230072969 + 3 ^ 40 * 6927250 * 2
def baseEnd_6927250 : Nat := 14637896559086943770441

theorem tailTrace_6927250 : CollatzResearch.WordTrace tailWord_6927250 prefixEnd_6927250 14637896559086943770441 := by
  unfold tailWord_6927250
  simp only [CollatzResearch.WordTrace]
  refine ⟨63164391038440951238822801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168438376102509203303527469 63164391038440951238822801)
  ·
    refine ⟨47373293278830713429117101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63164391038440951238822801 47373293278830713429117101)
    ·
      refine ⟨17764984979561517535918913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47373293278830713429117101 17764984979561517535918913)
      ·
        refine ⟨13323738734671138151939185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17764984979561517535918913 13323738734671138151939185)
        ·
          refine ⟨9992804051003353613954389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13323738734671138151939185 9992804051003353613954389)
          ·
            refine ⟨14637896559086943770441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9992804051003353613954389 14637896559086943770441)
            ·
              rfl

theorem cell23_6927250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 11].length) (baseStart_6927250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927250 prefixEnd_6927250 := by exact prefixLift 6927250
  have htrace : WordTrace (prefixWord ++ tailWord_6927250) baseStart_6927250 baseEnd_6927250 := by
    simpa [prefixWord, tailWord_6927250, baseEnd_6927250] using wordTrace_append hprefix tailTrace_6927250
  have hstable : (prefixWord ++ tailWord_6927250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927250).length < 2 ^ (prefixWord ++ tailWord_6927250).sum := by decide
  have hdescent : baseEnd_6927250 < baseStart_6927250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927261 : List Nat := [1, 4, 2, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_6927261 : Nat := 118140960795 + 6927261 * 2 ^ 59
def prefixEnd_6927261 : Nat := 4983230072969 + 3 ^ 40 * 6927261 * 2
def baseEnd_6927261 : Nat := 3557014512145326793179613

theorem tailTrace_6927261 : CollatzResearch.WordTrace tailWord_6927261 prefixEnd_6927261 3557014512145326793179613 := by
  unfold tailWord_6927261
  simp only [CollatzResearch.WordTrace]
  refine ⟨252657965356723953833941637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168438643571149302555961091 252657965356723953833941637)
  ·
    refine ⟨47373368504385741343864057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252657965356723953833941637 47373368504385741343864057)
    ·
      refine ⟨35530026378289306007898043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47373368504385741343864057 35530026378289306007898043)
      ·
        refine ⟨53295039567433959011847065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35530026378289306007898043 53295039567433959011847065)
        ·
          refine ⟨39971279675575469258885299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53295039567433959011847065 39971279675575469258885299)
          ·
            refine ⟨59956919513363203888327949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39971279675575469258885299 59956919513363203888327949)
            ·
              refine ⟨22483844817511201458122981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59956919513363203888327949 22483844817511201458122981)
              ·
                refine ⟨4215720903283350273398059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22483844817511201458122981 4215720903283350273398059)
                ·
                  refine ⟨6323581354925025410097089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215720903283350273398059 6323581354925025410097089)
                  ·
                    refine ⟨4742686016193769057572817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323581354925025410097089 4742686016193769057572817)
                    ·
                      refine ⟨3557014512145326793179613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742686016193769057572817 3557014512145326793179613)
                      ·
                        rfl

theorem cell23_6927261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_6927261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927261 prefixEnd_6927261 := by exact prefixLift 6927261
  have htrace : WordTrace (prefixWord ++ tailWord_6927261) baseStart_6927261 baseEnd_6927261 := by
    simpa [prefixWord, tailWord_6927261, baseEnd_6927261] using wordTrace_append hprefix tailTrace_6927261
  have hstable : (prefixWord ++ tailWord_6927261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927261).length < 2 ^ (prefixWord ++ tailWord_6927261).sum := by decide
  have hdescent : baseEnd_6927261 < baseStart_6927261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927284 : List Nat := [2, 5, 2, 1, 1, 2, 3, 7]
def baseStart_6927284 : Nat := 118140960795 + 6927284 * 2 ^ 59
def prefixEnd_6927284 : Nat := 4983230072969 + 3 ^ 40 * 6927284 * 2
def baseEnd_6927284 : Nat := 131741715637051118636741

theorem tailTrace_6927284 : CollatzResearch.WordTrace tailWord_6927284 prefixEnd_6927284 131741715637051118636741 := by
  unfold tailWord_6927284
  simp only [CollatzResearch.WordTrace]
  refine ⟨126329402117820314381014453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168439202823760419174685937 126329402117820314381014453)
  ·
    refine ⟨11843381448545654473220105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126329402117820314381014453 11843381448545654473220105)
    ·
      refine ⟨8882536086409240854915079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11843381448545654473220105 8882536086409240854915079)
      ·
        refine ⟨13323804129613861282372619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8882536086409240854915079 13323804129613861282372619)
        ·
          refine ⟨19985706194420791923558929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13323804129613861282372619 19985706194420791923558929)
          ·
            refine ⟨14989279645815593942669197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19985706194420791923558929 14989279645815593942669197)
            ·
              refine ⟨5620979867180847728500949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14989279645815593942669197 5620979867180847728500949)
              ·
                refine ⟨131741715637051118636741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5620979867180847728500949 131741715637051118636741)
                ·
                  rfl

theorem cell23_6927284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 7].length) (baseStart_6927284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927284 prefixEnd_6927284 := by exact prefixLift 6927284
  have htrace : WordTrace (prefixWord ++ tailWord_6927284) baseStart_6927284 baseEnd_6927284 := by
    simpa [prefixWord, tailWord_6927284, baseEnd_6927284] using wordTrace_append hprefix tailTrace_6927284
  have hstable : (prefixWord ++ tailWord_6927284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927284).length < 2 ^ (prefixWord ++ tailWord_6927284).sum := by decide
  have hdescent : baseEnd_6927284 < baseStart_6927284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927287 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 3, 3, 2]
def baseStart_6927287 : Nat := 118140960795 + 6927287 * 2 ^ 59
def prefixEnd_6927287 : Nat := 4983230072969 + 3 ^ 40 * 6927287 * 2
def baseEnd_6927287 : Nat := 3557027862642343691454493

theorem tailTrace_6927287 : CollatzResearch.WordTrace tailWord_6927287 prefixEnd_6927287 3557027862642343691454493 := by
  unfold tailWord_6927287
  simp only [CollatzResearch.WordTrace]
  refine ⟨252658913654629760274388115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168439275769753173516258743 252658913654629760274388115)
  ·
    refine ⟨378988370481944640411582173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252658913654629760274388115 378988370481944640411582173)
    ·
      refine ⟨142120638930729240154343315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 378988370481944640411582173 142120638930729240154343315)
      ·
        refine ⟨213180958396093860231514973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142120638930729240154343315 213180958396093860231514973)
        ·
          refine ⟨79942859398535197586818115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213180958396093860231514973 79942859398535197586818115)
          ·
            refine ⟨119914289097802796380227173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79942859398535197586818115 119914289097802796380227173)
            ·
              refine ⟨22483929205838024321292595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119914289097802796380227173 22483929205838024321292595)
              ·
                refine ⟨33725893808757036481938893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22483929205838024321292595 33725893808757036481938893)
                ·
                  refine ⟨12647210178283888680727085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33725893808757036481938893 12647210178283888680727085)
                  ·
                    refine ⟨4742703816856458255272657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12647210178283888680727085 4742703816856458255272657)
                    ·
                      refine ⟨3557027862642343691454493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742703816856458255272657 3557027862642343691454493)
                      ·
                        rfl

theorem cell23_6927287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3, 2].length) (baseStart_6927287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927287 prefixEnd_6927287 := by exact prefixLift 6927287
  have htrace : WordTrace (prefixWord ++ tailWord_6927287) baseStart_6927287 baseEnd_6927287 := by
    simpa [prefixWord, tailWord_6927287, baseEnd_6927287] using wordTrace_append hprefix tailTrace_6927287
  have hstable : (prefixWord ++ tailWord_6927287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927287).length < 2 ^ (prefixWord ++ tailWord_6927287).sum := by decide
  have hdescent : baseEnd_6927287 < baseStart_6927287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927310 : List Nat := [4, 1, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_6927310 : Nat := 118140960795 + 6927310 * 2 ^ 59
def prefixEnd_6927310 : Nat := 4983230072969 + 3 ^ 40 * 6927310 * 2
def baseEnd_6927310 : Nat := 1185679890899132367155629

theorem tailTrace_6927310 : CollatzResearch.WordTrace tailWord_6927310 prefixEnd_6927310 1185679890899132367155629 := by
  unfold tailWord_6927310
  simp only [CollatzResearch.WordTrace]
  refine ⟨31582469066693304400309423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168439835022364290134983589 31582469066693304400309423)
  ·
    refine ⟨47373703600039956600464135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31582469066693304400309423 47373703600039956600464135)
    ·
      refine ⟨71060555400059934900696203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47373703600039956600464135 71060555400059934900696203)
      ·
        refine ⟨106590833100089902351044305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71060555400059934900696203 106590833100089902351044305)
        ·
          refine ⟨79943124825067426763283229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106590833100089902351044305 79943124825067426763283229)
          ·
            refine ⟨29978671809400285036231211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79943124825067426763283229 29978671809400285036231211)
            ·
              refine ⟨44968007714100427554346817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29978671809400285036231211 44968007714100427554346817)
              ·
                refine ⟨33726005785575320665760113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44968007714100427554346817 33726005785575320665760113)
                ·
                  refine ⟨25294504339181490499320085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33726005785575320665760113 25294504339181490499320085)
                  ·
                    refine ⟨1185679890899132367155629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25294504339181490499320085 1185679890899132367155629)
                    ·
                      rfl

theorem cell23_6927310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_6927310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927310 prefixEnd_6927310 := by exact prefixLift 6927310
  have htrace : WordTrace (prefixWord ++ tailWord_6927310) baseStart_6927310 baseEnd_6927310 := by
    simpa [prefixWord, tailWord_6927310, baseEnd_6927310] using wordTrace_append hprefix tailTrace_6927310
  have hstable : (prefixWord ++ tailWord_6927310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927310).length < 2 ^ (prefixWord ++ tailWord_6927310).sum := by decide
  have hdescent : baseEnd_6927310 < baseStart_6927310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927427 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3]
def baseStart_6927427 : Nat := 118140960795 + 6927427 * 2 ^ 59
def prefixEnd_6927427 : Nat := 4983230072969 + 3 ^ 40 * 6927427 * 2
def baseEnd_6927427 : Nat := 3557099749933973143703849

theorem tailTrace_6927427 : CollatzResearch.WordTrace tailWord_6927427 prefixEnd_6927427 3557099749933973143703849 := by
  unfold tailWord_6927427
  simp only [CollatzResearch.WordTrace]
  refine ⟨252664019874122564184484535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168442679916081709456323023 252664019874122564184484535)
  ·
    refine ⟨378996029811183846276726803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252664019874122564184484535 378996029811183846276726803)
    ·
      refine ⟨568494044716775769415090205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378996029811183846276726803 568494044716775769415090205)
      ·
        refine ⟨213185266768790913530658827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568494044716775769415090205 213185266768790913530658827)
        ·
          refine ⟨319777900153186370295988241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213185266768790913530658827 319777900153186370295988241)
          ·
            refine ⟨239833425114889777721991181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319777900153186370295988241 239833425114889777721991181)
            ·
              refine ⟨89937534418083666645746693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239833425114889777721991181 89937534418083666645746693)
              ·
                refine ⟨16863287703390687496077505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89937534418083666645746693 16863287703390687496077505)
                ·
                  refine ⟨12647465777543015622058129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16863287703390687496077505 12647465777543015622058129)
                  ·
                    refine ⟨9485599333157261716543597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12647465777543015622058129 9485599333157261716543597)
                    ·
                      refine ⟨3557099749933973143703849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485599333157261716543597 3557099749933973143703849)
                      ·
                        rfl

theorem cell23_6927427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_6927427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927427 prefixEnd_6927427 := by exact prefixLift 6927427
  have htrace : WordTrace (prefixWord ++ tailWord_6927427) baseStart_6927427 baseEnd_6927427 := by
    simpa [prefixWord, tailWord_6927427, baseEnd_6927427] using wordTrace_append hprefix tailTrace_6927427
  have hstable : (prefixWord ++ tailWord_6927427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927427).length < 2 ^ (prefixWord ++ tailWord_6927427).sum := by decide
  have hdescent : baseEnd_6927427 < baseStart_6927427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927450 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_6927450 : Nat := 118140960795 + 6927450 * 2 ^ 59
def prefixEnd_6927450 : Nat := 4983230072969 + 3 ^ 40 * 6927450 * 2
def baseEnd_6927450 : Nat := 3557111559989026553716243

theorem tailTrace_6927450 : CollatzResearch.WordTrace tailWord_6927450 prefixEnd_6927450 3557111559989026553716243 := by
  unfold tailWord_6927450
  simp only [CollatzResearch.WordTrace]
  refine ⟨63166214688259809778142951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168443239168692826075047869 63166214688259809778142951)
  ·
    refine ⟨94749322032389714667214427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63166214688259809778142951 94749322032389714667214427)
    ·
      refine ⟨142123983048584572000821641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94749322032389714667214427 142123983048584572000821641)
      ·
        refine ⟨106592987286438429000616231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142123983048584572000821641 106592987286438429000616231)
        ·
          refine ⟨159889480929657643500924347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106592987286438429000616231 159889480929657643500924347)
          ·
            refine ⟨239834221394486465251386521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159889480929657643500924347 239834221394486465251386521)
            ·
              refine ⟨179875666045864848938539891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239834221394486465251386521 179875666045864848938539891)
              ·
                refine ⟨269813499068797273407809837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179875666045864848938539891 269813499068797273407809837)
                ·
                  refine ⟨101180062150798977527928689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 269813499068797273407809837 101180062150798977527928689)
                  ·
                    refine ⟨75885046613099233145946517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101180062150798977527928689 75885046613099233145946517)
                    ·
                      refine ⟨3557111559989026553716243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75885046613099233145946517 3557111559989026553716243)
                      ·
                        rfl

theorem cell23_6927450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_6927450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927450 prefixEnd_6927450 := by exact prefixLift 6927450
  have htrace : WordTrace (prefixWord ++ tailWord_6927450) baseStart_6927450 baseEnd_6927450 := by
    simpa [prefixWord, tailWord_6927450, baseEnd_6927450] using wordTrace_append hprefix tailTrace_6927450
  have hstable : (prefixWord ++ tailWord_6927450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927450).length < 2 ^ (prefixWord ++ tailWord_6927450).sum := by decide
  have hdescent : baseEnd_6927450 < baseStart_6927450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927474 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_6927474 : Nat := 118140960795 + 6927474 * 2 ^ 59
def prefixEnd_6927474 : Nat := 4983230072969 + 3 ^ 40 * 6927474 * 2
def baseEnd_6927474 : Nat := 3557123883524734459816133

theorem tailTrace_6927474 : CollatzResearch.WordTrace tailWord_6927474 prefixEnd_6927474 3557123883524734459816133 := by
  unfold tailWord_6927474
  simp only [CollatzResearch.WordTrace]
  refine ⟨63166433526238072802861369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168443822736634860807630317 63166433526238072802861369)
  ·
    refine ⟨47374825144678554602146027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63166433526238072802861369 47374825144678554602146027)
    ·
      refine ⟨71062237717017831903219041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47374825144678554602146027 71062237717017831903219041)
      ·
        refine ⟨53296678287763373927414281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71062237717017831903219041 53296678287763373927414281)
        ·
          refine ⟨39972508715822530445560711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53296678287763373927414281 39972508715822530445560711)
          ·
            refine ⟨59958763073733795668341067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39972508715822530445560711 59958763073733795668341067)
            ·
              refine ⟨89938144610600693502511601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59958763073733795668341067 89938144610600693502511601)
              ·
                refine ⟨67453608457950520126883701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89938144610600693502511601 67453608457950520126883701)
                ·
                  refine ⟨6323775792932861261895347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67453608457950520126883701 6323775792932861261895347)
                  ·
                    refine ⟨9485663689399291892843021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6323775792932861261895347 9485663689399291892843021)
                    ·
                      refine ⟨3557123883524734459816133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485663689399291892843021 3557123883524734459816133)
                      ·
                        rfl

theorem cell23_6927474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_6927474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927474 prefixEnd_6927474 := by exact prefixLift 6927474
  have htrace : WordTrace (prefixWord ++ tailWord_6927474) baseStart_6927474 baseEnd_6927474 := by
    simpa [prefixWord, tailWord_6927474, baseEnd_6927474] using wordTrace_append hprefix tailTrace_6927474
  have hstable : (prefixWord ++ tailWord_6927474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927474).length < 2 ^ (prefixWord ++ tailWord_6927474).sum := by decide
  have hdescent : baseEnd_6927474 < baseStart_6927474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927481 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 6]
def baseStart_6927481 : Nat := 118140960795 + 6927481 * 2 ^ 59
def prefixEnd_6927481 : Nat := 4983230072969 + 3 ^ 40 * 6927481 * 2
def baseEnd_6927481 : Nat := 395236386432146214714289

theorem tailTrace_6927481 : CollatzResearch.WordTrace tailWord_6927481 prefixEnd_6927481 395236386432146214714289 := by
  unfold tailWord_6927481
  simp only [CollatzResearch.WordTrace]
  refine ⟨252665989415926931406950297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168443992943951287604633531 252665989415926931406950297)
  ·
    refine ⟨189499492061945198555212723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252665989415926931406950297 189499492061945198555212723)
    ·
      refine ⟨284249238092917797832819085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189499492061945198555212723 284249238092917797832819085)
      ·
        refine ⟨106593464284844174187307157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284249238092917797832819085 106593464284844174187307157)
        ·
          refine ⟨4996568638352070665030023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106593464284844174187307157 4996568638352070665030023)
          ·
            refine ⟨7494852957528105997545035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996568638352070665030023 7494852957528105997545035)
            ·
              refine ⟨11242279436292158996317553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7494852957528105997545035 11242279436292158996317553)
              ·
                refine ⟨8431709577219119247238165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11242279436292158996317553 8431709577219119247238165)
                ·
                  refine ⟨395236386432146214714289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8431709577219119247238165 395236386432146214714289)
                  ·
                    rfl

theorem cell23_6927481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 6].length) (baseStart_6927481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927481 prefixEnd_6927481 := by exact prefixLift 6927481
  have htrace : WordTrace (prefixWord ++ tailWord_6927481) baseStart_6927481 baseEnd_6927481 := by
    simpa [prefixWord, tailWord_6927481, baseEnd_6927481] using wordTrace_append hprefix tailTrace_6927481
  have hstable : (prefixWord ++ tailWord_6927481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927481).length < 2 ^ (prefixWord ++ tailWord_6927481).sum := by decide
  have hdescent : baseEnd_6927481 < baseStart_6927481 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927484 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 4, 3, 2]
def baseStart_6927484 : Nat := 118140960795 + 6927484 * 2 ^ 59
def prefixEnd_6927484 : Nat := 4983230072969 + 3 ^ 40 * 6927484 * 2
def baseEnd_6927484 : Nat := 3557129018331279420691087

theorem tailTrace_6927484 : CollatzResearch.WordTrace tailWord_6927484 prefixEnd_6927484 3557129018331279420691087 := by
  unfold tailWord_6927484
  simp only [CollatzResearch.WordTrace]
  refine ⟨126333049417458031459654753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168444065889944041946206337 126333049417458031459654753)
  ·
    refine ⟨94749787063093523594741065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126333049417458031459654753 94749787063093523594741065)
    ·
      refine ⟨71062340297320142696055799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94749787063093523594741065 71062340297320142696055799)
      ·
        refine ⟨106593510445980214044083699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71062340297320142696055799 106593510445980214044083699)
        ·
          refine ⟨159890265668970321066125549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106593510445980214044083699 159890265668970321066125549)
          ·
            refine ⟨59958849625863870399797081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159890265668970321066125549 59958849625863870399797081)
            ·
              refine ⟨44969137219397902799847811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59958849625863870399797081 44969137219397902799847811)
              ·
                refine ⟨67453705829096854199771717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44969137219397902799847811 67453705829096854199771717)
                ·
                  refine ⟨12647569842955660162457197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67453705829096854199771717 12647569842955660162457197)
                  ·
                    refine ⟨4742838691108372560921449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12647569842955660162457197 4742838691108372560921449)
                    ·
                      refine ⟨3557129018331279420691087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742838691108372560921449 3557129018331279420691087)
                      ·
                        rfl

theorem cell23_6927484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 3, 2].length) (baseStart_6927484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927484 prefixEnd_6927484 := by exact prefixLift 6927484
  have htrace : WordTrace (prefixWord ++ tailWord_6927484) baseStart_6927484 baseEnd_6927484 := by
    simpa [prefixWord, tailWord_6927484, baseEnd_6927484] using wordTrace_append hprefix tailTrace_6927484
  have hstable : (prefixWord ++ tailWord_6927484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927484).length < 2 ^ (prefixWord ++ tailWord_6927484).sum := by decide
  have hdescent : baseEnd_6927484 < baseStart_6927484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927491 : List Nat := [1, 1, 1, 3, 3, 2, 1, 6, 1, 1, 3]
def baseStart_6927491 : Nat := 118140960795 + 6927491 * 2 ^ 59
def prefixEnd_6927491 : Nat := 4983230072969 + 3 ^ 40 * 6927491 * 2
def baseEnd_6927491 : Nat := 3557132612695860893303555

theorem tailTrace_6927491 : CollatzResearch.WordTrace tailWord_6927491 prefixEnd_6927491 3557132612695860893303555 := by
  unfold tailWord_6927491
  simp only [CollatzResearch.WordTrace]
  refine ⟨252666354145890703114814327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168444236097260468743209551 252666354145890703114814327)
  ·
    refine ⟨378999531218836054672221491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252666354145890703114814327 378999531218836054672221491)
    ·
      refine ⟨568499296828254082008332237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 378999531218836054672221491 568499296828254082008332237)
      ·
        refine ⟨213187236310595280753124589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568499296828254082008332237 213187236310595280753124589)
        ·
          refine ⟨79945213616473230282421721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213187236310595280753124589 79945213616473230282421721)
          ·
            refine ⟨59958910212354922711816291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79945213616473230282421721 59958910212354922711816291)
            ·
              refine ⟨89938365318532384067724437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59958910212354922711816291 89938365318532384067724437)
              ·
                refine ⟨4215860874306205503174583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89938365318532384067724437 4215860874306205503174583)
                ·
                  refine ⟨6323791311459308254761875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215860874306205503174583 6323791311459308254761875)
                  ·
                    refine ⟨9485686967188962382142813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6323791311459308254761875 9485686967188962382142813)
                    ·
                      refine ⟨3557132612695860893303555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485686967188962382142813 3557132612695860893303555)
                      ·
                        rfl

theorem cell23_6927491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 6, 1, 1, 3].length) (baseStart_6927491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927491 prefixEnd_6927491 := by exact prefixLift 6927491
  have htrace : WordTrace (prefixWord ++ tailWord_6927491) baseStart_6927491 baseEnd_6927491 := by
    simpa [prefixWord, tailWord_6927491, baseEnd_6927491] using wordTrace_append hprefix tailTrace_6927491
  have hstable : (prefixWord ++ tailWord_6927491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927491).length < 2 ^ (prefixWord ++ tailWord_6927491).sum := by decide
  have hdescent : baseEnd_6927491 < baseStart_6927491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927507 : List Nat := [1, 1, 1, 2, 1, 2, 7, 1, 1, 6]
def baseStart_6927507 : Nat := 118140960795 + 6927507 * 2 ^ 59
def prefixEnd_6927507 : Nat := 4983230072969 + 3 ^ 40 * 6927507 * 2
def baseEnd_6927507 : Nat := 1185713609462110943567827

theorem tailTrace_6927507 : CollatzResearch.WordTrace tailWord_6927507 prefixEnd_6927507 1185713609462110943567827 := by
  unfold tailWord_6927507
  simp only [CollatzResearch.WordTrace]
  refine ⟨252666937713832737847396775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168444625142555158564931183 252666937713832737847396775)
  ·
    refine ⟨379000406570749106771095163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252666937713832737847396775 379000406570749106771095163)
    ·
      refine ⟨568500609856123660156642745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379000406570749106771095163 568500609856123660156642745)
      ·
        refine ⟨426375457392092745117482059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568500609856123660156642745 426375457392092745117482059)
        ·
          refine ⟨639563186088139117676223089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426375457392092745117482059 639563186088139117676223089)
          ·
            refine ⟨479672389566104338257167317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639563186088139117676223089 479672389566104338257167317)
            ·
              refine ⟨11242321630455570427902359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 479672389566104338257167317 11242321630455570427902359)
              ·
                refine ⟨16863482445683355641853539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242321630455570427902359 16863482445683355641853539)
                ·
                  refine ⟨25295223668525033462780309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16863482445683355641853539 25295223668525033462780309)
                  ·
                    refine ⟨1185713609462110943567827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25295223668525033462780309 1185713609462110943567827)
                    ·
                      rfl

theorem cell23_6927507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 6].length) (baseStart_6927507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927507 prefixEnd_6927507 := by exact prefixLift 6927507
  have htrace : WordTrace (prefixWord ++ tailWord_6927507) baseStart_6927507 baseEnd_6927507 := by
    simpa [prefixWord, tailWord_6927507, baseEnd_6927507] using wordTrace_append hprefix tailTrace_6927507
  have hstable : (prefixWord ++ tailWord_6927507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927507).length < 2 ^ (prefixWord ++ tailWord_6927507).sum := by decide
  have hdescent : baseEnd_6927507 < baseStart_6927507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927517 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_6927517 : Nat := 118140960795 + 6927517 * 2 ^ 59
def prefixEnd_6927517 : Nat := 4983230072969 + 3 ^ 40 * 6927517 * 2
def baseEnd_6927517 : Nat := 3557145963192877791578435

theorem tailTrace_6927517 : CollatzResearch.WordTrace tailWord_6927517 prefixEnd_6927517 3557145963192877791578435 := by
  unfold tailWord_6927517
  simp only [CollatzResearch.WordTrace]
  refine ⟨252667302443796509555260805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168444868295864339703507203 252667302443796509555260805)
  ·
    refine ⟨47375119208211845541611401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252667302443796509555260805 47375119208211845541611401)
    ·
      refine ⟨35531339406158884156208551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47375119208211845541611401 35531339406158884156208551)
      ·
        refine ⟨53297009109238326234312827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35531339406158884156208551 53297009109238326234312827)
        ·
          refine ⟨79945513663857489351469241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53297009109238326234312827 79945513663857489351469241)
          ·
            refine ⟨59959135247893117013601931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79945513663857489351469241 59959135247893117013601931)
            ·
              refine ⟨89938702871839675520402897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59959135247893117013601931 89938702871839675520402897)
              ·
                refine ⟨67454027153879756640302173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89938702871839675520402897 67454027153879756640302173)
                ·
                  refine ⟨25295260182704908740113315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67454027153879756640302173 25295260182704908740113315)
                  ·
                    refine ⟨37942890274057363110169973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25295260182704908740113315 37942890274057363110169973)
                    ·
                      refine ⟨3557145963192877791578435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37942890274057363110169973 3557145963192877791578435)
                      ·
                        rfl

theorem cell23_6927517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_6927517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927517 prefixEnd_6927517 := by exact prefixLift 6927517
  have htrace : WordTrace (prefixWord ++ tailWord_6927517) baseStart_6927517 baseEnd_6927517 := by
    simpa [prefixWord, tailWord_6927517, baseEnd_6927517] using wordTrace_append hprefix tailTrace_6927517
  have hstable : (prefixWord ++ tailWord_6927517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927517).length < 2 ^ (prefixWord ++ tailWord_6927517).sum := by decide
  have hdescent : baseEnd_6927517 < baseStart_6927517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927524 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_6927524 : Nat := 118140960795 + 6927524 * 2 ^ 59
def prefixEnd_6927524 : Nat := 4983230072969 + 3 ^ 40 * 6927524 * 2
def baseEnd_6927524 : Nat := 1185716519185819754730301

theorem tailTrace_6927524 : CollatzResearch.WordTrace tailWord_6927524 prefixEnd_6927524 1185716519185819754730301 := by
  unfold tailWord_6927524
  simp only [CollatzResearch.WordTrace]
  refine ⟨126333778877385574875382813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168445038503180766500510417 126333778877385574875382813)
  ·
    refine ⟨47375167079019590578268555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126333778877385574875382813 47375167079019590578268555)
    ·
      refine ⟨71062750618529385867402833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47375167079019590578268555 71062750618529385867402833)
      ·
        refine ⟨53297062963897039400552125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71062750618529385867402833 53297062963897039400552125)
        ·
          refine ⟨19986398611461389775207047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53297062963897039400552125 19986398611461389775207047)
          ·
            refine ⟨29979597917192084662810571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19986398611461389775207047 29979597917192084662810571)
            ·
              refine ⟨44969396875788126994215857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29979597917192084662810571 44969396875788126994215857)
              ·
                refine ⟨33727047656841095245661893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44969396875788126994215857 33727047656841095245661893)
                ·
                  refine ⟨6323821435657705358561605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33727047656841095245661893 6323821435657705358561605)
                  ·
                    refine ⟨1185716519185819754730301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6323821435657705358561605 1185716519185819754730301)
                    ·
                      rfl

theorem cell23_6927524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_6927524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927524 prefixEnd_6927524 := by exact prefixLift 6927524
  have htrace : WordTrace (prefixWord ++ tailWord_6927524) baseStart_6927524 baseEnd_6927524 := by
    simpa [prefixWord, tailWord_6927524, baseEnd_6927524] using wordTrace_append hprefix tailTrace_6927524
  have hstable : (prefixWord ++ tailWord_6927524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927524).length < 2 ^ (prefixWord ++ tailWord_6927524).sum := by decide
  have hdescent : baseEnd_6927524 < baseStart_6927524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927537 : List Nat := [1, 2, 2, 5, 1, 1, 11]
def baseStart_6927537 : Nat := 118140960795 + 6927537 * 2 ^ 59
def prefixEnd_6927537 : Nat := 4983230072969 + 3 ^ 40 * 6927537 * 2
def baseEnd_6927537 : Nat := 43915509046987255720103

theorem tailTrace_6927537 : CollatzResearch.WordTrace tailWord_6927537 prefixEnd_6927537 43915509046987255720103 := by
  unfold tailWord_6927537
  simp only [CollatzResearch.WordTrace]
  refine ⟨252668031903724052970988865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168445354602482701980659243 252668031903724052970988865)
  ·
    refine ⟨189501023927793039728241649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252668031903724052970988865 189501023927793039728241649)
    ·
      refine ⟨142125767945844779796181237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189501023927793039728241649 142125767945844779796181237)
      ·
        refine ⟨13324290744922948105891991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142125767945844779796181237 13324290744922948105891991)
        ·
          refine ⟨19986436117384422158837987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13324290744922948105891991 19986436117384422158837987)
          ·
            refine ⟨29979654176076633238256981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19986436117384422158837987 29979654176076633238256981)
            ·
              refine ⟨43915509046987255720103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29979654176076633238256981 43915509046987255720103)
              ·
                rfl

theorem cell23_6927537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 11].length) (baseStart_6927537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927537 prefixEnd_6927537 := by exact prefixLift 6927537
  have htrace : WordTrace (prefixWord ++ tailWord_6927537) baseStart_6927537 baseEnd_6927537 := by
    simpa [prefixWord, tailWord_6927537, baseEnd_6927537] using wordTrace_append hprefix tailTrace_6927537
  have hstable : (prefixWord ++ tailWord_6927537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927537).length < 2 ^ (prefixWord ++ tailWord_6927537).sum := by decide
  have hdescent : baseEnd_6927537 < baseStart_6927537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927542 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_6927542 : Nat := 118140960795 + 6927542 * 2 ^ 59
def prefixEnd_6927542 : Nat := 4983230072969 + 3 ^ 40 * 6927542 * 2
def baseEnd_6927542 : Nat := 3557158800209240193765821

theorem tailTrace_6927542 : CollatzResearch.WordTrace tailWord_6927542 prefixEnd_6927542 3557158800209240193765821 := by
  unfold tailWord_6927542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15791763391794121176557555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168445476179137292549947253 15791763391794121176557555)
  ·
    refine ⟨23687645087691181764836333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15791763391794121176557555 23687645087691181764836333)
    ·
      refine ⟨8882866907884193161813625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23687645087691181764836333 8882866907884193161813625)
      ·
        refine ⟨6662150180913144871360219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8882866907884193161813625 6662150180913144871360219)
        ·
          refine ⟨9993225271369717307040329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662150180913144871360219 9993225271369717307040329)
          ·
            refine ⟨7494918953527287980280247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9993225271369717307040329 7494918953527287980280247)
            ·
              refine ⟨11242378430290931970420371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7494918953527287980280247 11242378430290931970420371)
              ·
                refine ⟨16863567645436397955630557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242378430290931970420371 16863567645436397955630557)
                ·
                  refine ⟨6323837867038649233361459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16863567645436397955630557 6323837867038649233361459)
                  ·
                    refine ⟨9485756800557973850042189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6323837867038649233361459 9485756800557973850042189)
                    ·
                      refine ⟨3557158800209240193765821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485756800557973850042189 3557158800209240193765821)
                      ·
                        rfl

theorem cell23_6927542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_6927542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927542 prefixEnd_6927542 := by exact prefixLift 6927542
  have htrace : WordTrace (prefixWord ++ tailWord_6927542) baseStart_6927542 baseEnd_6927542 := by
    simpa [prefixWord, tailWord_6927542, baseEnd_6927542] using wordTrace_append hprefix tailTrace_6927542
  have hstable : (prefixWord ++ tailWord_6927542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927542).length < 2 ^ (prefixWord ++ tailWord_6927542).sum := by decide
  have hdescent : baseEnd_6927542 < baseStart_6927542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927547 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3]
def baseStart_6927547 : Nat := 118140960795 + 6927547 * 2 ^ 59
def prefixEnd_6927547 : Nat := 4983230072969 + 3 ^ 40 * 6927547 * 2
def baseEnd_6927547 : Nat := 3557161367612512674203297

theorem tailTrace_6927547 : CollatzResearch.WordTrace tailWord_6927547 prefixEnd_6927547 3557161367612512674203297 := by
  unfold tailWord_6927547
  simp only [CollatzResearch.WordTrace]
  refine ⟨252668396633687824678852895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168445597755791883119235263 252668396633687824678852895)
  ·
    refine ⟨379002594950531737018279343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252668396633687824678852895 379002594950531737018279343)
    ·
      refine ⟨568503892425797605527419015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379002594950531737018279343 568503892425797605527419015)
      ·
        refine ⟨852755838638696408291128523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568503892425797605527419015 852755838638696408291128523)
        ·
          refine ⟨1279133757958044612436692785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852755838638696408291128523 1279133757958044612436692785)
          ·
            refine ⟨959350318468533459327519589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1279133757958044612436692785 959350318468533459327519589)
            ·
              refine ⟨179878184712850023623909923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 959350318468533459327519589 179878184712850023623909923)
              ·
                refine ⟨269817277069275035435864885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179878184712850023623909923 269817277069275035435864885)
                ·
                  refine ⟨25295369725244534572112333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 269817277069275035435864885 25295369725244534572112333)
                  ·
                    refine ⟨9485763646966700464542125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25295369725244534572112333 9485763646966700464542125)
                    ·
                      refine ⟨3557161367612512674203297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9485763646966700464542125 3557161367612512674203297)
                      ·
                        rfl

theorem cell23_6927547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3].length) (baseStart_6927547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927547 prefixEnd_6927547 := by exact prefixLift 6927547
  have htrace : WordTrace (prefixWord ++ tailWord_6927547) baseStart_6927547 baseEnd_6927547 := by
    simpa [prefixWord, tailWord_6927547, baseEnd_6927547] using wordTrace_append hprefix tailTrace_6927547
  have hstable : (prefixWord ++ tailWord_6927547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927547).length < 2 ^ (prefixWord ++ tailWord_6927547).sum := by decide
  have hdescent : baseEnd_6927547 < baseStart_6927547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927548 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 3, 2, 2]
def baseStart_6927548 : Nat := 118140960795 + 6927548 * 2 ^ 59
def prefixEnd_6927548 : Nat := 4983230072969 + 3 ^ 40 * 6927548 * 2
def baseEnd_6927548 : Nat := 3557161881093167170290793

theorem tailTrace_6927548 : CollatzResearch.WordTrace tailWord_6927548 prefixEnd_6927548 3557161881093167170290793 := by
  unfold tailWord_6927548
  simp only [CollatzResearch.WordTrace]
  refine ⟨126334216553342100924819649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168445622071122801233092865 126334216553342100924819649)
  ·
    refine ⟨94750662415006575693614737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126334216553342100924819649 94750662415006575693614737)
    ·
      refine ⟨71062996811254931770211053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94750662415006575693614737 71062996811254931770211053)
      ·
        refine ⟨26648623804220599413829145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71062996811254931770211053 26648623804220599413829145)
        ·
          refine ⟨19986467853165449560371859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26648623804220599413829145 19986467853165449560371859)
          ·
            refine ⟨29979701779748174340557789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19986467853165449560371859 29979701779748174340557789)
            ·
              refine ⟨11242388167405565377709171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29979701779748174340557789 11242388167405565377709171)
              ·
                refine ⟨16863582251108348066563757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242388167405565377709171 16863582251108348066563757)
                ·
                  refine ⟨6323843344165630524961409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16863582251108348066563757 6323843344165630524961409)
                  ·
                    refine ⟨4742882508124222893721057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323843344165630524961409 4742882508124222893721057)
                    ·
                      refine ⟨3557161881093167170290793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742882508124222893721057 3557161881093167170290793)
                      ·
                        rfl

theorem cell23_6927548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_6927548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927548 prefixEnd_6927548 := by exact prefixLift 6927548
  have htrace : WordTrace (prefixWord ++ tailWord_6927548) baseStart_6927548 baseEnd_6927548 := by
    simpa [prefixWord, tailWord_6927548, baseEnd_6927548] using wordTrace_append hprefix tailTrace_6927548
  have hstable : (prefixWord ++ tailWord_6927548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927548).length < 2 ^ (prefixWord ++ tailWord_6927548).sum := by decide
  have hdescent : baseEnd_6927548 < baseStart_6927548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927599 : List Nat := [1, 1, 2, 1, 8, 1, 2, 2, 1, 2, 2]
def baseStart_6927599 : Nat := 118140960795 + 6927599 * 2 ^ 59
def prefixEnd_6927599 : Nat := 4983230072969 + 3 ^ 40 * 6927599 * 2
def baseEnd_6927599 : Nat := 3557188068606546470753059

theorem tailTrace_6927599 : CollatzResearch.WordTrace tailWord_6927599 prefixEnd_6927599 3557188068606546470753059 := by
  unfold tailWord_6927599
  simp only [CollatzResearch.WordTrace]
  refine ⟨252670293229499437559745851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168446862152999625039830567 252670293229499437559745851)
  ·
    refine ⟨379005439844249156339618777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252670293229499437559745851 379005439844249156339618777)
    ·
      refine ⟨284254079883186867254714083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379005439844249156339618777 284254079883186867254714083)
      ·
        refine ⟨426381119824780300882071125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284254079883186867254714083 426381119824780300882071125)
        ·
          refine ⟨4996653747946644150961771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 426381119824780300882071125 4996653747946644150961771)
          ·
            refine ⟨7494980621919966226442657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4996653747946644150961771 7494980621919966226442657)
            ·
              refine ⟨5621235466439974669831993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7494980621919966226442657 5621235466439974669831993)
              ·
                refine ⟨4215926599829981002373995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621235466439974669831993 4215926599829981002373995)
                ·
                  refine ⟨6323889899744971503560993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4215926599829981002373995 6323889899744971503560993)
                  ·
                    refine ⟨4742917424808728627670745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6323889899744971503560993 4742917424808728627670745)
                    ·
                      refine ⟨3557188068606546470753059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742917424808728627670745 3557188068606546470753059)
                      ·
                        rfl

theorem cell23_6927599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 2, 1, 2, 2].length) (baseStart_6927599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927599 prefixEnd_6927599 := by exact prefixLift 6927599
  have htrace : WordTrace (prefixWord ++ tailWord_6927599) baseStart_6927599 baseEnd_6927599 := by
    simpa [prefixWord, tailWord_6927599, baseEnd_6927599] using wordTrace_append hprefix tailTrace_6927599
  have hstable : (prefixWord ++ tailWord_6927599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927599).length < 2 ^ (prefixWord ++ tailWord_6927599).sum := by decide
  have hdescent : baseEnd_6927599 < baseStart_6927599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927614 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 1, 8]
def baseStart_6927614 : Nat := 118140960795 + 6927614 * 2 ^ 59
def prefixEnd_6927614 : Nat := 4983230072969 + 3 ^ 40 * 6927614 * 2
def baseEnd_6927614 : Nat := 1185731923605454637355163

theorem tailTrace_6927614 : CollatzResearch.WordTrace tailWord_6927614 prefixEnd_6927614 1185731923605454637355163 := by
  unfold tailWord_6927614
  simp only [CollatzResearch.WordTrace]
  refine ⟨31583855040555636890192737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168447226882963396747694597 31583855040555636890192737)
  ·
    refine ⟨23687891280416727667644553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31583855040555636890192737 23687891280416727667644553)
    ·
      refine ⟨17765918460312545750733415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23687891280416727667644553 17765918460312545750733415)
      ·
        refine ⟨26648877690468818626100123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17765918460312545750733415 26648877690468818626100123)
        ·
          refine ⟨39973316535703227939150185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26648877690468818626100123 39973316535703227939150185)
          ·
            refine ⟨29979987401777420954362639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39973316535703227939150185 29979987401777420954362639)
            ·
              refine ⟨44969981102666131431543959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29979987401777420954362639 44969981102666131431543959)
              ·
                refine ⟨67454971653999197147315939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44969981102666131431543959 67454971653999197147315939)
                ·
                  refine ⟨101182457480998795720973909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67454971653999197147315939 101182457480998795720973909)
                  ·
                    refine ⟨1185731923605454637355163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101182457480998795720973909 1185731923605454637355163)
                    ·
                      rfl

theorem cell23_6927614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_6927614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927614 prefixEnd_6927614 := by exact prefixLift 6927614
  have htrace : WordTrace (prefixWord ++ tailWord_6927614) baseStart_6927614 baseEnd_6927614 := by
    simpa [prefixWord, tailWord_6927614, baseEnd_6927614] using wordTrace_append hprefix tailTrace_6927614
  have hstable : (prefixWord ++ tailWord_6927614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927614).length < 2 ^ (prefixWord ++ tailWord_6927614).sum := by decide
  have hdescent : baseEnd_6927614 < baseStart_6927614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927621 : List Nat := [1, 3, 1, 1, 2, 1, 6, 1, 1, 4, 2]
def baseStart_6927621 : Nat := 118140960795 + 6927621 * 2 ^ 59
def prefixEnd_6927621 : Nat := 4983230072969 + 3 ^ 40 * 6927621 * 2
def baseEnd_6927621 : Nat := 3557199365180945384677957

theorem tailTrace_6927621 : CollatzResearch.WordTrace tailWord_6927621 prefixEnd_6927621 3557199365180945384677957 := by
  unfold tailWord_6927621
  simp only [CollatzResearch.WordTrace]
  refine ⟨252671095635419735317046717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168447397090279823544697811 252671095635419735317046717)
  ·
    refine ⟨94751660863282400743892519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252671095635419735317046717 94751660863282400743892519)
    ·
      refine ⟨142127491294923601115838779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94751660863282400743892519 142127491294923601115838779)
      ·
        refine ⟨213191236942385401673758169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142127491294923601115838779 213191236942385401673758169)
        ·
          refine ⟨159893427706789051255318627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213191236942385401673758169 159893427706789051255318627)
          ·
            refine ⟨239840141560183576882977941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159893427706789051255318627 239840141560183576882977941)
            ·
              refine ⟨11242506635633605166389591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239840141560183576882977941 11242506635633605166389591)
              ·
                refine ⟨16863759953450407749584387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242506635633605166389591 16863759953450407749584387)
                ·
                  refine ⟨25295639930175611624376581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16863759953450407749584387 25295639930175611624376581)
                  ·
                    refine ⟨4742932486907927179570609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25295639930175611624376581 4742932486907927179570609)
                    ·
                      refine ⟨3557199365180945384677957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4742932486907927179570609 3557199365180945384677957)
                      ·
                        rfl

theorem cell23_6927621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 4, 2].length) (baseStart_6927621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927621 prefixEnd_6927621 := by exact prefixLift 6927621
  have htrace : WordTrace (prefixWord ++ tailWord_6927621) baseStart_6927621 baseEnd_6927621 := by
    simpa [prefixWord, tailWord_6927621, baseEnd_6927621] using wordTrace_append hprefix tailTrace_6927621
  have hstable : (prefixWord ++ tailWord_6927621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927621).length < 2 ^ (prefixWord ++ tailWord_6927621).sum := by decide
  have hdescent : baseEnd_6927621 < baseStart_6927621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927627 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 9]
def baseStart_6927627 : Nat := 118140960795 + 6927627 * 2 ^ 59
def prefixEnd_6927627 : Nat := 4983230072969 + 3 ^ 40 * 6927627 * 2
def baseEnd_6927627 : Nat := 395244716229430262355881

theorem tailTrace_6927627 : CollatzResearch.WordTrace tailWord_6927627 prefixEnd_6927627 395244716229430262355881 := by
  unfold tailWord_6927627
  simp only [CollatzResearch.WordTrace]
  refine ⟨252671314473397998341765135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168447542982265332227843423 252671314473397998341765135)
  ·
    refine ⟨379006971710096997512647703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252671314473397998341765135 379006971710096997512647703)
    ·
      refine ⟨568510457565145496268971555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379006971710096997512647703 568510457565145496268971555)
      ·
        refine ⟨852765686347718244403457333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568510457565145496268971555 852765686347718244403457333)
        ·
          refine ⟨79946783095098585412824125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 852765686347718244403457333 79946783095098585412824125)
          ·
            refine ⟨29980043660661969529809047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79946783095098585412824125 29980043660661969529809047)
            ·
              refine ⟨44970065490992954294713571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29980043660661969529809047 44970065490992954294713571)
              ·
                refine ⟨67455098236489431442070357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44970065490992954294713571 67455098236489431442070357)
                ·
                  refine ⟨395244716229430262355881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67455098236489431442070357 395244716229430262355881)
                  ·
                    rfl

theorem cell23_6927627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 9].length) (baseStart_6927627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927627 prefixEnd_6927627 := by exact prefixLift 6927627
  have htrace : WordTrace (prefixWord ++ tailWord_6927627) baseStart_6927627 baseEnd_6927627 := by
    simpa [prefixWord, tailWord_6927627, baseEnd_6927627] using wordTrace_append hprefix tailTrace_6927627
  have hstable : (prefixWord ++ tailWord_6927627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927627).length < 2 ^ (prefixWord ++ tailWord_6927627).sum := by decide
  have hdescent : baseEnd_6927627 < baseStart_6927627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927637 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_6927637 : Nat := 118140960795 + 6927637 * 2 ^ 59
def prefixEnd_6927637 : Nat := 4983230072969 + 3 ^ 40 * 6927637 * 2
def baseEnd_6927637 : Nat := 3557207580871417322077883

theorem tailTrace_6927637 : CollatzResearch.WordTrace tailWord_6927637 prefixEnd_6927637 3557207580871417322077883 := by
  unfold tailWord_6927637
  simp only [CollatzResearch.WordTrace]
  refine ⟨252671679203361770049629165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168447786135574513366419443 252671679203361770049629165)
  ·
    refine ⟨94751879701260663768610937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252671679203361770049629165 94751879701260663768610937)
    ·
      refine ⟨71063909775945497826458203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94751879701260663768610937 71063909775945497826458203)
      ·
        refine ⟨106595864663918246739687305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71063909775945497826458203 106595864663918246739687305)
        ·
          refine ⟨79946898497938685054765479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106595864663918246739687305 79946898497938685054765479)
          ·
            refine ⟨119920347746908027582148219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79946898497938685054765479 119920347746908027582148219)
            ·
              refine ⟨179880521620362041373222329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119920347746908027582148219 179880521620362041373222329)
              ·
                refine ⟨134910391215271531029916747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179880521620362041373222329 134910391215271531029916747)
                ·
                  refine ⟨202365586822907296544875121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134910391215271531029916747 202365586822907296544875121)
                  ·
                    refine ⟨151774190117180472408656341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202365586822907296544875121 151774190117180472408656341)
                    ·
                      refine ⟨3557207580871417322077883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151774190117180472408656341 3557207580871417322077883)
                      ·
                        rfl

theorem cell23_6927637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_6927637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927637 prefixEnd_6927637 := by exact prefixLift 6927637
  have htrace : WordTrace (prefixWord ++ tailWord_6927637) baseStart_6927637 baseEnd_6927637 := by
    simpa [prefixWord, tailWord_6927637, baseEnd_6927637] using wordTrace_append hprefix tailTrace_6927637
  have hstable : (prefixWord ++ tailWord_6927637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927637).length < 2 ^ (prefixWord ++ tailWord_6927637).sum := by decide
  have hdescent : baseEnd_6927637 < baseStart_6927637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927661 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 7]
def baseStart_6927661 : Nat := 118140960795 + 6927661 * 2 ^ 59
def prefixEnd_6927661 : Nat := 4983230072969 + 3 ^ 40 * 6927661 * 2
def baseEnd_6927661 : Nat := 395246656045236136464197

theorem tailTrace_6927661 : CollatzResearch.WordTrace tailWord_6927661 prefixEnd_6927661 395246656045236136464197 := by
  unfold tailWord_6927661
  simp only [CollatzResearch.WordTrace]
  refine ⟨252672554555274822148502837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168448369703516548099001891 252672554555274822148502837)
  ·
    refine ⟨23688051989557014576422141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252672554555274822148502837 23688051989557014576422141)
    ·
      refine ⟨8883019496083880466158303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23688051989557014576422141 8883019496083880466158303)
      ·
        refine ⟨13324529244125820699237455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8883019496083880466158303 13324529244125820699237455)
        ·
          refine ⟨19986793866188731048856183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13324529244125820699237455 19986793866188731048856183)
          ·
            refine ⟨29980190799283096573284275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19986793866188731048856183 29980190799283096573284275)
            ·
              refine ⟨44970286198924644859926413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29980190799283096573284275 44970286198924644859926413)
              ·
                refine ⟨16863857324596741822472405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44970286198924644859926413 16863857324596741822472405)
                ·
                  refine ⟨395246656045236136464197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16863857324596741822472405 395246656045236136464197)
                  ·
                    rfl

theorem cell23_6927661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_6927661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927661 prefixEnd_6927661 := by exact prefixLift 6927661
  have htrace : WordTrace (prefixWord ++ tailWord_6927661) baseStart_6927661 baseEnd_6927661 := by
    simpa [prefixWord, tailWord_6927661, baseEnd_6927661] using wordTrace_append hprefix tailTrace_6927661
  have hstable : (prefixWord ++ tailWord_6927661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927661).length < 2 ^ (prefixWord ++ tailWord_6927661).sum := by decide
  have hdescent : baseEnd_6927661 < baseStart_6927661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927694 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6927694 : Nat := 118140960795 + 6927694 * 2 ^ 59
def prefixEnd_6927694 : Nat := 4983230072969 + 3 ^ 40 * 6927694 * 2
def baseEnd_6927694 : Nat := 3557236849268723599065121

theorem tailTrace_6927694 : CollatzResearch.WordTrace tailWord_6927694 prefixEnd_6927694 3557236849268723599065121 := by
  unfold tailWord_6927694
  simp only [CollatzResearch.WordTrace]
  refine ⟨31584219770519408598056767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168449172109436845856302757 31584219770519408598056767)
  ·
    refine ⟨47376329655779112897085151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31584219770519408598056767 47376329655779112897085151)
    ·
      refine ⟨71064494483668669345627727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47376329655779112897085151 71064494483668669345627727)
      ·
        refine ⟨106596741725503004018441591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71064494483668669345627727 106596741725503004018441591)
        ·
          refine ⟨159895112588254506027662387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106596741725503004018441591 159895112588254506027662387)
          ·
            refine ⟨239842668882381759041493581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159895112588254506027662387 239842668882381759041493581)
            ·
              refine ⟨89941000830893159640560093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239842668882381759041493581 89941000830893159640560093)
              ·
                refine ⟨33727875311584934865210035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89941000830893159640560093 33727875311584934865210035)
                ·
                  refine ⟨50591812967377402297815053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33727875311584934865210035 50591812967377402297815053)
                  ·
                    refine ⟨18971929862766525861680645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50591812967377402297815053 18971929862766525861680645)
                    ·
                      refine ⟨3557236849268723599065121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18971929862766525861680645 3557236849268723599065121)
                      ·
                        rfl

theorem cell23_6927694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6927694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927694 prefixEnd_6927694 := by exact prefixLift 6927694
  have htrace : WordTrace (prefixWord ++ tailWord_6927694) baseStart_6927694 baseEnd_6927694 := by
    simpa [prefixWord, tailWord_6927694, baseEnd_6927694] using wordTrace_append hprefix tailTrace_6927694
  have hstable : (prefixWord ++ tailWord_6927694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927694).length < 2 ^ (prefixWord ++ tailWord_6927694).sum := by decide
  have hdescent : baseEnd_6927694 < baseStart_6927694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927744 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3]
def baseStart_6927744 : Nat := 118140960795 + 6927744 * 2 ^ 59
def prefixEnd_6927744 : Nat := 4983230072969 + 3 ^ 40 * 6927744 * 2
def baseEnd_6927744 : Nat := 3557262523301448403439891

theorem tailTrace_6927744 : CollatzResearch.WordTrace tailWord_6927744 prefixEnd_6927744 3557262523301448403439891 := by
  unfold tailWord_6927744
  simp only [CollatzResearch.WordTrace]
  refine ⟨126337790906987063661887143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168450387875982751549182857 126337790906987063661887143)
  ·
    refine ⟨189506686360480595492830715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126337790906987063661887143 189506686360480595492830715)
    ·
      refine ⟨284260029540720893239246073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189506686360480595492830715 284260029540720893239246073)
      ·
        refine ⟨213195022155540669929434555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284260029540720893239246073 213195022155540669929434555)
        ·
          refine ⟨319792533233311004894151833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213195022155540669929434555 319792533233311004894151833)
          ·
            refine ⟨239844399924983253670613875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319792533233311004894151833 239844399924983253670613875)
            ·
              refine ⟨359766599887474880505920813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239844399924983253670613875 359766599887474880505920813)
              ·
                refine ⟨134912474957803080189720305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359766599887474880505920813 134912474957803080189720305)
                ·
                  refine ⟨101184356218352310142290229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134912474957803080189720305 101184356218352310142290229)
                  ·
                    refine ⟨9486033395470529075839709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101184356218352310142290229 9486033395470529075839709)
                    ·
                      refine ⟨3557262523301448403439891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486033395470529075839709 3557262523301448403439891)
                      ·
                        rfl

theorem cell23_6927744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_6927744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927744 prefixEnd_6927744 := by exact prefixLift 6927744
  have htrace : WordTrace (prefixWord ++ tailWord_6927744) baseStart_6927744 baseEnd_6927744 := by
    simpa [prefixWord, tailWord_6927744, baseEnd_6927744] using wordTrace_append hprefix tailTrace_6927744
  have hstable : (prefixWord ++ tailWord_6927744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927744).length < 2 ^ (prefixWord ++ tailWord_6927744).sum := by decide
  have hdescent : baseEnd_6927744 < baseStart_6927744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927748 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_6927748 : Nat := 118140960795 + 6927748 * 2 ^ 59
def prefixEnd_6927748 : Nat := 4983230072969 + 3 ^ 40 * 6927748 * 2
def baseEnd_6927748 : Nat := 3557264577224066387789873

theorem tailTrace_6927748 : CollatzResearch.WordTrace tailWord_6927748 prefixEnd_6927748 3557264577224066387789873 := by
  unfold tailWord_6927748
  simp only [CollatzResearch.WordTrace]
  refine ⟨126337863852979818003459949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168450485137306424004613265 126337863852979818003459949)
  ·
    refine ⟨47376698944867431751297481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126337863852979818003459949 47376698944867431751297481)
    ·
      refine ⟨35532524208650573813473111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47376698944867431751297481 35532524208650573813473111)
      ·
        refine ⟨53298786312975860720209667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35532524208650573813473111 53298786312975860720209667)
        ·
          refine ⟨79948179469463791080314501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53298786312975860720209667 79948179469463791080314501)
          ·
            refine ⟨14990283650524460827558969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79948179469463791080314501 14990283650524460827558969)
            ·
              refine ⟨11242712737893345620669227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14990283650524460827558969 11242712737893345620669227)
              ·
                refine ⟨16864069106840018431003841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11242712737893345620669227 16864069106840018431003841)
                ·
                  refine ⟨12648051830130013823252881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16864069106840018431003841 12648051830130013823252881)
                  ·
                    refine ⟨9486038872597510367439661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12648051830130013823252881 9486038872597510367439661)
                    ·
                      refine ⟨3557264577224066387789873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486038872597510367439661 3557264577224066387789873)
                      ·
                        rfl

theorem cell23_6927748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_6927748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927748 prefixEnd_6927748 := by exact prefixLift 6927748
  have htrace : WordTrace (prefixWord ++ tailWord_6927748) baseStart_6927748 baseEnd_6927748 := by
    simpa [prefixWord, tailWord_6927748, baseEnd_6927748] using wordTrace_append hprefix tailTrace_6927748
  have hstable : (prefixWord ++ tailWord_6927748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927748).length < 2 ^ (prefixWord ++ tailWord_6927748).sum := by decide
  have hdescent : baseEnd_6927748 < baseStart_6927748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927761 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 3]
def baseStart_6927761 : Nat := 118140960795 + 6927761 * 2 ^ 59
def prefixEnd_6927761 : Nat := 4983230072969 + 3 ^ 40 * 6927761 * 2
def baseEnd_6927761 : Nat := 3557271252472574836927313

theorem tailTrace_6927761 : CollatzResearch.WordTrace tailWord_6927761 prefixEnd_6927761 3557271252472574836927313 := by
  unfold tailWord_6927761
  simp only [CollatzResearch.WordTrace]
  refine ⟨252676201854912539227143137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168450801236608359484762091 252676201854912539227143137)
  ·
    refine ⟨189507151391184404420357353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252676201854912539227143137 189507151391184404420357353)
    ·
      refine ⟨142130363543388303315268015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189507151391184404420357353 142130363543388303315268015)
      ·
        refine ⟨213195545315082454972902023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142130363543388303315268015 213195545315082454972902023)
        ·
          refine ⟨319793317972623682459353035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213195545315082454972902023 319793317972623682459353035)
          ·
            refine ⟨479689976958935523689029553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319793317972623682459353035 479689976958935523689029553)
            ·
              refine ⟨359767482719201642766772165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479689976958935523689029553 359767482719201642766772165)
              ·
                refine ⟨67456403009850308018769781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359767482719201642766772165 67456403009850308018769781)
                ·
                  refine ⟨6324037782173466376759667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67456403009850308018769781 6324037782173466376759667)
                  ·
                    refine ⟨9486056673260199565139501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324037782173466376759667 9486056673260199565139501)
                    ·
                      refine ⟨3557271252472574836927313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486056673260199565139501 3557271252472574836927313)
                      ·
                        rfl

theorem cell23_6927761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 3].length) (baseStart_6927761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927761 prefixEnd_6927761 := by exact prefixLift 6927761
  have htrace : WordTrace (prefixWord ++ tailWord_6927761) baseStart_6927761 baseEnd_6927761 := by
    simpa [prefixWord, tailWord_6927761, baseEnd_6927761] using wordTrace_append hprefix tailTrace_6927761
  have hstable : (prefixWord ++ tailWord_6927761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927761).length < 2 ^ (prefixWord ++ tailWord_6927761).sum := by decide
  have hdescent : baseEnd_6927761 < baseStart_6927761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927768 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 6]
def baseStart_6927768 : Nat := 118140960795 + 6927768 * 2 ^ 59
def prefixEnd_6927768 : Nat := 4983230072969 + 3 ^ 40 * 6927768 * 2
def baseEnd_6927768 : Nat := 395252760759684034393309

theorem tailTrace_6927768 : CollatzResearch.WordTrace tailWord_6927768 prefixEnd_6927768 395252760759684034393309 := by
  unfold tailWord_6927768
  simp only [CollatzResearch.WordTrace]
  refine ⟨126338228582943589711323979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168450971443924786281765305 126338228582943589711323979)
  ·
    refine ⟨189507342874415384566985969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126338228582943589711323979 189507342874415384566985969)
    ·
      refine ⟨142130507155811538425239477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189507342874415384566985969 142130507155811538425239477)
      ·
        refine ⟨13324735045857331727366201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142130507155811538425239477 13324735045857331727366201)
        ·
          refine ⟨9993551284392998795524651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13324735045857331727366201 9993551284392998795524651)
          ·
            refine ⟨14990326926589498193286977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993551284392998795524651 14990326926589498193286977)
            ·
              refine ⟨11242745194942123644965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14990326926589498193286977 11242745194942123644965233)
              ·
                refine ⟨8432058896206592733723925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11242745194942123644965233 8432058896206592733723925)
                ·
                  refine ⟨395252760759684034393309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8432058896206592733723925 395252760759684034393309)
                  ·
                    rfl

theorem cell23_6927768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 6].length) (baseStart_6927768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927768 prefixEnd_6927768 := by exact prefixLift 6927768
  have htrace : WordTrace (prefixWord ++ tailWord_6927768) baseStart_6927768 baseEnd_6927768 := by
    simpa [prefixWord, tailWord_6927768, baseEnd_6927768] using wordTrace_append hprefix tailTrace_6927768
  have hstable : (prefixWord ++ tailWord_6927768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927768).length < 2 ^ (prefixWord ++ tailWord_6927768).sum := by decide
  have hdescent : baseEnd_6927768 < baseStart_6927768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927772 : List Nat := [2, 2, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_6927772 : Nat := 118140960795 + 6927772 * 2 ^ 59
def prefixEnd_6927772 : Nat := 4983230072969 + 3 ^ 40 * 6927772 * 2
def baseEnd_6927772 : Nat := 1185758966919924764629921

theorem tailTrace_6927772 : CollatzResearch.WordTrace tailWord_6927772 prefixEnd_6927772 1185758966919924764629921 := by
  unfold tailWord_6927772
  simp only [CollatzResearch.WordTrace]
  refine ⟨126338301528936344052896785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168451068705248458737195713 126338301528936344052896785)
  ·
    refine ⟨94753726146702258039672589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126338301528936344052896785 94753726146702258039672589)
    ·
      refine ⟨35532647305013346764877221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94753726146702258039672589 35532647305013346764877221)
      ·
        refine ⟨6662371369690002518414479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35532647305013346764877221 6662371369690002518414479)
        ·
          refine ⟨9993557054535003777621719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662371369690002518414479 9993557054535003777621719)
          ·
            refine ⟨14990335581802505666432579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993557054535003777621719 14990335581802505666432579)
            ·
              refine ⟨22485503372703758499648869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990335581802505666432579 22485503372703758499648869)
              ·
                refine ⟨4216031882381954718684163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22485503372703758499648869 4216031882381954718684163)
                ·
                  refine ⟨6324047823572932078026245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216031882381954718684163 6324047823572932078026245)
                  ·
                    refine ⟨1185758966919924764629921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324047823572932078026245 1185758966919924764629921)
                    ·
                      rfl

theorem cell23_6927772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_6927772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927772 prefixEnd_6927772 := by exact prefixLift 6927772
  have htrace : WordTrace (prefixWord ++ tailWord_6927772) baseStart_6927772 baseEnd_6927772 := by
    simpa [prefixWord, tailWord_6927772, baseEnd_6927772] using wordTrace_append hprefix tailTrace_6927772
  have hstable : (prefixWord ++ tailWord_6927772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927772).length < 2 ^ (prefixWord ++ tailWord_6927772).sum := by decide
  have hdescent : baseEnd_6927772 < baseStart_6927772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927812 : List Nat := [2, 3, 3, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6927812 : Nat := 118140960795 + 6927812 * 2 ^ 59
def prefixEnd_6927812 : Nat := 4983230072969 + 3 ^ 40 * 6927812 * 2
def baseEnd_6927812 : Nat := 3557297439985954137389579

theorem tailTrace_6927812 : CollatzResearch.WordTrace tailWord_6927812 prefixEnd_6927812 3557297439985954137389579 := by
  unfold tailWord_6927812
  simp only [CollatzResearch.WordTrace]
  refine ⟨126339030988863887468624845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168452041318485183291499793 126339030988863887468624845)
  ·
    refine ⟨47377136620823957800734317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126339030988863887468624845 47377136620823957800734317)
    ·
      refine ⟨17766426232808984175275369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47377136620823957800734317 17766426232808984175275369)
      ·
        refine ⟨13324819674606738131456527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17766426232808984175275369 13324819674606738131456527)
        ·
          refine ⟨19987229511910107197184791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13324819674606738131456527 19987229511910107197184791)
          ·
            refine ⟨29980844267865160795777187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19987229511910107197184791 29980844267865160795777187)
            ·
              refine ⟨44971266401797741193665781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29980844267865160795777187 44971266401797741193665781)
              ·
                refine ⟨4216056225168538236906167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44971266401797741193665781 4216056225168538236906167)
                ·
                  refine ⟨6324084337752807355359251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216056225168538236906167 6324084337752807355359251)
                  ·
                    refine ⟨9486126506629211033038877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324084337752807355359251 9486126506629211033038877)
                    ·
                      refine ⟨3557297439985954137389579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486126506629211033038877 3557297439985954137389579)
                      ·
                        rfl

theorem cell23_6927812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6927812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927812 prefixEnd_6927812 := by exact prefixLift 6927812
  have htrace : WordTrace (prefixWord ++ tailWord_6927812) baseStart_6927812 baseEnd_6927812 := by
    simpa [prefixWord, tailWord_6927812, baseEnd_6927812] using wordTrace_append hprefix tailTrace_6927812
  have hstable : (prefixWord ++ tailWord_6927812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927812).length < 2 ^ (prefixWord ++ tailWord_6927812).sum := by decide
  have hdescent : baseEnd_6927812 < baseStart_6927812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927818 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4]
def baseStart_6927818 : Nat := 118140960795 + 6927818 * 2 ^ 59
def prefixEnd_6927818 : Nat := 4983230072969 + 3 ^ 40 * 6927818 * 2
def baseEnd_6927818 : Nat := 3557300520869881113914551

theorem tailTrace_6927818 : CollatzResearch.WordTrace tailWord_6927818 prefixEnd_6927818 3557300520869881113914551 := by
  unfold tailWord_6927818
  simp only [CollatzResearch.WordTrace]
  refine ⟨63169570203926509490492027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168452187210470691974645405 63169570203926509490492027)
  ·
    refine ⟨94754355305889764235738041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63169570203926509490492027 94754355305889764235738041)
    ·
      refine ⟨71065766479417323176803531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94754355305889764235738041 71065766479417323176803531)
      ·
        refine ⟨106598649719125984765205297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71065766479417323176803531 106598649719125984765205297)
        ·
          refine ⟨79948987289344488573903973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106598649719125984765205297 79948987289344488573903973)
          ·
            refine ⟨14990435116752091607606995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79948987289344488573903973 14990435116752091607606995)
            ·
              refine ⟨22485652675128137411410493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990435116752091607606995 22485652675128137411410493)
              ·
                refine ⟨8432119753173051529278935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22485652675128137411410493 8432119753173051529278935)
                ·
                  refine ⟨12648179629759577293918403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432119753173051529278935 12648179629759577293918403)
                  ·
                    refine ⟨18972269444639365940877605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12648179629759577293918403 18972269444639365940877605)
                    ·
                      refine ⟨3557300520869881113914551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18972269444639365940877605 3557300520869881113914551)
                      ·
                        rfl

theorem cell23_6927818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4].length) (baseStart_6927818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927818 prefixEnd_6927818 := by exact prefixLift 6927818
  have htrace : WordTrace (prefixWord ++ tailWord_6927818) baseStart_6927818 baseEnd_6927818 := by
    simpa [prefixWord, tailWord_6927818, baseEnd_6927818] using wordTrace_append hprefix tailTrace_6927818
  have hstable : (prefixWord ++ tailWord_6927818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927818).length < 2 ^ (prefixWord ++ tailWord_6927818).sum := by decide
  have hdescent : baseEnd_6927818 < baseStart_6927818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927851 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3]
def baseStart_6927851 : Nat := 118140960795 + 6927851 * 2 ^ 59
def prefixEnd_6927851 : Nat := 4983230072969 + 3 ^ 40 * 6927851 * 2
def baseEnd_6927851 : Nat := 3557317465731479484801899

theorem tailTrace_6927851 : CollatzResearch.WordTrace tailWord_6927851 prefixEnd_6927851 3557317465731479484801899 := by
  unfold tailWord_6927851
  simp only [CollatzResearch.WordTrace]
  refine ⟨252679484424586484597919407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168452989616390989731946271 252679484424586484597919407)
  ·
    refine ⟨379019226636879726896879111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252679484424586484597919407 379019226636879726896879111)
    ·
      refine ⟨568528839955319590345318667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379019226636879726896879111 568528839955319590345318667)
      ·
        refine ⟨852793259932979385517978001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568528839955319590345318667 852793259932979385517978001)
        ·
          refine ⟨639594944949734539138483501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 852793259932979385517978001 639594944949734539138483501)
          ·
            refine ⟨239848104356150452176931313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639594944949734539138483501 239848104356150452176931313)
            ·
              refine ⟨179886078267112839132698485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239848104356150452176931313 179886078267112839132698485)
              ·
                refine ⟨16864319837541828668690483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179886078267112839132698485 16864319837541828668690483)
                ·
                  refine ⟨25296479756312743003035725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16864319837541828668690483 25296479756312743003035725)
                  ·
                    refine ⟨9486179908617278626138397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25296479756312743003035725 9486179908617278626138397)
                    ·
                      refine ⟨3557317465731479484801899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486179908617278626138397 3557317465731479484801899)
                      ·
                        rfl

theorem cell23_6927851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3].length) (baseStart_6927851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927851 prefixEnd_6927851 := by exact prefixLift 6927851
  have htrace : WordTrace (prefixWord ++ tailWord_6927851) baseStart_6927851 baseEnd_6927851 := by
    simpa [prefixWord, tailWord_6927851, baseEnd_6927851] using wordTrace_append hprefix tailTrace_6927851
  have hstable : (prefixWord ++ tailWord_6927851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927851).length < 2 ^ (prefixWord ++ tailWord_6927851).sum := by decide
  have hdescent : baseEnd_6927851 < baseStart_6927851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927858 : List Nat := [3, 2, 1, 4, 1, 1, 4, 7]
def baseStart_6927858 : Nat := 118140960795 + 6927858 * 2 ^ 59
def prefixEnd_6927858 : Nat := 4983230072969 + 3 ^ 40 * 6927858 * 2
def baseEnd_6927858 : Nat := 131752631855409665089421

theorem tailTrace_6927858 : CollatzResearch.WordTrace tailWord_6927858 prefixEnd_6927858 131752631855409665089421 := by
  unfold tailWord_6927858
  simp only [CollatzResearch.WordTrace]
  refine ⟨63169934933890281198356057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168453159823707416528949485 63169934933890281198356057)
  ·
    refine ⟨47377451200417710898767043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63169934933890281198356057 47377451200417710898767043)
    ·
      refine ⟨71066176800626566348150565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47377451200417710898767043 71066176800626566348150565)
      ·
        refine ⟨13324908150117481190278231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71066176800626566348150565 13324908150117481190278231)
        ·
          refine ⟨19987362225176221785417347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13324908150117481190278231 19987362225176221785417347)
          ·
            refine ⟨29981043337764332678126021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19987362225176221785417347 29981043337764332678126021)
            ·
              refine ⟨5621445625830812377148629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29981043337764332678126021 5621445625830812377148629)
              ·
                refine ⟨131752631855409665089421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5621445625830812377148629 131752631855409665089421)
                ·
                  rfl

theorem cell23_6927858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 7].length) (baseStart_6927858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927858 prefixEnd_6927858 := by exact prefixLift 6927858
  have htrace : WordTrace (prefixWord ++ tailWord_6927858) baseStart_6927858 baseEnd_6927858 := by
    simpa [prefixWord, tailWord_6927858, baseEnd_6927858] using wordTrace_append hprefix tailTrace_6927858
  have hstable : (prefixWord ++ tailWord_6927858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927858).length < 2 ^ (prefixWord ++ tailWord_6927858).sum := by decide
  have hdescent : baseEnd_6927858 < baseStart_6927858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927868 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 4, 1, 3]
def baseStart_6927868 : Nat := 118140960795 + 6927868 * 2 ^ 59
def prefixEnd_6927868 : Nat := 4983230072969 + 3 ^ 40 * 6927868 * 2
def baseEnd_6927868 : Nat := 3557326194902605918289321

theorem tailTrace_6927868 : CollatzResearch.WordTrace tailWord_6927868 prefixEnd_6927868 3557326194902605918289321 := by
  unfold tailWord_6927868
  simp only [CollatzResearch.WordTrace]
  refine ⟨126340052232762448250644129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168453402977016597667525505 126340052232762448250644129)
  ·
    refine ⟨94755039174571836187983097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126340052232762448250644129 94755039174571836187983097)
    ·
      refine ⟨71066279380928877140987323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94755039174571836187983097 71066279380928877140987323)
      ·
        refine ⟨106599419071393315711480985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71066279380928877140987323 106599419071393315711480985)
        ·
          refine ⟨79949564303544986783610739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106599419071393315711480985 79949564303544986783610739)
          ·
            refine ⟨119924346455317480175416109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79949564303544986783610739 119924346455317480175416109)
            ·
              refine ⟨44971629920744055065781041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119924346455317480175416109 44971629920744055065781041)
              ·
                refine ⟨33728722440558041299335781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44971629920744055065781041 33728722440558041299335781)
                ·
                  refine ⟨6324135457604632743625459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33728722440558041299335781 6324135457604632743625459)
                  ·
                    refine ⟨9486203186406949115438189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324135457604632743625459 9486203186406949115438189)
                    ·
                      refine ⟨3557326194902605918289321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486203186406949115438189 3557326194902605918289321)
                      ·
                        rfl

theorem cell23_6927868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 4, 1, 3].length) (baseStart_6927868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927868 prefixEnd_6927868 := by exact prefixLift 6927868
  have htrace : WordTrace (prefixWord ++ tailWord_6927868) baseStart_6927868 baseEnd_6927868 := by
    simpa [prefixWord, tailWord_6927868, baseEnd_6927868] using wordTrace_append hprefix tailTrace_6927868
  have hstable : (prefixWord ++ tailWord_6927868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927868).length < 2 ^ (prefixWord ++ tailWord_6927868).sum := by decide
  have hdescent : baseEnd_6927868 < baseStart_6927868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927869 : List Nat := [1, 4, 1, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_6927869 : Nat := 118140960795 + 6927869 * 2 ^ 59
def prefixEnd_6927869 : Nat := 4983230072969 + 3 ^ 40 * 6927869 * 2
def baseEnd_6927869 : Nat := 3557326708383260414376817

theorem tailTrace_6927869 : CollatzResearch.WordTrace tailWord_6927869 prefixEnd_6927869 3557326708383260414376817 := by
  unfold tailWord_6927869
  simp only [CollatzResearch.WordTrace]
  refine ⟨252680140938521273672074661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168453427292347515781383107 252680140938521273672074661)
  ·
    refine ⟨47377526425972738813513999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252680140938521273672074661 47377526425972738813513999)
    ·
      refine ⟨71066289638959108220270999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47377526425972738813513999 71066289638959108220270999)
      ·
        refine ⟨106599434458438662330406499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71066289638959108220270999 106599434458438662330406499)
        ·
          refine ⟨159899151687657993495609749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106599434458438662330406499 159899151687657993495609749)
          ·
            refine ⟨7495272735358968445106707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159899151687657993495609749 7495272735358968445106707)
            ·
              refine ⟨11242909103038452667660061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495272735358968445106707 11242909103038452667660061)
              ·
                refine ⟨4216090913639419750372523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11242909103038452667660061 4216090913639419750372523)
                ·
                  refine ⟨6324136370459129625558785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216090913639419750372523 6324136370459129625558785)
                  ·
                    refine ⟨4743102277844347219169089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324136370459129625558785 4743102277844347219169089)
                    ·
                      refine ⟨3557326708383260414376817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743102277844347219169089 3557326708383260414376817)
                      ·
                        rfl

theorem cell23_6927869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_6927869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927869 prefixEnd_6927869 := by exact prefixLift 6927869
  have htrace : WordTrace (prefixWord ++ tailWord_6927869) baseStart_6927869 baseEnd_6927869 := by
    simpa [prefixWord, tailWord_6927869, baseEnd_6927869] using wordTrace_append hprefix tailTrace_6927869
  have hstable : (prefixWord ++ tailWord_6927869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927869).length < 2 ^ (prefixWord ++ tailWord_6927869).sum := by decide
  have hdescent : baseEnd_6927869 < baseStart_6927869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927886 : List Nat := [4, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_6927886 : Nat := 118140960795 + 6927886 * 2 ^ 59
def prefixEnd_6927886 : Nat := 4983230072969 + 3 ^ 40 * 6927886 * 2
def baseEnd_6927886 : Nat := 3557335437554386847864239

theorem tailTrace_6927886 : CollatzResearch.WordTrace tailWord_6927886 prefixEnd_6927886 3557335437554386847864239 := by
  unfold tailWord_6927886
  simp only [CollatzResearch.WordTrace]
  refine ⟨31585095122432460696930439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168453840652973123716962341 31585095122432460696930439)
  ·
    refine ⟨47377642683648691045395659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31585095122432460696930439 47377642683648691045395659)
    ·
      refine ⟨71066464025473036568093489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47377642683648691045395659 71066464025473036568093489)
      ·
        refine ⟨53299848019104777426070117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71066464025473036568093489 53299848019104777426070117)
        ·
          refine ⟨9993721503582145767388147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53299848019104777426070117 9993721503582145767388147)
          ·
            refine ⟨14990582255373218651082221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993721503582145767388147 14990582255373218651082221)
            ·
              refine ⟨5621468345764956994155833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14990582255373218651082221 5621468345764956994155833)
              ·
                refine ⟨4216101259323717745616875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621468345764956994155833 4216101259323717745616875)
                ·
                  refine ⟨6324151888985576618425313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216101259323717745616875 6324151888985576618425313)
                  ·
                    refine ⟨4743113916739182463818985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324151888985576618425313 4743113916739182463818985)
                    ·
                      refine ⟨3557335437554386847864239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743113916739182463818985 3557335437554386847864239)
                      ·
                        rfl

theorem cell23_6927886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_6927886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927886 prefixEnd_6927886 := by exact prefixLift 6927886
  have htrace : WordTrace (prefixWord ++ tailWord_6927886) baseStart_6927886 baseEnd_6927886 := by
    simpa [prefixWord, tailWord_6927886, baseEnd_6927886] using wordTrace_append hprefix tailTrace_6927886
  have hstable : (prefixWord ++ tailWord_6927886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927886).length < 2 ^ (prefixWord ++ tailWord_6927886).sum := by decide
  have hdescent : baseEnd_6927886 < baseStart_6927886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927901 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_6927901 : Nat := 118140960795 + 6927901 * 2 ^ 59
def prefixEnd_6927901 : Nat := 4983230072969 + 3 ^ 40 * 6927901 * 2
def baseEnd_6927901 : Nat := 1185781046588068096392223

theorem tailTrace_6927901 : CollatzResearch.WordTrace tailWord_6927901 prefixEnd_6927901 1185781046588068096392223 := by
  unfold tailWord_6927901
  simp only [CollatzResearch.WordTrace]
  refine ⟨252681308074405343137239557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168454205382936895424826371 252681308074405343137239557)
  ·
    refine ⟨47377745263951001838232417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252681308074405343137239557 47377745263951001838232417)
    ·
      refine ⟨35533308947963251378674313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47377745263951001838232417 35533308947963251378674313)
      ·
        refine ⟨26649981710972438534005735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35533308947963251378674313 26649981710972438534005735)
        ·
          refine ⟨39974972566458657801008603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26649981710972438534005735 39974972566458657801008603)
          ·
            refine ⟨59962458849687986701512905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39974972566458657801008603 59962458849687986701512905)
            ·
              refine ⟨44971844137265990026134679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59962458849687986701512905 44971844137265990026134679)
              ·
                refine ⟨67457766205898985039202019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44971844137265990026134679 67457766205898985039202019)
                ·
                  refine ⟨101186649308848477558803029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67457766205898985039202019 101186649308848477558803029)
                  ·
                    refine ⟨1185781046588068096392223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101186649308848477558803029 1185781046588068096392223)
                    ·
                      rfl

theorem cell23_6927901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_6927901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927901 prefixEnd_6927901 := by exact prefixLift 6927901
  have htrace : WordTrace (prefixWord ++ tailWord_6927901) baseStart_6927901 baseEnd_6927901 := by
    simpa [prefixWord, tailWord_6927901, baseEnd_6927901] using wordTrace_append hprefix tailTrace_6927901
  have hstable : (prefixWord ++ tailWord_6927901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927901).length < 2 ^ (prefixWord ++ tailWord_6927901).sum := by decide
  have hdescent : baseEnd_6927901 < baseStart_6927901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927912 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2]
def baseStart_6927912 : Nat := 118140960795 + 6927912 * 2 ^ 59
def prefixEnd_6927912 : Nat := 4983230072969 + 3 ^ 40 * 6927912 * 2
def baseEnd_6927912 : Nat := 3557348788051403746139119

theorem tailTrace_6927912 : CollatzResearch.WordTrace tailWord_6927912 prefixEnd_6927912 3557348788051403746139119 := by
  unfold tailWord_6927912
  simp only [CollatzResearch.WordTrace]
  refine ⟨126340854638682746007944995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168454472851576994677259993 126340854638682746007944995)
  ·
    refine ⟨189511281958024119011917493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126340854638682746007944995 189511281958024119011917493)
    ·
      refine ⟨17766682683564761157367265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189511281958024119011917493 17766682683564761157367265)
      ·
        refine ⟨13325012012673570868025449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17766682683564761157367265 13325012012673570868025449)
        ·
          refine ⟨9993759009505178151019087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13325012012673570868025449 9993759009505178151019087)
          ·
            refine ⟨14990638514257767226528631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993759009505178151019087 14990638514257767226528631)
            ·
              refine ⟨22485957771386650839792947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990638514257767226528631 22485957771386650839792947)
              ·
                refine ⟨33728936657079976259689421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22485957771386650839792947 33728936657079976259689421)
                ·
                  refine ⟨12648351246404991097383533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33728936657079976259689421 12648351246404991097383533)
                  ·
                    refine ⟨4743131717401871661518825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12648351246404991097383533 4743131717401871661518825)
                    ·
                      refine ⟨3557348788051403746139119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743131717401871661518825 3557348788051403746139119)
                      ·
                        rfl

theorem cell23_6927912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_6927912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927912 prefixEnd_6927912 := by exact prefixLift 6927912
  have htrace : WordTrace (prefixWord ++ tailWord_6927912) baseStart_6927912 baseEnd_6927912 := by
    simpa [prefixWord, tailWord_6927912, baseEnd_6927912] using wordTrace_append hprefix tailTrace_6927912
  have hstable : (prefixWord ++ tailWord_6927912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927912).length < 2 ^ (prefixWord ++ tailWord_6927912).sum := by decide
  have hdescent : baseEnd_6927912 < baseStart_6927912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927921 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_6927921 : Nat := 118140960795 + 6927921 * 2 ^ 59
def prefixEnd_6927921 : Nat := 4983230072969 + 3 ^ 40 * 6927921 * 2
def baseEnd_6927921 : Nat := 3557353409377294210926577

theorem tailTrace_6927921 : CollatzResearch.WordTrace tailWord_6927921 prefixEnd_6927921 3557353409377294210926577 := by
  unfold tailWord_6927921
  simp only [CollatzResearch.WordTrace]
  refine ⟨252682037534332886552967617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168454691689555257701978411 252682037534332886552967617)
  ·
    refine ⟨189511528150749664914725713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252682037534332886552967617 189511528150749664914725713)
    ·
      refine ⟨142133646113062248686044285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189511528150749664914725713 142133646113062248686044285)
      ·
        refine ⟨53300117292398343257266607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142133646113062248686044285 53300117292398343257266607)
        ·
          refine ⟨79950175938597514885899911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53300117292398343257266607 79950175938597514885899911)
          ·
            refine ⟨119925263907896272328849867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79950175938597514885899911 119925263907896272328849867)
            ·
              refine ⟨179887895861844408493274801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119925263907896272328849867 179887895861844408493274801)
              ·
                refine ⟨134915921896383306369956101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179887895861844408493274801 134915921896383306369956101)
                ·
                  refine ⟨25296735355571869944366769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134915921896383306369956101 25296735355571869944366769)
                  ·
                    refine ⟨18972551516678902458275077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25296735355571869944366769 18972551516678902458275077)
                    ·
                      refine ⟨3557353409377294210926577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18972551516678902458275077 3557353409377294210926577)
                      ·
                        rfl

theorem cell23_6927921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_6927921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927921 prefixEnd_6927921 := by exact prefixLift 6927921
  have htrace : WordTrace (prefixWord ++ tailWord_6927921) baseStart_6927921 baseEnd_6927921 := by
    simpa [prefixWord, tailWord_6927921, baseEnd_6927921] using wordTrace_append hprefix tailTrace_6927921
  have hstable : (prefixWord ++ tailWord_6927921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927921).length < 2 ^ (prefixWord ++ tailWord_6927921).sum := by decide
  have hdescent : baseEnd_6927921 < baseStart_6927921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927925 : List Nat := [1, 3, 3, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_6927925 : Nat := 118140960795 + 6927925 * 2 ^ 59
def prefixEnd_6927925 : Nat := 4983230072969 + 3 ^ 40 * 6927925 * 2
def baseEnd_6927925 : Nat := 3557355463299912195276559

theorem tailTrace_6927925 : CollatzResearch.WordTrace tailWord_6927925 prefixEnd_6927925 3557355463299912195276559 := by
  unfold tailWord_6927925
  simp only [CollatzResearch.WordTrace]
  refine ⟨252682183426318395236113229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168454788950878930157408819 252682183426318395236113229)
  ·
    refine ⟨94755818784869398213542461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252682183426318395236113229 94755818784869398213542461)
    ·
      refine ⟨35533432044326024330078423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94755818784869398213542461 35533432044326024330078423)
      ·
        refine ⟨53300148066489036495117635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35533432044326024330078423 53300148066489036495117635)
        ·
          refine ⟨79950222099733554742676453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53300148066489036495117635 79950222099733554742676453)
          ·
            refine ⟨14990666643700041514251835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79950222099733554742676453 14990666643700041514251835)
            ·
              refine ⟨22485999965550062271377753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990666643700041514251835 22485999965550062271377753)
              ·
                refine ⟨16864499974162546703533315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22485999965550062271377753 16864499974162546703533315)
                ·
                  refine ⟨25296749961243820055299973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16864499974162546703533315 25296749961243820055299973)
                  ·
                    refine ⟨4743140617733216260368745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25296749961243820055299973 4743140617733216260368745)
                    ·
                      refine ⟨3557355463299912195276559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743140617733216260368745 3557355463299912195276559)
                      ·
                        rfl

theorem cell23_6927925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_6927925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927925 prefixEnd_6927925 := by exact prefixLift 6927925
  have htrace : WordTrace (prefixWord ++ tailWord_6927925) baseStart_6927925 baseEnd_6927925 := by
    simpa [prefixWord, tailWord_6927925, baseEnd_6927925] using wordTrace_append hprefix tailTrace_6927925
  have hstable : (prefixWord ++ tailWord_6927925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927925).length < 2 ^ (prefixWord ++ tailWord_6927925).sum := by decide
  have hdescent : baseEnd_6927925 < baseStart_6927925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927961 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_6927961 : Nat := 118140960795 + 6927961 * 2 ^ 59
def prefixEnd_6927961 : Nat := 4983230072969 + 3 ^ 40 * 6927961 * 2
def baseEnd_6927961 : Nat := 1185791316201158018142131

theorem tailTrace_6927961 : CollatzResearch.WordTrace tailWord_6927961 prefixEnd_6927961 1185791316201158018142131 := by
  unfold tailWord_6927961
  simp only [CollatzResearch.WordTrace]
  refine ⟨252683496454187973384423737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168455664302791982256282491 252683496454187973384423737)
  ·
    refine ⟨189512622340640980038317803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252683496454187973384423737 189512622340640980038317803)
    ·
      refine ⟨284268933510961470057476705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189512622340640980038317803 284268933510961470057476705)
      ·
        refine ⟨213201700133221102543107529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284268933510961470057476705 213201700133221102543107529)
        ·
          refine ⟨159901275099915826907330647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213201700133221102543107529 159901275099915826907330647)
          ·
            refine ⟨239851912649873740360995971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159901275099915826907330647 239851912649873740360995971)
            ·
              refine ⟨359777868974810610541493957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239851912649873740360995971 359777868974810610541493957)
              ·
                refine ⟨67458350432776989476530117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 359777868974810610541493957 67458350432776989476530117)
                ·
                  refine ⟨12648440706145685526849397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67458350432776989476530117 12648440706145685526849397)
                  ·
                    refine ⟨1185791316201158018142131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12648440706145685526849397 1185791316201158018142131)
                    ·
                      rfl

theorem cell23_6927961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_6927961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927961 prefixEnd_6927961 := by exact prefixLift 6927961
  have htrace : WordTrace (prefixWord ++ tailWord_6927961) baseStart_6927961 baseEnd_6927961 := by
    simpa [prefixWord, tailWord_6927961, baseEnd_6927961] using wordTrace_append hprefix tailTrace_6927961
  have hstable : (prefixWord ++ tailWord_6927961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927961).length < 2 ^ (prefixWord ++ tailWord_6927961).sum := by decide
  have hdescent : baseEnd_6927961 < baseStart_6927961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927968 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2]
def baseStart_6927968 : Nat := 118140960795 + 6927968 * 2 ^ 59
def prefixEnd_6927968 : Nat := 4983230072969 + 3 ^ 40 * 6927968 * 2
def baseEnd_6927968 : Nat := 3557377542968055527038861

theorem tailTrace_6927968 : CollatzResearch.WordTrace tailWord_6927968 prefixEnd_6927968 3557377542968055527038861 := by
  unfold tailWord_6927968
  simp only [CollatzResearch.WordTrace]
  refine ⟨126341875882581306789964279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168455834510108409053285705 126341875882581306789964279)
  ·
    refine ⟨189512813823871960184946419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126341875882581306789964279 189512813823871960184946419)
    ·
      refine ⟨284269220735807940277419629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189512813823871960184946419 284269220735807940277419629)
      ·
        refine ⟨106600957775927977604032361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284269220735807940277419629 106600957775927977604032361)
        ·
          refine ⟨79950718331945983203024271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106600957775927977604032361 79950718331945983203024271)
          ·
            refine ⟨119926077497918974804536407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79950718331945983203024271 119926077497918974804536407)
            ·
              refine ⟨179889116246878462206804611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119926077497918974804536407 179889116246878462206804611)
              ·
                refine ⟨269833674370317693310206917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179889116246878462206804611 269833674370317693310206917)
                ·
                  refine ⟨50593813944434567495663797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269833674370317693310206917 50593813944434567495663797)
                  ·
                    refine ⟨4743170057290740702718481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50593813944434567495663797 4743170057290740702718481)
                    ·
                      refine ⟨3557377542968055527038861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743170057290740702718481 3557377542968055527038861)
                      ·
                        rfl

theorem cell23_6927968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_6927968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927968 prefixEnd_6927968 := by exact prefixLift 6927968
  have htrace : WordTrace (prefixWord ++ tailWord_6927968) baseStart_6927968 baseEnd_6927968 := by
    simpa [prefixWord, tailWord_6927968, baseEnd_6927968] using wordTrace_append hprefix tailTrace_6927968
  have hstable : (prefixWord ++ tailWord_6927968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927968).length < 2 ^ (prefixWord ++ tailWord_6927968).sum := by decide
  have hdescent : baseEnd_6927968 < baseStart_6927968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927978 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 1, 7]
def baseStart_6927978 : Nat := 118140960795 + 6927978 * 2 ^ 59
def prefixEnd_6927978 : Nat := 4983230072969 + 3 ^ 40 * 6927978 * 2
def baseEnd_6927978 : Nat := 1185794225924866829304605

theorem tailTrace_6927978 : CollatzResearch.WordTrace tailWord_6927978 prefixEnd_6927978 1185794225924866829304605 := by
  unfold tailWord_6927978
  simp only [CollatzResearch.WordTrace]
  refine ⟨63171029123781596321948147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168456077663417590191861725 63171029123781596321948147)
  ·
    refine ⟨94756543685672394482922221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63171029123781596321948147 94756543685672394482922221)
    ·
      refine ⟨35533703882127147931095833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94756543685672394482922221 35533703882127147931095833)
      ·
        refine ⟨26650277911595360948321875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35533703882127147931095833 26650277911595360948321875)
        ·
          refine ⟨39975416867393041422482813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26650277911595360948321875 39975416867393041422482813)
          ·
            refine ⟨14990781325272390533431055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39975416867393041422482813 14990781325272390533431055)
            ·
              refine ⟨22486171987908585800146583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14990781325272390533431055 22486171987908585800146583)
              ·
                refine ⟨33729257981862878700219875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22486171987908585800146583 33729257981862878700219875)
                ·
                  refine ⟨50593886972794318050329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33729257981862878700219875 50593886972794318050329813)
                  ·
                    refine ⟨1185794225924866829304605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50593886972794318050329813 1185794225924866829304605)
                    ·
                      rfl

theorem cell23_6927978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_6927978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927978 prefixEnd_6927978 := by exact prefixLift 6927978
  have htrace : WordTrace (prefixWord ++ tailWord_6927978) baseStart_6927978 baseEnd_6927978 := by
    simpa [prefixWord, tailWord_6927978, baseEnd_6927978] using wordTrace_append hprefix tailTrace_6927978
  have hstable : (prefixWord ++ tailWord_6927978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927978).length < 2 ^ (prefixWord ++ tailWord_6927978).sum := by decide
  have hdescent : baseEnd_6927978 < baseStart_6927978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6927982 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_6927982 : Nat := 118140960795 + 6927982 * 2 ^ 59
def prefixEnd_6927982 : Nat := 4983230072969 + 3 ^ 40 * 6927982 * 2
def baseEnd_6927982 : Nat := 395264970188579830251533

theorem tailTrace_6927982 : CollatzResearch.WordTrace tailWord_6927982 prefixEnd_6927982 395264970188579830251533 := by
  unfold tailWord_6927982
  simp only [CollatzResearch.WordTrace]
  refine ⟨31585532798388986746367275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168456174924741262647292133 31585532798388986746367275)
  ·
    refine ⟨47378299197583480119550913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31585532798388986746367275 47378299197583480119550913)
    ·
      refine ⟨35533724398187610089663185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47378299197583480119550913 35533724398187610089663185)
      ·
        refine ⟨26650293298640707567247389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35533724398187610089663185 26650293298640707567247389)
        ·
          refine ⟨9993859986990265337717771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26650293298640707567247389 9993859986990265337717771)
          ·
            refine ⟨14990789980485398006576657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9993859986990265337717771 14990789980485398006576657)
            ·
              refine ⟨11243092485364048504932493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14990789980485398006576657 11243092485364048504932493)
              ·
                refine ⟨4216159682011518189349685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11243092485364048504932493 4216159682011518189349685)
                ·
                  refine ⟨395264970188579830251533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4216159682011518189349685 395264970188579830251533)
                  ·
                    rfl

theorem cell23_6927982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_6927982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6927982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6927982 prefixEnd_6927982 := by exact prefixLift 6927982
  have htrace : WordTrace (prefixWord ++ tailWord_6927982) baseStart_6927982 baseEnd_6927982 := by
    simpa [prefixWord, tailWord_6927982, baseEnd_6927982] using wordTrace_append hprefix tailTrace_6927982
  have hstable : (prefixWord ++ tailWord_6927982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6927982).length < 2 ^ (prefixWord ++ tailWord_6927982).sum := by decide
  have hdescent : baseEnd_6927982 < baseStart_6927982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6927982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928011 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_6928011 : Nat := 118140960795 + 6928011 * 2 ^ 59
def prefixEnd_6928011 : Nat := 4983230072969 + 3 ^ 40 * 6928011 * 2
def baseEnd_6928011 : Nat := 3557399622636198858801163

theorem tailTrace_6928011 : CollatzResearch.WordTrace tailWord_6928011 prefixEnd_6928011 3557399622636198858801163 := by
  unfold tailWord_6928011
  simp only [CollatzResearch.WordTrace]
  refine ⟨252685320104006831923743887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168456880069337887949162591 252685320104006831923743887)
  ·
    refine ⟨379027980156010247885615831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252685320104006831923743887 379027980156010247885615831)
    ·
      refine ⟨568541970234015371828423747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379027980156010247885615831 568541970234015371828423747)
      ·
        refine ⟨852812955351023057742635621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568541970234015371828423747 852812955351023057742635621)
        ·
          refine ⟨159902429128316823326744179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 852812955351023057742635621 159902429128316823326744179)
          ·
            refine ⟨239853643692475234990116269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159902429128316823326744179 239853643692475234990116269)
            ·
              refine ⟨89945116384678213121293601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239853643692475234990116269 89945116384678213121293601)
              ·
                refine ⟨67458837288508659840970201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89945116384678213121293601 67458837288508659840970201)
                ·
                  refine ⟨50594127966381494880727651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67458837288508659840970201 50594127966381494880727651)
                  ·
                    refine ⟨75891191949572242321091477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50594127966381494880727651 75891191949572242321091477)
                    ·
                      refine ⟨3557399622636198858801163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75891191949572242321091477 3557399622636198858801163)
                      ·
                        rfl

theorem cell23_6928011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_6928011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928011 prefixEnd_6928011 := by exact prefixLift 6928011
  have htrace : WordTrace (prefixWord ++ tailWord_6928011) baseStart_6928011 baseEnd_6928011 := by
    simpa [prefixWord, tailWord_6928011, baseEnd_6928011] using wordTrace_append hprefix tailTrace_6928011
  have hstable : (prefixWord ++ tailWord_6928011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928011).length < 2 ^ (prefixWord ++ tailWord_6928011).sum := by decide
  have hdescent : baseEnd_6928011 < baseStart_6928011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928086 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6928086 : Nat := 118140960795 + 6928086 * 2 ^ 59
def prefixEnd_6928086 : Nat := 4983230072969 + 3 ^ 40 * 6928086 * 2
def baseEnd_6928086 : Nat := 3557438133685286065363319

theorem tailTrace_6928086 : CollatzResearch.WordTrace tailWord_6928086 prefixEnd_6928086 3557438133685286065363319 := by
  unfold tailWord_6928086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15793003473670944983295257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168458703719156746488482741 15793003473670944983295257)
  ·
    refine ⟨11844752605253208737471443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15793003473670944983295257 11844752605253208737471443)
    ·
      refine ⟨17767128907879813106207165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11844752605253208737471443 17767128907879813106207165)
      ·
        refine ⟨6662673340454929914827687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17767128907879813106207165 6662673340454929914827687)
        ·
          refine ⟨9994010010682394872241531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662673340454929914827687 9994010010682394872241531)
          ·
            refine ⟨14991015016023592308362297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994010010682394872241531 14991015016023592308362297)
            ·
              refine ⟨11243261262017694231271723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14991015016023592308362297 11243261262017694231271723)
              ·
                refine ⟨16864891893026541346907585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243261262017694231271723 16864891893026541346907585)
                ·
                  refine ⟨12648668919769906010180689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16864891893026541346907585 12648668919769906010180689)
                  ·
                    refine ⟨9486501689827429507635517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12648668919769906010180689 9486501689827429507635517)
                    ·
                      refine ⟨3557438133685286065363319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486501689827429507635517 3557438133685286065363319)
                      ·
                        rfl

theorem cell23_6928086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6928086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928086 prefixEnd_6928086 := by exact prefixLift 6928086
  have htrace : WordTrace (prefixWord ++ tailWord_6928086) baseStart_6928086 baseEnd_6928086 := by
    simpa [prefixWord, tailWord_6928086, baseEnd_6928086] using wordTrace_append hprefix tailTrace_6928086
  have hstable : (prefixWord ++ tailWord_6928086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928086).length < 2 ^ (prefixWord ++ tailWord_6928086).sum := by decide
  have hdescent : baseEnd_6928086 < baseStart_6928086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928115 : List Nat := [1, 1, 1, 2, 2, 3, 3, 4, 2, 4]
def baseStart_6928115 : Nat := 118140960795 + 6928115 * 2 ^ 59
def prefixEnd_6928115 : Nat := 4983230072969 + 3 ^ 40 * 6928115 * 2
def baseEnd_6928115 : Nat := 1185817674874755483966895

theorem tailTrace_6928115 : CollatzResearch.WordTrace tailWord_6928115 prefixEnd_6928115 1185817674874755483966895 := by
  unfold tailWord_6928115
  simp only [CollatzResearch.WordTrace]
  refine ⟨252689113295630057685529799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168459408863753371790353199 252689113295630057685529799)
  ·
    refine ⟨379033669943445086528294699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252689113295630057685529799 379033669943445086528294699)
    ·
      refine ⟨568550504915167629792442049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379033669943445086528294699 568550504915167629792442049)
      ·
        refine ⟨426412878686375722344331537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568550504915167629792442049 426412878686375722344331537)
        ·
          refine ⟨319809659014781791758248653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426412878686375722344331537 319809659014781791758248653)
          ·
            refine ⟨119928622130543171909343245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319809659014781791758248653 119928622130543171909343245)
            ·
              refine ⟨44973233298953689466003717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119928622130543171909343245 44973233298953689466003717)
              ·
                refine ⟨8432481243553816774875697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44973233298953689466003717 8432481243553816774875697)
                ·
                  refine ⟨6324360932665362581156773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432481243553816774875697 6324360932665362581156773)
                  ·
                    refine ⟨1185817674874755483966895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324360932665362581156773 1185817674874755483966895)
                    ·
                      rfl

theorem cell23_6928115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 4].length) (baseStart_6928115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928115 prefixEnd_6928115 := by exact prefixLift 6928115
  have htrace : WordTrace (prefixWord ++ tailWord_6928115) baseStart_6928115 baseEnd_6928115 := by
    simpa [prefixWord, tailWord_6928115, baseEnd_6928115] using wordTrace_append hprefix tailTrace_6928115
  have hstable : (prefixWord ++ tailWord_6928115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928115).length < 2 ^ (prefixWord ++ tailWord_6928115).sum := by decide
  have hdescent : baseEnd_6928115 < baseStart_6928115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928122 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2]
def baseStart_6928122 : Nat := 118140960795 + 6928122 * 2 ^ 59
def prefixEnd_6928122 : Nat := 4983230072969 + 3 ^ 40 * 6928122 * 2
def baseEnd_6928122 : Nat := 3557456618988847924513153

theorem tailTrace_6928122 : CollatzResearch.WordTrace tailWord_6928122 prefixEnd_6928122 3557456618988847924513153 := by
  unfold tailWord_6928122
  simp only [CollatzResearch.WordTrace]
  refine ⟨63172342151651174470258655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168459579071069798587356413 63172342151651174470258655)
  ·
    refine ⟨94758513227476761705387983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63172342151651174470258655 94758513227476761705387983)
    ·
      refine ⟨142137769841215142558081975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94758513227476761705387983 142137769841215142558081975)
      ·
        refine ⟨213206654761822713837122963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142137769841215142558081975 213206654761822713837122963)
        ·
          refine ⟨319809982142734070755684445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213206654761822713837122963 319809982142734070755684445)
          ·
            refine ⟨119928743303525276533381667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319809982142734070755684445 119928743303525276533381667)
            ·
              refine ⟨179893114955287914800072501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119928743303525276533381667 179893114955287914800072501)
              ·
                refine ⟨16864979527058242012506797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179893114955287914800072501 16864979527058242012506797)
                ·
                  refine ⟨6324367322646840754690049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16864979527058242012506797 6324367322646840754690049)
                  ·
                    refine ⟨4743275491985130566017537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324367322646840754690049 4743275491985130566017537)
                    ·
                      refine ⟨3557456618988847924513153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743275491985130566017537 3557456618988847924513153)
                      ·
                        rfl

theorem cell23_6928122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2].length) (baseStart_6928122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928122 prefixEnd_6928122 := by exact prefixLift 6928122
  have htrace : WordTrace (prefixWord ++ tailWord_6928122) baseStart_6928122 baseEnd_6928122 := by
    simpa [prefixWord, tailWord_6928122, baseEnd_6928122] using wordTrace_append hprefix tailTrace_6928122
  have hstable : (prefixWord ++ tailWord_6928122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928122).length < 2 ^ (prefixWord ++ tailWord_6928122).sum := by decide
  have hdescent : baseEnd_6928122 < baseStart_6928122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928132 : List Nat := [2, 3, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_6928132 : Nat := 118140960795 + 6928132 * 2 ^ 59
def prefixEnd_6928132 : Nat := 4983230072969 + 3 ^ 40 * 6928132 * 2
def baseEnd_6928132 : Nat := 1185820584598464295129369

theorem tailTrace_6928132 : CollatzResearch.WordTrace tailWord_6928132 prefixEnd_6928132 1185820584598464295129369 := by
  unfold tailWord_6928132
  simp only [CollatzResearch.WordTrace]
  refine ⟨126344866668284234794449325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168459822224378979725932433 126344866668284234794449325)
  ·
    refine ⟨47379325000606588047918497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126344866668284234794449325 47379325000606588047918497)
    ·
      refine ⟨35534493750454941035938873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47379325000606588047918497 35534493750454941035938873)
      ·
        refine ⟨26650870312841205776954155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35534493750454941035938873 26650870312841205776954155)
        ·
          refine ⟨39976305469261808665431233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26650870312841205776954155 39976305469261808665431233)
          ·
            refine ⟨29982229101946356499073425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39976305469261808665431233 29982229101946356499073425)
            ·
              refine ⟨22486671826459767374305069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29982229101946356499073425 22486671826459767374305069)
              ·
                refine ⟨8432501934922412765364401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22486671826459767374305069 8432501934922412765364401)
                ·
                  refine ⟨6324376451191809574023301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432501934922412765364401 6324376451191809574023301)
                  ·
                    refine ⟨1185820584598464295129369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324376451191809574023301 1185820584598464295129369)
                    ·
                      rfl

theorem cell23_6928132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_6928132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928132 prefixEnd_6928132 := by exact prefixLift 6928132
  have htrace : WordTrace (prefixWord ++ tailWord_6928132) baseStart_6928132 baseEnd_6928132 := by
    simpa [prefixWord, tailWord_6928132, baseEnd_6928132] using wordTrace_append hprefix tailTrace_6928132
  have hstable : (prefixWord ++ tailWord_6928132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928132).length < 2 ^ (prefixWord ++ tailWord_6928132).sum := by decide
  have hdescent : baseEnd_6928132 < baseStart_6928132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928155 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 3]
def baseStart_6928155 : Nat := 118140960795 + 6928155 * 2 ^ 59
def prefixEnd_6928155 : Nat := 4983230072969 + 3 ^ 40 * 6928155 * 2
def baseEnd_6928155 : Nat := 3557473563850446295400501

theorem tailTrace_6928155 : CollatzResearch.WordTrace tailWord_6928155 prefixEnd_6928155 3557473563850446295400501 := by
  unfold tailWord_6928155
  simp only [CollatzResearch.WordTrace]
  refine ⟨252690572215485144516985919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168460381476990096344657279 252690572215485144516985919)
  ·
    refine ⟨379035858323227716775478879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252690572215485144516985919 379035858323227716775478879)
    ·
      refine ⟨568553787484841575163218319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379035858323227716775478879 568553787484841575163218319)
      ·
        refine ⟨852830681227262362744827479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568553787484841575163218319 852830681227262362744827479)
        ·
          refine ⟨1279246021840893544117241219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 852830681227262362744827479 1279246021840893544117241219)
          ·
            refine ⟨1918869032761340316175861829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1279246021840893544117241219 1918869032761340316175861829)
            ·
              refine ⟨359787943642751309282974093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1918869032761340316175861829 359787943642751309282974093)
              ·
                refine ⟨134920478866031740981115285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 359787943642751309282974093 134920478866031740981115285)
                ·
                  refine ⟨6324397446845237858489779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134920478866031740981115285 6324397446845237858489779)
                  ·
                    refine ⟨9486596170267856787734669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324397446845237858489779 9486596170267856787734669)
                    ·
                      refine ⟨3557473563850446295400501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486596170267856787734669 3557473563850446295400501)
                      ·
                        rfl

theorem cell23_6928155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 3].length) (baseStart_6928155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928155 prefixEnd_6928155 := by exact prefixLift 6928155
  have htrace : WordTrace (prefixWord ++ tailWord_6928155) baseStart_6928155 baseEnd_6928155 := by
    simpa [prefixWord, tailWord_6928155, baseEnd_6928155] using wordTrace_append hprefix tailTrace_6928155
  have hstable : (prefixWord ++ tailWord_6928155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928155).length < 2 ^ (prefixWord ++ tailWord_6928155).sum := by decide
  have hdescent : baseEnd_6928155 < baseStart_6928155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928156 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 1, 2, 2]
def baseStart_6928156 : Nat := 118140960795 + 6928156 * 2 ^ 59
def prefixEnd_6928156 : Nat := 4983230072969 + 3 ^ 40 * 6928156 * 2
def baseEnd_6928156 : Nat := 3557474077331100791487997

theorem tailTrace_6928156 : CollatzResearch.WordTrace tailWord_6928156 prefixEnd_6928156 3557474077331100791487997 := by
  unfold tailWord_6928156
  simp only [CollatzResearch.WordTrace]
  refine ⟨126345304344240760843886161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168460405792321014458514881 126345304344240760843886161)
  ·
    refine ⟨94758978258180570632914621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126345304344240760843886161 94758978258180570632914621)
    ·
      refine ⟨35534616846817713987342983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94758978258180570632914621 35534616846817713987342983)
      ·
        refine ⟨53301925270226570981014475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35534616846817713987342983 53301925270226570981014475)
        ·
          refine ⟨79952887905339856471521713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53301925270226570981014475 79952887905339856471521713)
          ·
            refine ⟨59964665929004892353641285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79952887905339856471521713 59964665929004892353641285)
            ·
              refine ⟨11243374861688417316307741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59964665929004892353641285 11243374861688417316307741)
              ·
                refine ⟨4216265573133156493615403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11243374861688417316307741 4216265573133156493615403)
                ·
                  refine ⟨6324398359699734740423105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216265573133156493615403 6324398359699734740423105)
                  ·
                    refine ⟨4743298769774801055317329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324398359699734740423105 4743298769774801055317329)
                    ·
                      refine ⟨3557474077331100791487997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743298769774801055317329 3557474077331100791487997)
                      ·
                        rfl

theorem cell23_6928156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_6928156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928156 prefixEnd_6928156 := by exact prefixLift 6928156
  have htrace : WordTrace (prefixWord ++ tailWord_6928156) baseStart_6928156 baseEnd_6928156 := by
    simpa [prefixWord, tailWord_6928156, baseEnd_6928156] using wordTrace_append hprefix tailTrace_6928156
  have hstable : (prefixWord ++ tailWord_6928156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928156).length < 2 ^ (prefixWord ++ tailWord_6928156).sum := by decide
  have hdescent : baseEnd_6928156 < baseStart_6928156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928172 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 3]
def baseStart_6928172 : Nat := 118140960795 + 6928172 * 2 ^ 59
def prefixEnd_6928172 : Nat := 4983230072969 + 3 ^ 40 * 6928172 * 2
def baseEnd_6928172 : Nat := 3557482293021572728887923

theorem tailTrace_6928172 : CollatzResearch.WordTrace tailWord_6928172 prefixEnd_6928172 3557482293021572728887923 := by
  unfold tailWord_6928172
  simp only [CollatzResearch.WordTrace]
  refine ⟨126345596128211778210177385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168460794837615704280236513 126345596128211778210177385)
  ·
    refine ⟨94759197096158833657633039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126345596128211778210177385 94759197096158833657633039)
    ·
      refine ⟨142138795644238250486449559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94759197096158833657633039 142138795644238250486449559)
      ·
        refine ⟨213208193466357375729674339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142138795644238250486449559 213208193466357375729674339)
        ·
          refine ⟨319812290199536063594511509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213208193466357375729674339 319812290199536063594511509)
          ·
            refine ⟨14991201103103252980992727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 319812290199536063594511509 14991201103103252980992727)
            ·
              refine ⟨22486801654654879471489091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14991201103103252980992727 22486801654654879471489091)
              ·
                refine ⟨33730202481982319207233637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22486801654654879471489091 33730202481982319207233637)
                ·
                  refine ⟨6324412965371684851356307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33730202481982319207233637 6324412965371684851356307)
                  ·
                    refine ⟨9486619448057527277034461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324412965371684851356307 9486619448057527277034461)
                    ·
                      refine ⟨3557482293021572728887923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486619448057527277034461 3557482293021572728887923)
                      ·
                        rfl

theorem cell23_6928172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 3].length) (baseStart_6928172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928172 prefixEnd_6928172 := by exact prefixLift 6928172
  have htrace : WordTrace (prefixWord ++ tailWord_6928172) baseStart_6928172 baseEnd_6928172 := by
    simpa [prefixWord, tailWord_6928172, baseEnd_6928172] using wordTrace_append hprefix tailTrace_6928172
  have hstable : (prefixWord ++ tailWord_6928172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928172).length < 2 ^ (prefixWord ++ tailWord_6928172).sum := by decide
  have hdescent : baseEnd_6928172 < baseStart_6928172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928189 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6928189 : Nat := 118140960795 + 6928189 * 2 ^ 59
def prefixEnd_6928189 : Nat := 4983230072969 + 3 ^ 40 * 6928189 * 2
def baseEnd_6928189 : Nat := 3557491022192699162375345

theorem tailTrace_6928189 : CollatzResearch.WordTrace tailWord_6928189 prefixEnd_6928189 3557491022192699162375345 := by
  unfold tailWord_6928189
  simp only [CollatzResearch.WordTrace]
  refine ⟨252691812297361968323723621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168461208198241312215815747 252691812297361968323723621)
  ·
    refine ⟨47379714805755369060698179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252691812297361968323723621 47379714805755369060698179)
    ·
      refine ⟨71069572208633053591047269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47379714805755369060698179 71069572208633053591047269)
      ·
        refine ⟨13325544789118697548321363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71069572208633053591047269 13325544789118697548321363)
        ·
          refine ⟨19988317183678046322482045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13325544789118697548321363 19988317183678046322482045)
          ·
            refine ⟨7495618943879267370930767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19988317183678046322482045 7495618943879267370930767)
            ·
              refine ⟨11243428415818901056396151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495618943879267370930767 11243428415818901056396151)
              ·
                refine ⟨16865142623728351584594227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243428415818901056396151 16865142623728351584594227)
                ·
                  refine ⟨25297713935592527376891341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16865142623728351584594227 25297713935592527376891341)
                  ·
                    refine ⟨9486642725847197766334253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25297713935592527376891341 9486642725847197766334253)
                    ·
                      refine ⟨3557491022192699162375345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486642725847197766334253 3557491022192699162375345)
                      ·
                        rfl

theorem cell23_6928189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6928189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928189 prefixEnd_6928189 := by exact prefixLift 6928189
  have htrace : WordTrace (prefixWord ++ tailWord_6928189) baseStart_6928189 baseEnd_6928189 := by
    simpa [prefixWord, tailWord_6928189, baseEnd_6928189] using wordTrace_append hprefix tailTrace_6928189
  have hstable : (prefixWord ++ tailWord_6928189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928189).length < 2 ^ (prefixWord ++ tailWord_6928189).sum := by decide
  have hdescent : baseEnd_6928189 < baseStart_6928189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928229 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 2, 2, 2]
def baseStart_6928229 : Nat := 118140960795 + 6928229 * 2 ^ 59
def prefixEnd_6928229 : Nat := 4983230072969 + 3 ^ 40 * 6928229 * 2
def baseEnd_6928229 : Nat := 3557511561418879005875161

theorem tailTrace_6928229 : CollatzResearch.WordTrace tailWord_6928229 prefixEnd_6928229 3557511561418879005875161 := by
  unfold tailWord_6928229
  simp only [CollatzResearch.WordTrace]
  refine ⟨252693271217217055155179741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168462180811478036770119827 252693271217217055155179741)
  ·
    refine ⟨94759976706456395683192403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252693271217217055155179741 94759976706456395683192403)
    ·
      refine ⟨142139965059684593524788605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94759976706456395683192403 142139965059684593524788605)
      ·
        refine ⟨53302486897381722571795727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142139965059684593524788605 53302486897381722571795727)
        ·
          refine ⟨79953730346072583857693591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53302486897381722571795727 79953730346072583857693591)
          ·
            refine ⟨119930595519108875786540387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79953730346072583857693591 119930595519108875786540387)
            ·
              refine ⟨179895893278663313679810581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119930595519108875786540387 179895893278663313679810581)
              ·
                refine ⟨8432619997437342828741121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 179895893278663313679810581 8432619997437342828741121)
                ·
                  refine ⟨6324464998078007121555841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432619997437342828741121 6324464998078007121555841)
                  ·
                    refine ⟨4743348748558505341166881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324464998078007121555841 4743348748558505341166881)
                    ·
                      refine ⟨3557511561418879005875161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743348748558505341166881 3557511561418879005875161)
                      ·
                        rfl

theorem cell23_6928229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_6928229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928229 prefixEnd_6928229 := by exact prefixLift 6928229
  have htrace : WordTrace (prefixWord ++ tailWord_6928229) baseStart_6928229 baseEnd_6928229 := by
    simpa [prefixWord, tailWord_6928229, baseEnd_6928229] using wordTrace_append hprefix tailTrace_6928229
  have hstable : (prefixWord ++ tailWord_6928229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928229).length < 2 ^ (prefixWord ++ tailWord_6928229).sum := by decide
  have hdescent : baseEnd_6928229 < baseStart_6928229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928282 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 2, 5]
def baseStart_6928282 : Nat := 118140960795 + 6928282 * 2 ^ 59
def prefixEnd_6928282 : Nat := 4983230072969 + 3 ^ 40 * 6928282 * 2
def baseEnd_6928282 : Nat := 1185846258631189099504139

theorem tailTrace_6928282 : CollatzResearch.WordTrace tailWord_6928282 prefixEnd_6928282 1185846258631189099504139 := by
  unfold tailWord_6928282
  simp only [CollatzResearch.WordTrace]
  refine ⟨63173801071506261301714775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168463469524016696804572733 63173801071506261301714775)
  ·
    refine ⟨94760701607259391952572163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63173801071506261301714775 94760701607259391952572163)
    ·
      refine ⟨142141052410889087928858245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94760701607259391952572163 142141052410889087928858245)
      ·
        refine ⟨26651447327041703986660921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142141052410889087928858245 26651447327041703986660921)
        ·
          refine ⟨19988585495281277989995691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26651447327041703986660921 19988585495281277989995691)
          ·
            refine ⟨29982878242921916984993537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19988585495281277989995691 29982878242921916984993537)
            ·
              refine ⟨22487158682191437738745153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29982878242921916984993537 22487158682191437738745153)
              ·
                refine ⟨16865369011643578304058865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22487158682191437738745153 16865369011643578304058865)
                ·
                  refine ⟨12649026758732683728044149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16865369011643578304058865 12649026758732683728044149)
                  ·
                    refine ⟨1185846258631189099504139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12649026758732683728044149 1185846258631189099504139)
                    ·
                      rfl

theorem cell23_6928282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_6928282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928282 prefixEnd_6928282 := by exact prefixLift 6928282
  have htrace : WordTrace (prefixWord ++ tailWord_6928282) baseStart_6928282 baseEnd_6928282 := by
    simpa [prefixWord, tailWord_6928282, baseEnd_6928282] using wordTrace_append hprefix tailTrace_6928282
  have hstable : (prefixWord ++ tailWord_6928282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928282).length < 2 ^ (prefixWord ++ tailWord_6928282).sum := by decide
  have hdescent : baseEnd_6928282 < baseStart_6928282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928296 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_6928296 : Nat := 118140960795 + 6928296 * 2 ^ 59
def prefixEnd_6928296 : Nat := 4983230072969 + 3 ^ 40 * 6928296 * 2
def baseEnd_6928296 : Nat := 3557545964622730243737353

theorem tailTrace_6928296 : CollatzResearch.WordTrace tailWord_6928296 prefixEnd_6928296 3557545964622730243737353 := by
  unfold tailWord_6928296
  simp only [CollatzResearch.WordTrace]
  refine ⟨126347857453987162798934371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168463809938649550398579161 126347857453987162798934371)
  ·
    refine ⟨189521786180980744198401557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126347857453987162798934371 189521786180980744198401557)
    ·
      refine ⟨8883833727233472384300073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 189521786180980744198401557 8883833727233472384300073)
      ·
        refine ⟨6662875295425104288225055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8883833727233472384300073 6662875295425104288225055)
        ·
          refine ⟨9994312943137656432337583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662875295425104288225055 9994312943137656432337583)
          ·
            refine ⟨14991469414706484648506375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994312943137656432337583 14991469414706484648506375)
            ·
              refine ⟨22487204122059726972759563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14991469414706484648506375 22487204122059726972759563)
              ·
                refine ⟨33730806183089590459139345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22487204122059726972759563 33730806183089590459139345)
                ·
                  refine ⟨25298104637317192844354509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33730806183089590459139345 25298104637317192844354509)
                  ·
                    refine ⟨9486789238993947316632941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25298104637317192844354509 9486789238993947316632941)
                    ·
                      refine ⟨3557545964622730243737353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9486789238993947316632941 3557545964622730243737353)
                      ·
                        rfl

theorem cell23_6928296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_6928296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928296 prefixEnd_6928296 := by exact prefixLift 6928296
  have htrace : WordTrace (prefixWord ++ tailWord_6928296) baseStart_6928296 baseEnd_6928296 := by
    simpa [prefixWord, tailWord_6928296, baseEnd_6928296] using wordTrace_append hprefix tailTrace_6928296
  have hstable : (prefixWord ++ tailWord_6928296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928296).length < 2 ^ (prefixWord ++ tailWord_6928296).sum := by decide
  have hdescent : baseEnd_6928296 < baseStart_6928296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928312 : List Nat := [2, 1, 2, 1, 2, 3, 3, 2, 3, 4]
def baseStart_6928312 : Nat := 118140960795 + 6928312 * 2 ^ 59
def prefixEnd_6928312 : Nat := 4983230072969 + 3 ^ 40 * 6928312 * 2
def baseEnd_6928312 : Nat := 1185851393437734060379093

theorem tailTrace_6928312 : CollatzResearch.WordTrace tailWord_6928312 prefixEnd_6928312 1185851393437734060379093 := by
  unfold tailWord_6928312
  simp only [CollatzResearch.WordTrace]
  refine ⟨126348149237958180165225595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168464198983944240220300793 126348149237958180165225595)
  ·
    refine ⟨189522223856937270247838393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126348149237958180165225595 189522223856937270247838393)
    ·
      refine ⟨142141667892702952685878795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189522223856937270247838393 142141667892702952685878795)
      ·
        refine ⟨213212501839054429028818193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142141667892702952685878795 213212501839054429028818193)
        ·
          refine ⟨159909376379290821771613645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213212501839054429028818193 159909376379290821771613645)
          ·
            refine ⟨59966016142234058164355117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159909376379290821771613645 59966016142234058164355117)
            ·
              refine ⟨22487256053337771811633169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59966016142234058164355117 22487256053337771811633169)
              ·
                refine ⟨16865442040003328858724877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22487256053337771811633169 16865442040003328858724877)
                ·
                  refine ⟨6324540765001248322021829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16865442040003328858724877 6324540765001248322021829)
                  ·
                    refine ⟨1185851393437734060379093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324540765001248322021829 1185851393437734060379093)
                    ·
                      rfl

theorem cell23_6928312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_6928312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928312 prefixEnd_6928312 := by exact prefixLift 6928312
  have htrace : WordTrace (prefixWord ++ tailWord_6928312) baseStart_6928312 baseEnd_6928312 := by
    simpa [prefixWord, tailWord_6928312, baseEnd_6928312] using wordTrace_append hprefix tailTrace_6928312
  have hstable : (prefixWord ++ tailWord_6928312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928312).length < 2 ^ (prefixWord ++ tailWord_6928312).sum := by decide
  have hdescent : baseEnd_6928312 < baseStart_6928312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928316 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_6928316 : Nat := 118140960795 + 6928316 * 2 ^ 59
def prefixEnd_6928316 : Nat := 4983230072969 + 3 ^ 40 * 6928316 * 2
def baseEnd_6928316 : Nat := 1185852078078606721829087

theorem tailTrace_6928316 : CollatzResearch.WordTrace tailWord_6928316 prefixEnd_6928316 1185852078078606721829087 := by
  unfold tailWord_6928316
  simp only [CollatzResearch.WordTrace]
  refine ⟨126348222183950934506798401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168464296245267912675731201 126348222183950934506798401)
  ·
    refine ⟨94761166637963200880098801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126348222183950934506798401 94761166637963200880098801)
    ·
      refine ⟨71070874978472400660074101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94761166637963200880098801 71070874978472400660074101)
      ·
        refine ⟨6662894529231787561881947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71070874978472400660074101 6662894529231787561881947)
        ·
          refine ⟨9994341793847681342822921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6662894529231787561881947 9994341793847681342822921)
          ·
            refine ⟨7495756345385761007117191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994341793847681342822921 7495756345385761007117191)
            ·
              refine ⟨11243634518078641510675787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495756345385761007117191 11243634518078641510675787)
              ·
                refine ⟨16865451777117962266013681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243634518078641510675787 16865451777117962266013681)
                ·
                  refine ⟨12649088832838471699510261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16865451777117962266013681 12649088832838471699510261)
                  ·
                    refine ⟨1185852078078606721829087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12649088832838471699510261 1185852078078606721829087)
                    ·
                      rfl

theorem cell23_6928316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_6928316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928316 prefixEnd_6928316 := by exact prefixLift 6928316
  have htrace : WordTrace (prefixWord ++ tailWord_6928316) baseStart_6928316 baseEnd_6928316 := by
    simpa [prefixWord, tailWord_6928316, baseEnd_6928316] using wordTrace_append hprefix tailTrace_6928316
  have hstable : (prefixWord ++ tailWord_6928316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928316).length < 2 ^ (prefixWord ++ tailWord_6928316).sum := by decide
  have hdescent : baseEnd_6928316 < baseStart_6928316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928375 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_6928375 : Nat := 118140960795 + 6928375 * 2 ^ 59
def prefixEnd_6928375 : Nat := 4983230072969 + 3 ^ 40 * 6928375 * 2
def baseEnd_6928375 : Nat := 3557586529594435434649489

theorem tailTrace_6928375 : CollatzResearch.WordTrace tailWord_6928375 prefixEnd_6928375 3557586529594435434649489 := by
  unfold tailWord_6928375
  simp only [CollatzResearch.WordTrace]
  refine ⟨252698596274688122089994579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168465730849792081393329719 252698596274688122089994579)
  ·
    refine ⟨379047894412032183134991869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252698596274688122089994579 379047894412032183134991869)
    ·
      refine ⟨142142960404512068675621951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379047894412032183134991869 142142960404512068675621951)
      ·
        refine ⟨213214440606768103013432927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142142960404512068675621951 213214440606768103013432927)
        ·
          refine ⟨319821660910152154520149391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213214440606768103013432927 319821660910152154520149391)
          ·
            refine ⟨479732491365228231780224087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319821660910152154520149391 479732491365228231780224087)
            ·
              refine ⟨719598737047842347670336131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479732491365228231780224087 719598737047842347670336131)
              ·
                refine ⟨1079398105571763521505504197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719598737047842347670336131 1079398105571763521505504197)
                ·
                  refine ⟨202387144794705660282282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1079398105571763521505504197 202387144794705660282282037)
                  ·
                    refine ⟨18973794824503655651463941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202387144794705660282282037 18973794824503655651463941)
                    ·
                      refine ⟨3557586529594435434649489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18973794824503655651463941 3557586529594435434649489)
                      ·
                        rfl

theorem cell23_6928375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_6928375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928375 prefixEnd_6928375 := by exact prefixLift 6928375
  have htrace : WordTrace (prefixWord ++ tailWord_6928375) baseStart_6928375 baseEnd_6928375 := by
    simpa [prefixWord, tailWord_6928375, baseEnd_6928375] using wordTrace_append hprefix tailTrace_6928375
  have hstable : (prefixWord ++ tailWord_6928375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928375).length < 2 ^ (prefixWord ++ tailWord_6928375).sum := by decide
  have hdescent : baseEnd_6928375 < baseStart_6928375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928397 : List Nat := [1, 7, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_6928397 : Nat := 118140960795 + 6928397 * 2 ^ 59
def prefixEnd_6928397 : Nat := 4983230072969 + 3 ^ 40 * 6928397 * 2
def baseEnd_6928397 : Nat := 1185865942056278116191463

theorem tailTrace_6928397 : CollatzResearch.WordTrace tailWord_6928397 prefixEnd_6928397 1185865942056278116191463 := by
  unfold tailWord_6928397
  simp only [CollatzResearch.WordTrace]
  refine ⟨252699398680608419847295445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168466265787072279898196963 252699398680608419847295445)
  ·
    refine ⟨5922642156576759840170987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 252699398680608419847295445 5922642156576759840170987)
    ·
      refine ⟨8883963234865139760256481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5922642156576759840170987 8883963234865139760256481)
      ·
        refine ⟨6662972426148854820192361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8883963234865139760256481 6662972426148854820192361)
        ·
          refine ⟨4997229319611641115144271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6662972426148854820192361 4997229319611641115144271)
          ·
            refine ⟨7495843979417461672716407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997229319611641115144271 7495843979417461672716407)
            ·
              refine ⟨11243765969126192509074611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495843979417461672716407 11243765969126192509074611)
              ·
                refine ⟨16865648953689288763611917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243765969126192509074611 16865648953689288763611917)
                ·
                  refine ⟨6324618357633483286354469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16865648953689288763611917 6324618357633483286354469)
                  ·
                    refine ⟨1185865942056278116191463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324618357633483286354469 1185865942056278116191463)
                    ·
                      rfl

theorem cell23_6928397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_6928397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928397 prefixEnd_6928397 := by exact prefixLift 6928397
  have htrace : WordTrace (prefixWord ++ tailWord_6928397) baseStart_6928397 baseEnd_6928397 := by
    simpa [prefixWord, tailWord_6928397, baseEnd_6928397] using wordTrace_append hprefix tailTrace_6928397
  have hstable : (prefixWord ++ tailWord_6928397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928397).length < 2 ^ (prefixWord ++ tailWord_6928397).sum := by decide
  have hdescent : baseEnd_6928397 < baseStart_6928397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928419 : List Nat := [1, 1, 1, 4, 3, 1, 3, 3, 2, 4]
def baseStart_6928419 : Nat := 118140960795 + 6928419 * 2 ^ 59
def prefixEnd_6928419 : Nat := 4983230072969 + 3 ^ 40 * 6928419 * 2
def baseEnd_6928419 : Nat := 1185869707581077754166429

theorem tailTrace_6928419 : CollatzResearch.WordTrace tailWord_6928419 prefixEnd_6928419 1185869707581077754166429 := by
  unfold tailWord_6928419
  simp only [CollatzResearch.WordTrace]
  refine ⟨252700201086528717604596311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168466800724352478403064207 252700201086528717604596311)
  ·
    refine ⟨379050301629793076406894467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252700201086528717604596311 379050301629793076406894467)
    ·
      refine ⟨568575452444689614610341701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379050301629793076406894467 568575452444689614610341701)
      ·
        refine ⟨106607897333379302739439069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 568575452444689614610341701 106607897333379302739439069)
        ·
          refine ⟨39977961500017238527289651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106607897333379302739439069 39977961500017238527289651)
          ·
            refine ⟨59966942250025857790934477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39977961500017238527289651 59966942250025857790934477)
            ·
              refine ⟨22487603343759696671600429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59966942250025857790934477 22487603343759696671600429)
              ·
                refine ⟨8432851253909886251850161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22487603343759696671600429 8432851253909886251850161)
                ·
                  refine ⟨6324638440432414688887621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8432851253909886251850161 6324638440432414688887621)
                  ·
                    refine ⟨1185869707581077754166429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324638440432414688887621 1185869707581077754166429)
                    ·
                      rfl

theorem cell23_6928419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 2, 4].length) (baseStart_6928419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928419 prefixEnd_6928419 := by exact prefixLift 6928419
  have htrace : WordTrace (prefixWord ++ tailWord_6928419) baseStart_6928419 baseEnd_6928419 := by
    simpa [prefixWord, tailWord_6928419, baseEnd_6928419] using wordTrace_append hprefix tailTrace_6928419
  have hstable : (prefixWord ++ tailWord_6928419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928419).length < 2 ^ (prefixWord ++ tailWord_6928419).sum := by decide
  have hdescent : baseEnd_6928419 < baseStart_6928419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928423 : List Nat := [1, 1, 7, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6928423 : Nat := 118140960795 + 6928423 * 2 ^ 59
def prefixEnd_6928423 : Nat := 4983230072969 + 3 ^ 40 * 6928423 * 2
def baseEnd_6928423 : Nat := 1185870392221950415616423

theorem tailTrace_6928423 : CollatzResearch.WordTrace tailWord_6928423 prefixEnd_6928423 1185870392221950415616423 := by
  unfold tailWord_6928423
  simp only [CollatzResearch.WordTrace]
  refine ⟨252700346978514226287741923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168466897985676150858494615 252700346978514226287741923)
  ·
    refine ⟨379050520467771339431612885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252700346978514226287741923 379050520467771339431612885)
    ·
      refine ⟨8883996573463390767928427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 379050520467771339431612885 8883996573463390767928427)
      ·
        refine ⟨13325994860195086151892641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8883996573463390767928427 13325994860195086151892641)
        ·
          refine ⟨9994496145146314613919481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13325994860195086151892641 9994496145146314613919481)
          ·
            refine ⟨7495872108859735960439611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994496145146314613919481 7495872108859735960439611)
            ·
              refine ⟨11243808163289603940659417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495872108859735960439611 11243808163289603940659417)
              ·
                refine ⟨8432856122467202955494563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11243808163289603940659417 8432856122467202955494563)
                ·
                  refine ⟨12649284183700804433241845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432856122467202955494563 12649284183700804433241845)
                  ·
                    refine ⟨1185870392221950415616423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12649284183700804433241845 1185870392221950415616423)
                    ·
                      rfl

theorem cell23_6928423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6928423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928423 prefixEnd_6928423 := by exact prefixLift 6928423
  have htrace : WordTrace (prefixWord ++ tailWord_6928423) baseStart_6928423 baseEnd_6928423 := by
    simpa [prefixWord, tailWord_6928423, baseEnd_6928423] using wordTrace_append hprefix tailTrace_6928423
  have hstable : (prefixWord ++ tailWord_6928423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928423).length < 2 ^ (prefixWord ++ tailWord_6928423).sum := by decide
  have hdescent : baseEnd_6928423 < baseStart_6928423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928426 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6928426 : Nat := 118140960795 + 6928426 * 2 ^ 59
def prefixEnd_6928426 : Nat := 4983230072969 + 3 ^ 40 * 6928426 * 2
def baseEnd_6928426 : Nat := 3557612717107814735111755

theorem tailTrace_6928426 : CollatzResearch.WordTrace tailWord_6928426 prefixEnd_6928426 3557612717107814735111755 := by
  unfold tailWord_6928426
  simp only [CollatzResearch.WordTrace]
  refine ⟨63175114099375839450025283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168466970931668905200067421 63175114099375839450025283)
  ·
    refine ⟨94762671149063759175037925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63175114099375839450025283 94762671149063759175037925)
    ·
      refine ⟨17768000840449454845319611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94762671149063759175037925 17768000840449454845319611)
      ·
        refine ⟨26652001260674182267979417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768000840449454845319611 26652001260674182267979417)
        ·
          refine ⟨19989000945505636700984563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26652001260674182267979417 19989000945505636700984563)
          ·
            refine ⟨29983501418258455051476845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19989000945505636700984563 29983501418258455051476845)
            ·
              refine ⟨11243813031846920644303817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29983501418258455051476845 11243813031846920644303817)
              ·
                refine ⟨8432859773885190483227863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11243813031846920644303817 8432859773885190483227863)
                ·
                  refine ⟨12649289660827785724841795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432859773885190483227863 12649289660827785724841795)
                  ·
                    refine ⟨18973934491241678587262693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12649289660827785724841795 18973934491241678587262693)
                    ·
                      refine ⟨3557612717107814735111755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18973934491241678587262693 3557612717107814735111755)
                      ·
                        rfl

theorem cell23_6928426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6928426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928426 prefixEnd_6928426 := by exact prefixLift 6928426
  have htrace : WordTrace (prefixWord ++ tailWord_6928426) baseStart_6928426 baseEnd_6928426 := by
    simpa [prefixWord, tailWord_6928426, baseEnd_6928426] using wordTrace_append hprefix tailTrace_6928426
  have hstable : (prefixWord ++ tailWord_6928426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928426).length < 2 ^ (prefixWord ++ tailWord_6928426).sum := by decide
  have hdescent : baseEnd_6928426 < baseStart_6928426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928436 : List Nat := [2, 5, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_6928436 : Nat := 118140960795 + 6928436 * 2 ^ 59
def prefixEnd_6928436 : Nat := 4983230072969 + 3 ^ 40 * 6928436 * 2
def baseEnd_6928436 : Nat := 1185872617304786565328903

theorem tailTrace_6928436 : CollatzResearch.WordTrace tailWord_6928436 prefixEnd_6928436 1185872617304786565328903 := by
  unfold tailWord_6928436
  simp only [CollatzResearch.WordTrace]
  refine ⟨126350410563733564753982581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168467214084978086338643441 126350410563733564753982581)
  ·
    refine ⟨11845350990350021695685867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126350410563733564753982581 11845350990350021695685867)
    ·
      refine ⟨17768026485525032543528801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845350990350021695685867 17768026485525032543528801)
      ·
        refine ⟨13326019864143774407646601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17768026485525032543528801 13326019864143774407646601)
        ·
          refine ⟨9994514898107830805734951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13326019864143774407646601 9994514898107830805734951)
          ·
            refine ⟨14991772347161746208602427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994514898107830805734951 14991772347161746208602427)
            ·
              refine ⟨22487658520742619312903641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14991772347161746208602427 22487658520742619312903641)
              ·
                refine ⟨16865743890556964484677731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22487658520742619312903641 16865743890556964484677731)
                ·
                  refine ⟨25298615835835446727016597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16865743890556964484677731 25298615835835446727016597)
                  ·
                    refine ⟨1185872617304786565328903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25298615835835446727016597 1185872617304786565328903)
                    ·
                      rfl

theorem cell23_6928436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_6928436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928436 prefixEnd_6928436 := by exact prefixLift 6928436
  have htrace : WordTrace (prefixWord ++ tailWord_6928436) baseStart_6928436 baseEnd_6928436 := by
    simpa [prefixWord, tailWord_6928436, baseEnd_6928436] using wordTrace_append hprefix tailTrace_6928436
  have hstable : (prefixWord ++ tailWord_6928436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928436).length < 2 ^ (prefixWord ++ tailWord_6928436).sum := by decide
  have hdescent : baseEnd_6928436 < baseStart_6928436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928460 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 1, 2, 2]
def baseStart_6928460 : Nat := 118140960795 + 6928460 * 2 ^ 59
def prefixEnd_6928460 : Nat := 4983230072969 + 3 ^ 40 * 6928460 * 2
def baseEnd_6928460 : Nat := 3557630175450067602086599

theorem tailTrace_6928460 : CollatzResearch.WordTrace tailWord_6928460 prefixEnd_6928460 3557630175450067602086599 := by
  unfold tailWord_6928460
  simp only [CollatzResearch.WordTrace]
  refine ⟨126350848239690090803419417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168467797652920121071225889 126350848239690090803419417)
  ·
    refine ⟨94763136179767568102564563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126350848239690090803419417 94763136179767568102564563)
    ·
      refine ⟨142144704269651352153846845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94763136179767568102564563 142144704269651352153846845)
      ·
        refine ⟨53304264101119257057692567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142144704269651352153846845 53304264101119257057692567)
        ·
          refine ⟨79956396151678885586538851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53304264101119257057692567 79956396151678885586538851)
          ·
            refine ⟨119934594227518328379808277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79956396151678885586538851 119934594227518328379808277)
            ·
              refine ⟨5621934104414921642803513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 119934594227518328379808277 5621934104414921642803513)
              ·
                refine ⟨4216450578311191232102635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5621934104414921642803513 4216450578311191232102635)
                ·
                  refine ⟨6324675867466786848153953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216450578311191232102635 6324675867466786848153953)
                  ·
                    refine ⟨4743506900600090136115465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324675867466786848153953 4743506900600090136115465)
                    ·
                      refine ⟨3557630175450067602086599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743506900600090136115465 3557630175450067602086599)
                      ·
                        rfl

theorem cell23_6928460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 2, 2].length) (baseStart_6928460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928460 prefixEnd_6928460 := by exact prefixLift 6928460
  have htrace : WordTrace (prefixWord ++ tailWord_6928460) baseStart_6928460 baseEnd_6928460 := by
    simpa [prefixWord, tailWord_6928460, baseEnd_6928460] using wordTrace_append hprefix tailTrace_6928460
  have hstable : (prefixWord ++ tailWord_6928460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928460).length < 2 ^ (prefixWord ++ tailWord_6928460).sum := by decide
  have hdescent : baseEnd_6928460 < baseStart_6928460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928462 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_6928462 : Nat := 118140960795 + 6928462 * 2 ^ 59
def prefixEnd_6928462 : Nat := 4983230072969 + 3 ^ 40 * 6928462 * 2
def baseEnd_6928462 : Nat := 1185877067470458864753863

theorem tailTrace_6928462 : CollatzResearch.WordTrace tailWord_6928462 prefixEnd_6928462 1185877067470458864753863 := by
  unfold tailWord_6928462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31587721178171616993551455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168467846283581957298941093 31587721178171616993551455)
  ·
    refine ⟨47381581767257425490327183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31587721178171616993551455 47381581767257425490327183)
    ·
      refine ⟨71072372650886138235490775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47381581767257425490327183 71072372650886138235490775)
      ·
        refine ⟨106608558976329207353236163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71072372650886138235490775 106608558976329207353236163)
        ·
          refine ⟨159912838464493811029854245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106608558976329207353236163 159912838464493811029854245)
          ·
            refine ⟨29983657212092589568097671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159912838464493811029854245 29983657212092589568097671)
            ·
              refine ⟨44975485818138884352146507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29983657212092589568097671 44975485818138884352146507)
              ·
                refine ⟨67463228727208326528219761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44975485818138884352146507 67463228727208326528219761)
                ·
                  refine ⟨50597421545406244896164821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67463228727208326528219761 50597421545406244896164821)
                  ·
                    refine ⟨1185877067470458864753863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50597421545406244896164821 1185877067470458864753863)
                    ·
                      rfl

theorem cell23_6928462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_6928462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928462 prefixEnd_6928462 := by exact prefixLift 6928462
  have htrace : WordTrace (prefixWord ++ tailWord_6928462) baseStart_6928462 baseEnd_6928462 := by
    simpa [prefixWord, tailWord_6928462, baseEnd_6928462] using wordTrace_append hprefix tailTrace_6928462
  have hstable : (prefixWord ++ tailWord_6928462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928462).length < 2 ^ (prefixWord ++ tailWord_6928462).sum := by decide
  have hdescent : baseEnd_6928462 < baseStart_6928462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928466 : List Nat := [3, 2, 2, 1, 5, 1, 1, 8]
def baseStart_6928466 : Nat := 118140960795 + 6928466 * 2 ^ 59
def prefixEnd_6928466 : Nat := 4983230072969 + 3 ^ 40 * 6928466 * 2
def baseEnd_6928466 : Nat := 131764194679036836244873

theorem tailTrace_6928466 : CollatzResearch.WordTrace tailWord_6928466 prefixEnd_6928466 131764194679036836244873 := by
  unfold tailWord_6928466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63175478829339611157889313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168467943544905629754371501 63175478829339611157889313)
  ·
    refine ⟨47381609122004708368416985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63175478829339611157889313 47381609122004708368416985)
    ·
      refine ⟨35536206841503531276312739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47381609122004708368416985 35536206841503531276312739)
      ·
        refine ⟨53304310262255296914469109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35536206841503531276312739 53304310262255296914469109)
        ·
          refine ⟨4997279087086434085731479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53304310262255296914469109 4997279087086434085731479)
          ·
            refine ⟨7495918630629651128597219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997279087086434085731479 7495918630629651128597219)
            ·
              refine ⟨11243877945944476692895829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7495918630629651128597219 11243877945944476692895829)
              ·
                refine ⟨131764194679036836244873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11243877945944476692895829 131764194679036836244873)
                ·
                  rfl

theorem cell23_6928466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 1, 8].length) (baseStart_6928466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928466 prefixEnd_6928466 := by exact prefixLift 6928466
  have htrace : WordTrace (prefixWord ++ tailWord_6928466) baseStart_6928466 baseEnd_6928466 := by
    simpa [prefixWord, tailWord_6928466, baseEnd_6928466] using wordTrace_append hprefix tailTrace_6928466
  have hstable : (prefixWord ++ tailWord_6928466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928466).length < 2 ^ (prefixWord ++ tailWord_6928466).sum := by decide
  have hdescent : baseEnd_6928466 < baseStart_6928466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928476 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6928476 : Nat := 118140960795 + 6928476 * 2 ^ 59
def prefixEnd_6928476 : Nat := 4983230072969 + 3 ^ 40 * 6928476 * 2
def baseEnd_6928476 : Nat := 3557638391140539539486525

theorem tailTrace_6928476 : CollatzResearch.WordTrace tailWord_6928476 prefixEnd_6928476 3557638391140539539486525 := by
  unfold tailWord_6928476
  simp only [CollatzResearch.WordTrace]
  refine ⟨126351140023661108169710641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168468186698214810892947521 126351140023661108169710641)
  ·
    refine ⟨94763355017745831127282981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126351140023661108169710641 94763355017745831127282981)
    ·
      refine ⟨17768129065827343336365559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94763355017745831127282981 17768129065827343336365559)
      ·
        refine ⟨26652193598741015004548339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768129065827343336365559 26652193598741015004548339)
        ·
          refine ⟨39978290398111522506822509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26652193598741015004548339 39978290398111522506822509)
          ·
            refine ⟨14991858899291820940058441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39978290398111522506822509 14991858899291820940058441)
            ·
              refine ⟨11243894174468865705043831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14991858899291820940058441 11243894174468865705043831)
              ·
                refine ⟨16865841261703298557565747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11243894174468865705043831 16865841261703298557565747)
                ·
                  refine ⟨25298761892554947836348621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16865841261703298557565747 25298761892554947836348621)
                  ·
                    refine ⟨9487035709708105438630733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25298761892554947836348621 9487035709708105438630733)
                    ·
                      refine ⟨3557638391140539539486525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9487035709708105438630733 3557638391140539539486525)
                      ·
                        rfl

theorem cell23_6928476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6928476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928476 prefixEnd_6928476 := by exact prefixLift 6928476
  have htrace : WordTrace (prefixWord ++ tailWord_6928476) baseStart_6928476 baseEnd_6928476 := by
    simpa [prefixWord, tailWord_6928476, baseEnd_6928476] using wordTrace_append hprefix tailTrace_6928476
  have hstable : (prefixWord ++ tailWord_6928476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928476).length < 2 ^ (prefixWord ++ tailWord_6928476).sum := by decide
  have hdescent : baseEnd_6928476 < baseStart_6928476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928503 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 1, 3, 2]
def baseStart_6928503 : Nat := 118140960795 + 6928503 * 2 ^ 59
def prefixEnd_6928503 : Nat := 4983230072969 + 3 ^ 40 * 6928503 * 2
def baseEnd_6928503 : Nat := 3557652255118210933848901

theorem tailTrace_6928503 : CollatzResearch.WordTrace tailWord_6928503 prefixEnd_6928503 3557652255118210933848901 := by
  unfold tailWord_6928503
  simp only [CollatzResearch.WordTrace]
  refine ⟨252703264818224399950654163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168468843212149599967102775 252703264818224399950654163)
  ·
    refine ⟨379054897227336599925981245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252703264818224399950654163 379054897227336599925981245)
    ·
      refine ⟨142145586460251224972242967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379054897227336599925981245 142145586460251224972242967)
      ·
        refine ⟨213218379690376837458364451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142145586460251224972242967 213218379690376837458364451)
        ·
          refine ⟨319827569535565256187546677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213218379690376837458364451 319827569535565256187546677)
          ·
            refine ⟨29983834643959242767582501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 319827569535565256187546677 29983834643959242767582501)
            ·
              refine ⟨5621968995742358018921719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29983834643959242767582501 5621968995742358018921719)
              ·
                refine ⟨8432953493613537028382579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5621968995742358018921719 8432953493613537028382579)
                ·
                  refine ⟨12649430240420305542573869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8432953493613537028382579 12649430240420305542573869)
                  ·
                    refine ⟨4743536340157614578465201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12649430240420305542573869 4743536340157614578465201)
                    ·
                      refine ⟨3557652255118210933848901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743536340157614578465201 3557652255118210933848901)
                      ·
                        rfl

theorem cell23_6928503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 3, 2].length) (baseStart_6928503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928503 prefixEnd_6928503 := by exact prefixLift 6928503
  have htrace : WordTrace (prefixWord ++ tailWord_6928503) baseStart_6928503 baseEnd_6928503 := by
    simpa [prefixWord, tailWord_6928503, baseEnd_6928503] using wordTrace_append hprefix tailTrace_6928503
  have hstable : (prefixWord ++ tailWord_6928503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928503).length < 2 ^ (prefixWord ++ tailWord_6928503).sum := by decide
  have hdescent : baseEnd_6928503 < baseStart_6928503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928534 : List Nat := [5, 3, 2, 1, 2, 1, 2, 7]
def baseStart_6928534 : Nat := 118140960795 + 6928534 * 2 ^ 59
def prefixEnd_6928534 : Nat := 4983230072969 + 3 ^ 40 * 6928534 * 2
def baseEnd_6928534 : Nat := 131765487889574085650417

theorem tailTrace_6928534 : CollatzResearch.WordTrace tailWord_6928534 prefixEnd_6928534 131765487889574085650417 := by
  unfold tailWord_6928534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794024717569505765314541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168469596987408061496688437 15794024717569505765314541)
  ·
    refine ⟨5922759269088564661992953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15794024717569505765314541 5922759269088564661992953)
    ·
      refine ⟨4442069451816423496494715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5922759269088564661992953 4442069451816423496494715)
      ·
        refine ⟨6663104177724635244742073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4442069451816423496494715 6663104177724635244742073)
        ·
          refine ⟨4997328133293476433556555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6663104177724635244742073 4997328133293476433556555)
          ·
            refine ⟨7495992199940214650334833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997328133293476433556555 7495992199940214650334833)
            ·
              refine ⟨5621994149955160987751125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7495992199940214650334833 5621994149955160987751125)
              ·
                refine ⟨131765487889574085650417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5621994149955160987751125 131765487889574085650417)
                ·
                  rfl

theorem cell23_6928534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_6928534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928534 prefixEnd_6928534 := by exact prefixLift 6928534
  have htrace : WordTrace (prefixWord ++ tailWord_6928534) baseStart_6928534 baseEnd_6928534 := by
    simpa [prefixWord, tailWord_6928534, baseEnd_6928534] using wordTrace_append hprefix tailTrace_6928534
  have hstable : (prefixWord ++ tailWord_6928534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928534).length < 2 ^ (prefixWord ++ tailWord_6928534).sum := by decide
  have hdescent : baseEnd_6928534 < baseStart_6928534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928559 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 7, 2]
def baseStart_6928559 : Nat := 118140960795 + 6928559 * 2 ^ 59
def prefixEnd_6928559 : Nat := 4983230072969 + 3 ^ 40 * 6928559 * 2
def baseEnd_6928559 : Nat := 3557681010034862714748643

theorem tailTrace_6928559 : CollatzResearch.WordTrace tailWord_6928559 prefixEnd_6928559 3557681010034862714748643 := by
  unfold tailWord_6928559
  simp only [CollatzResearch.WordTrace]
  refine ⟨252705307306021521514692731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168470204870681014343128487 252705307306021521514692731)
  ·
    refine ⟨379057960959032282272039097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252705307306021521514692731 379057960959032282272039097)
    ·
      refine ⟨284293470719274211704029323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379057960959032282272039097 284293470719274211704029323)
      ·
        refine ⟨426440206078911317556043985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284293470719274211704029323 426440206078911317556043985)
        ·
          refine ⟨319830154559183488167032989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426440206078911317556043985 319830154559183488167032989)
          ·
            refine ⟨119936307959693808062637371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319830154559183488167032989 119936307959693808062637371)
            ·
              refine ⟨179904461939540712093956057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119936307959693808062637371 179904461939540712093956057)
              ·
                refine ⟨134928346454655534070467043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179904461939540712093956057 134928346454655534070467043)
                ·
                  refine ⟨202392519681983301105700565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134928346454655534070467043 202392519681983301105700565)
                  ·
                    refine ⟨4743574680046483619664857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202392519681983301105700565 4743574680046483619664857)
                    ·
                      refine ⟨3557681010034862714748643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743574680046483619664857 3557681010034862714748643)
                      ·
                        rfl

theorem cell23_6928559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7, 2].length) (baseStart_6928559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928559 prefixEnd_6928559 := by exact prefixLift 6928559
  have htrace : WordTrace (prefixWord ++ tailWord_6928559) baseStart_6928559 baseEnd_6928559 := by
    simpa [prefixWord, tailWord_6928559, baseEnd_6928559] using wordTrace_append hprefix tailTrace_6928559
  have hstable : (prefixWord ++ tailWord_6928559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928559).length < 2 ^ (prefixWord ++ tailWord_6928559).sum := by decide
  have hdescent : baseEnd_6928559 < baseStart_6928559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928569 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 2, 5]
def baseStart_6928569 : Nat := 118140960795 + 6928569 * 2 ^ 59
def prefixEnd_6928569 : Nat := 4983230072969 + 3 ^ 40 * 6928569 * 2
def baseEnd_6928569 : Nat := 1185895381613802558541199

theorem tailTrace_6928569 : CollatzResearch.WordTrace tailWord_6928569 prefixEnd_6928569 1185895381613802558541199 := by
  unfold tailWord_6928569
  simp only [CollatzResearch.WordTrace]
  refine ⟨252705672035985293222556761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168470448023990195481704507 252705672035985293222556761)
  ·
    refine ⟨189529254026988969916917571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252705672035985293222556761 189529254026988969916917571)
    ·
      refine ⟨284293881040483454875376357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189529254026988969916917571 284293881040483454875376357)
      ·
        refine ⟨53305102695090647789133067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284293881040483454875376357 53305102695090647789133067)
        ·
          refine ⟨79957654042635971683699601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53305102695090647789133067 79957654042635971683699601)
          ·
            refine ⟨59968240531976978762774701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79957654042635971683699601 59968240531976978762774701)
            ·
              refine ⟨22488090199491367036040513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59968240531976978762774701 22488090199491367036040513)
              ·
                refine ⟨16866067649618525277030385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22488090199491367036040513 16866067649618525277030385)
                ·
                  refine ⟨12649550737213893957772789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16866067649618525277030385 12649550737213893957772789)
                  ·
                    refine ⟨1185895381613802558541199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12649550737213893957772789 1185895381613802558541199)
                    ·
                      rfl

theorem cell23_6928569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_6928569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928569 prefixEnd_6928569 := by exact prefixLift 6928569
  have htrace : WordTrace (prefixWord ++ tailWord_6928569) baseStart_6928569 baseEnd_6928569 := by
    simpa [prefixWord, tailWord_6928569, baseEnd_6928569] using wordTrace_append hprefix tailTrace_6928569
  have hstable : (prefixWord ++ tailWord_6928569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928569).length < 2 ^ (prefixWord ++ tailWord_6928569).sum := by decide
  have hdescent : baseEnd_6928569 < baseStart_6928569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928592 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_6928592 : Nat := 118140960795 + 6928592 * 2 ^ 59
def prefixEnd_6928592 : Nat := 4983230072969 + 3 ^ 40 * 6928592 * 2
def baseEnd_6928592 : Nat := 3557697954896461085635991

theorem tailTrace_6928592 : CollatzResearch.WordTrace tailWord_6928592 prefixEnd_6928592 3557697954896461085635991 := by
  unfold tailWord_6928592
  simp only [CollatzResearch.WordTrace]
  refine ⟨126353255457450984075322015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168471007276601312100429353 126353255457450984075322015)
  ·
    refine ⟨189529883186176476112983023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126353255457450984075322015 189529883186176476112983023)
    ·
      refine ⟨284294824779264714169474535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189529883186176476112983023 284294824779264714169474535)
      ·
        refine ⟨426442237168897071254211803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284294824779264714169474535 426442237168897071254211803)
        ·
          refine ⟨639663355753345606881317705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426442237168897071254211803 639663355753345606881317705)
          ·
            refine ⟨479747516815009205160988279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639663355753345606881317705 479747516815009205160988279)
            ·
              refine ⟨719621275222513807741482419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479747516815009205160988279 719621275222513807741482419)
              ·
                refine ⟨1079431912833770711612223629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 719621275222513807741482419 1079431912833770711612223629)
                ·
                  refine ⟨404786967312664016854583861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1079431912833770711612223629 404786967312664016854583861)
                  ·
                    refine ⟨37948778185562251580117237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 404786967312664016854583861 37948778185562251580117237)
                    ·
                      refine ⟨3557697954896461085635991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37948778185562251580117237 3557697954896461085635991)
                      ·
                        rfl

theorem cell23_6928592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_6928592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928592 prefixEnd_6928592 := by exact prefixLift 6928592
  have htrace : WordTrace (prefixWord ++ tailWord_6928592) baseStart_6928592 baseEnd_6928592 := by
    simpa [prefixWord, tailWord_6928592, baseEnd_6928592] using wordTrace_append hprefix tailTrace_6928592
  have hstable : (prefixWord ++ tailWord_6928592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928592).length < 2 ^ (prefixWord ++ tailWord_6928592).sum := by decide
  have hdescent : baseEnd_6928592 < baseStart_6928592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928599 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 5, 4]
def baseStart_6928599 : Nat := 118140960795 + 6928599 * 2 ^ 59
def prefixEnd_6928599 : Nat := 4983230072969 + 3 ^ 40 * 6928599 * 2
def baseEnd_6928599 : Nat := 1185900516420347519416153

theorem tailTrace_6928599 : CollatzResearch.WordTrace tailWord_6928599 prefixEnd_6928599 1185900516420347519416153 := by
  unfold tailWord_6928599
  simp only [CollatzResearch.WordTrace]
  refine ⟨252706766225876608346148851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168471177483917738897432567 252706766225876608346148851)
  ·
    refine ⟨379060149338814912519223277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252706766225876608346148851 379060149338814912519223277)
    ·
      refine ⟨142147556002055592194708729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379060149338814912519223277 142147556002055592194708729)
      ·
        refine ⟨106610667001541694146031547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142147556002055592194708729 106610667001541694146031547)
        ·
          refine ⟨159916000502312541219047321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106610667001541694146031547 159916000502312541219047321)
          ·
            refine ⟨119937000376734405914285491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159916000502312541219047321 119937000376734405914285491)
            ·
              refine ⟨179905500565101608871428237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119937000376734405914285491 179905500565101608871428237)
              ·
                refine ⟨67464562711913103326785589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179905500565101608871428237 67464562711913103326785589)
                ·
                  refine ⟨6324802754241853436886149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67464562711913103326785589 6324802754241853436886149)
                  ·
                    refine ⟨1185900516420347519416153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324802754241853436886149 1185900516420347519416153)
                    ·
                      rfl

theorem cell23_6928599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 5, 4].length) (baseStart_6928599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928599 prefixEnd_6928599 := by exact prefixLift 6928599
  have htrace : WordTrace (prefixWord ++ tailWord_6928599) baseStart_6928599 baseEnd_6928599 := by
    simpa [prefixWord, tailWord_6928599, baseEnd_6928599] using wordTrace_append hprefix tailTrace_6928599
  have hstable : (prefixWord ++ tailWord_6928599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928599).length < 2 ^ (prefixWord ++ tailWord_6928599).sum := by decide
  have hdescent : baseEnd_6928599 < baseStart_6928599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928680 : List Nat := [2, 1, 5, 1, 4, 1, 1, 2, 6]
def baseStart_6928680 : Nat := 118140960795 + 6928680 * 2 ^ 59
def prefixEnd_6928680 : Nat := 4983230072969 + 3 ^ 40 * 6928680 * 2
def baseEnd_6928680 : Nat := 395304793466006304592843

theorem tailTrace_6928680 : CollatzResearch.WordTrace tailWord_6928680 prefixEnd_6928680 395304793466006304592843 := by
  unfold tailWord_6928680
  simp only [CollatzResearch.WordTrace]
  refine ⟨126354860269291579589923747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168473147025722106119898329 126354860269291579589923747)
  ·
    refine ⟨189532290403937369384885621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126354860269291579589923747 189532290403937369384885621)
    ·
      refine ⟨17768652225369128379833027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189532290403937369384885621 17768652225369128379833027)
      ·
        refine ⟨26652978338053692569749541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768652225369128379833027 26652978338053692569749541)
        ·
          refine ⟨4997433438385067356828039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26652978338053692569749541 4997433438385067356828039)
          ·
            refine ⟨7496150157577601035242059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4997433438385067356828039 7496150157577601035242059)
            ·
              refine ⟨11244225236366401552863089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496150157577601035242059 11244225236366401552863089)
              ·
                refine ⟨8433168927274801164647317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244225236366401552863089 8433168927274801164647317)
                ·
                  refine ⟨395304793466006304592843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8433168927274801164647317 395304793466006304592843)
                  ·
                    rfl

theorem cell23_6928680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 6].length) (baseStart_6928680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928680 prefixEnd_6928680 := by exact prefixLift 6928680
  have htrace : WordTrace (prefixWord ++ tailWord_6928680) baseStart_6928680 baseEnd_6928680 := by
    simpa [prefixWord, tailWord_6928680, baseEnd_6928680] using wordTrace_append hprefix tailTrace_6928680
  have hstable : (prefixWord ++ tailWord_6928680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928680).length < 2 ^ (prefixWord ++ tailWord_6928680).sum := by decide
  have hdescent : baseEnd_6928680 < baseStart_6928680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928690 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_6928690 : Nat := 118140960795 + 6928690 * 2 ^ 59
def prefixEnd_6928690 : Nat := 4983230072969 + 3 ^ 40 * 6928690 * 2
def baseEnd_6928690 : Nat := 3557748276000601702210541

theorem tailTrace_6928690 : CollatzResearch.WordTrace tailWord_6928690 prefixEnd_6928690 3557748276000601702210541 := by
  unfold tailWord_6928690
  simp only [CollatzResearch.WordTrace]
  refine ⟨63177521317136732721927881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168473390179031287258474349 63177521317136732721927881)
  ·
    refine ⟨47383140987852549541445911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63177521317136732721927881 47383140987852549541445911)
    ·
      refine ⟨71074711481778824312168867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47383140987852549541445911 71074711481778824312168867)
      ·
        refine ⟨106612067222668236468253301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71074711481778824312168867 106612067222668236468253301)
        ·
          refine ⟨9994881302125147168898747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106612067222668236468253301 9994881302125147168898747)
          ·
            refine ⟨14992321953187720753348121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9994881302125147168898747 14992321953187720753348121)
            ·
              refine ⟨11244241464890790565011091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14992321953187720753348121 11244241464890790565011091)
              ·
                refine ⟨16866362197336185847516637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11244241464890790565011091 16866362197336185847516637)
                ·
                  refine ⟨6324885824001069692818739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16866362197336185847516637 6324885824001069692818739)
                  ·
                    refine ⟨9487328736001604539228109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324885824001069692818739 9487328736001604539228109)
                    ·
                      refine ⟨3557748276000601702210541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9487328736001604539228109 3557748276000601702210541)
                      ·
                        rfl

theorem cell23_6928690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_6928690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928690 prefixEnd_6928690 := by exact prefixLift 6928690
  have htrace : WordTrace (prefixWord ++ tailWord_6928690) baseStart_6928690 baseEnd_6928690 := by
    simpa [prefixWord, tailWord_6928690, baseEnd_6928690] using wordTrace_append hprefix tailTrace_6928690
  have hstable : (prefixWord ++ tailWord_6928690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928690).length < 2 ^ (prefixWord ++ tailWord_6928690).sum := by decide
  have hdescent : baseEnd_6928690 < baseStart_6928690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928736 : List Nat := [2, 1, 1, 3, 5, 2, 9]
def baseStart_6928736 : Nat := 118140960795 + 6928736 * 2 ^ 59
def prefixEnd_6928736 : Nat := 4983230072969 + 3 ^ 40 * 6928736 * 2
def baseEnd_6928736 : Nat := 43923109828527265706609

theorem tailTrace_6928736 : CollatzResearch.WordTrace tailWord_6928736 prefixEnd_6928736 43923109828527265706609 := by
  unfold tailWord_6928736
  simp only [CollatzResearch.WordTrace]
  refine ⟨126355881513190140371943031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168474508684253520495924041 126355881513190140371943031)
  ·
    refine ⟨189533822269785210557914547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126355881513190140371943031 189533822269785210557914547)
    ·
      refine ⟨284300733404677815836871821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189533822269785210557914547 284300733404677815836871821)
      ·
        refine ⟨106612775026754180938826933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284300733404677815836871821 106612775026754180938826933)
        ·
          refine ⟨9994947658758204463015025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106612775026754180938826933 9994947658758204463015025)
          ·
            refine ⟨7496210744068653347261269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9994947658758204463015025 7496210744068653347261269)
            ·
              refine ⟨43923109828527265706609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7496210744068653347261269 43923109828527265706609)
              ·
                rfl

theorem cell23_6928736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 9].length) (baseStart_6928736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928736 prefixEnd_6928736 := by exact prefixLift 6928736
  have htrace : WordTrace (prefixWord ++ tailWord_6928736) baseStart_6928736 baseEnd_6928736 := by
    simpa [prefixWord, tailWord_6928736, baseEnd_6928736] using wordTrace_append hprefix tailTrace_6928736
  have hstable : (prefixWord ++ tailWord_6928736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928736).length < 2 ^ (prefixWord ++ tailWord_6928736).sum := by decide
  have hdescent : baseEnd_6928736 < baseStart_6928736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928757 : List Nat := [1, 3, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_6928757 : Nat := 118140960795 + 6928757 * 2 ^ 59
def prefixEnd_6928757 : Nat := 4983230072969 + 3 ^ 40 * 6928757 * 2
def baseEnd_6928757 : Nat := 1185927559734817646690911

theorem tailTrace_6928757 : CollatzResearch.WordTrace tailWord_6928757 prefixEnd_6928757 1185927559734817646690911 := by
  unfold tailWord_6928757
  simp only [CollatzResearch.WordTrace]
  refine ⟨252712528959304201330400525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168475019306202800886933683 252712528959304201330400525)
  ·
    refine ⟨94767198359739075498900197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252712528959304201330400525 94767198359739075498900197)
    ·
      refine ⟨17768849692451076656043787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94767198359739075498900197 17768849692451076656043787)
      ·
        refine ⟨26653274538676614984065681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17768849692451076656043787 26653274538676614984065681)
        ·
          refine ⟨19989955904007461238049261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26653274538676614984065681 19989955904007461238049261)
          ·
            refine ⟨7496233464002797964268473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19989955904007461238049261 7496233464002797964268473)
            ·
              refine ⟨5622175098002098473201355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496233464002797964268473 5622175098002098473201355)
              ·
                refine ⟨8433262647003147709802033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622175098002098473201355 8433262647003147709802033)
                ·
                  refine ⟨6324946985252360782351525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8433262647003147709802033 6324946985252360782351525)
                  ·
                    refine ⟨1185927559734817646690911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6324946985252360782351525 1185927559734817646690911)
                    ·
                      rfl

theorem cell23_6928757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_6928757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928757 prefixEnd_6928757 := by exact prefixLift 6928757
  have htrace : WordTrace (prefixWord ++ tailWord_6928757) baseStart_6928757 baseEnd_6928757 := by
    simpa [prefixWord, tailWord_6928757, baseEnd_6928757] using wordTrace_append hprefix tailTrace_6928757
  have hstable : (prefixWord ++ tailWord_6928757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928757).length < 2 ^ (prefixWord ++ tailWord_6928757).sum := by decide
  have hdescent : baseEnd_6928757 < baseStart_6928757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928759 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_6928759 : Nat := 118140960795 + 6928759 * 2 ^ 59
def prefixEnd_6928759 : Nat := 4983230072969 + 3 ^ 40 * 6928759 * 2
def baseEnd_6928759 : Nat := 3557783706165761932247723

theorem tailTrace_6928759 : CollatzResearch.WordTrace tailWord_6928759 prefixEnd_6928759 3557783706165761932247723 := by
  unfold tailWord_6928759
  simp only [CollatzResearch.WordTrace]
  refine ⟨252712601905296955671973331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168475067936864637114648887 252712601905296955671973331)
  ·
    refine ⟨379068902857945433507959997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252712601905296955671973331 379068902857945433507959997)
    ·
      refine ⟨142150838571729537565484999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379068902857945433507959997 142150838571729537565484999)
      ·
        refine ⟨213226257857594306348227499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142150838571729537565484999 213226257857594306348227499)
        ·
          refine ⟨319839386786391459522341249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213226257857594306348227499 319839386786391459522341249)
          ·
            refine ⟨239879540089793594641755937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319839386786391459522341249 239879540089793594641755937)
            ·
              refine ⟨179909655067345195981316953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239879540089793594641755937 179909655067345195981316953)
              ·
                refine ⟨134932241300508896985987715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179909655067345195981316953 134932241300508896985987715)
                ·
                  refine ⟨202398361950763345478981573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134932241300508896985987715 202398361950763345478981573)
                  ·
                    refine ⟨37949692865768127277309045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202398361950763345478981573 37949692865768127277309045)
                    ·
                      refine ⟨3557783706165761932247723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37949692865768127277309045 3557783706165761932247723)
                      ·
                        rfl

theorem cell23_6928759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_6928759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928759 prefixEnd_6928759 := by exact prefixLift 6928759
  have htrace : WordTrace (prefixWord ++ tailWord_6928759) baseStart_6928759 baseEnd_6928759 := by
    simpa [prefixWord, tailWord_6928759, baseEnd_6928759] using wordTrace_append hprefix tailTrace_6928759
  have hstable : (prefixWord ++ tailWord_6928759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928759).length < 2 ^ (prefixWord ++ tailWord_6928759).sum := by decide
  have hdescent : baseEnd_6928759 < baseStart_6928759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928797 : List Nat := [1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_6928797 : Nat := 118140960795 + 6928797 * 2 ^ 59
def prefixEnd_6928797 : Nat := 4983230072969 + 3 ^ 40 * 6928797 * 2
def baseEnd_6928797 : Nat := 3557803218430632783572549

theorem tailTrace_6928797 : CollatzResearch.WordTrace tailWord_6928797 prefixEnd_6928797 3557803218430632783572549 := by
  unfold tailWord_6928797
  simp only [CollatzResearch.WordTrace]
  refine ⟨252713987879159288161856645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168475991919439525441237763 252713987879159288161856645)
  ·
    refine ⟨47383872727342366530348121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252713987879159288161856645 47383872727342366530348121)
    ·
      refine ⟨35537904545506774897761091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47383872727342366530348121 35537904545506774897761091)
      ·
        refine ⟨53306856818260162346641637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35537904545506774897761091 53306856818260162346641637)
        ·
          refine ⟨9995035653423780439995307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53306856818260162346641637 9995035653423780439995307)
          ·
            refine ⟨14992553480135670659992961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9995035653423780439995307 14992553480135670659992961)
            ·
              refine ⟨11244415110101752994994721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14992553480135670659992961 11244415110101752994994721)
              ·
                refine ⟨8433311332576314746246041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244415110101752994994721 8433311332576314746246041)
                ·
                  refine ⟨6324983499432236059684531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8433311332576314746246041 6324983499432236059684531)
                  ·
                    refine ⟨9487475249148354089526797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6324983499432236059684531 9487475249148354089526797)
                    ·
                      refine ⟨3557803218430632783572549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9487475249148354089526797 3557803218430632783572549)
                      ·
                        rfl

theorem cell23_6928797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_6928797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928797 prefixEnd_6928797 := by exact prefixLift 6928797
  have htrace : WordTrace (prefixWord ++ tailWord_6928797) baseStart_6928797 baseEnd_6928797 := by
    simpa [prefixWord, tailWord_6928797, baseEnd_6928797] using wordTrace_append hprefix tailTrace_6928797
  have hstable : (prefixWord ++ tailWord_6928797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928797).length < 2 ^ (prefixWord ++ tailWord_6928797).sum := by decide
  have hdescent : baseEnd_6928797 < baseStart_6928797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928798 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6928798 : Nat := 118140960795 + 6928798 * 2 ^ 59
def prefixEnd_6928798 : Nat := 4983230072969 + 3 ^ 40 * 6928798 * 2
def baseEnd_6928798 : Nat := 3557803731911287279660045

theorem tailTrace_6928798 : CollatzResearch.WordTrace tailWord_6928798 prefixEnd_6928798 3557803731911287279660045 := by
  unfold tailWord_6928798
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589253044019458166580381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168476016234770443555095365 31589253044019458166580381)
  ·
    refine ⟨11845969891507296812467643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31589253044019458166580381 11845969891507296812467643)
    ·
      refine ⟨17768954837260945218701465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11845969891507296812467643 17768954837260945218701465)
      ·
        refine ⟨13326716127945708914026099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17768954837260945218701465 13326716127945708914026099)
        ·
          refine ⟨19990074191918563371039149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13326716127945708914026099 19990074191918563371039149)
          ·
            refine ⟨7496277821969461264139681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19990074191918563371039149 7496277821969461264139681)
            ·
              refine ⟨5622208366477095948104761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496277821969461264139681 5622208366477095948104761)
              ·
                refine ⟨4216656274857821961078571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5622208366477095948104761 4216656274857821961078571)
                ·
                  refine ⟨6324984412286732941617857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216656274857821961078571 6324984412286732941617857)
                  ·
                    refine ⟨4743738309215049706213393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6324984412286732941617857 4743738309215049706213393)
                    ·
                      refine ⟨3557803731911287279660045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4743738309215049706213393 3557803731911287279660045)
                      ·
                        rfl

theorem cell23_6928798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6928798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928798 prefixEnd_6928798 := by exact prefixLift 6928798
  have htrace : WordTrace (prefixWord ++ tailWord_6928798) baseStart_6928798 baseEnd_6928798 := by
    simpa [prefixWord, tailWord_6928798, baseEnd_6928798] using wordTrace_append hprefix tailTrace_6928798
  have hstable : (prefixWord ++ tailWord_6928798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928798).length < 2 ^ (prefixWord ++ tailWord_6928798).sum := by decide
  have hdescent : baseEnd_6928798 < baseStart_6928798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928809 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 11]
def baseStart_6928809 : Nat := 118140960795 + 6928809 * 2 ^ 59
def prefixEnd_6928809 : Nat := 4983230072969 + 3 ^ 40 * 6928809 * 2
def baseEnd_6928809 : Nat := 395312153355387415180277

theorem tailTrace_6928809 : CollatzResearch.WordTrace tailWord_6928809 prefixEnd_6928809 395312153355387415180277 := by
  unfold tailWord_6928809
  simp only [CollatzResearch.WordTrace]
  refine ⟨252714425555115814211293481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168476283703410542807528987 252714425555115814211293481)
  ·
    refine ⟨189535819166336860658470111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252714425555115814211293481 189535819166336860658470111)
    ·
      refine ⟨284303728749505290987705167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189535819166336860658470111 284303728749505290987705167)
      ·
        refine ⟨426455593124257936481557751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284303728749505290987705167 426455593124257936481557751)
        ·
          refine ⟨639683389686386904722336627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426455593124257936481557751 639683389686386904722336627)
          ·
            refine ⟨959525084529580357083504941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 639683389686386904722336627 959525084529580357083504941)
            ·
              refine ⟨359821906698592633906314353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 959525084529580357083504941 359821906698592633906314353)
              ·
                refine ⟨269866430023944475429735765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 359821906698592633906314353 269866430023944475429735765)
                ·
                  refine ⟨395312153355387415180277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 269866430023944475429735765 395312153355387415180277)
                  ·
                    rfl

theorem cell23_6928809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 11].length) (baseStart_6928809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928809 prefixEnd_6928809 := by exact prefixLift 6928809
  have htrace : WordTrace (prefixWord ++ tailWord_6928809) baseStart_6928809 baseEnd_6928809 := by
    simpa [prefixWord, tailWord_6928809, baseEnd_6928809] using wordTrace_append hprefix tailTrace_6928809
  have hstable : (prefixWord ++ tailWord_6928809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928809).length < 2 ^ (prefixWord ++ tailWord_6928809).sum := by decide
  have hdescent : baseEnd_6928809 < baseStart_6928809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928853 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_6928853 : Nat := 118140960795 + 6928853 * 2 ^ 59
def prefixEnd_6928853 : Nat := 4983230072969 + 3 ^ 40 * 6928853 * 2
def baseEnd_6928853 : Nat := 3557831973347284564472291

theorem tailTrace_6928853 : CollatzResearch.WordTrace tailWord_6928853 prefixEnd_6928853 3557831973347284564472291 := by
  unfold tailWord_6928853
  simp only [CollatzResearch.WordTrace]
  refine ⟨252716030366956409725895213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168477353577970939817263475 252716030366956409725895213)
  ·
    refine ⟨94768511387608653647210705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252716030366956409725895213 94768511387608653647210705)
    ·
      refine ⟨71076383540706490235408029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94768511387608653647210705 71076383540706490235408029)
      ·
        refine ⟨26653643827764933838278011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71076383540706490235408029 26653643827764933838278011)
        ·
          refine ⟨39980465741647400757417017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26653643827764933838278011 39980465741647400757417017)
          ·
            refine ⟨29985349306235550568062763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39980465741647400757417017 29985349306235550568062763)
            ·
              refine ⟨44978023959353325852094145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29985349306235550568062763 44978023959353325852094145)
              ·
                refine ⟨33733517969514994389070609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44978023959353325852094145 33733517969514994389070609)
                ·
                  refine ⟨25300138477136245791802957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33733517969514994389070609 25300138477136245791802957)
                  ·
                    refine ⟨9487551928926092171926109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25300138477136245791802957 9487551928926092171926109)
                    ·
                      refine ⟨3557831973347284564472291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9487551928926092171926109 3557831973347284564472291)
                      ·
                        rfl

theorem cell23_6928853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_6928853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928853 prefixEnd_6928853 := by exact prefixLift 6928853
  have htrace : WordTrace (prefixWord ++ tailWord_6928853) baseStart_6928853 baseEnd_6928853 := by
    simpa [prefixWord, tailWord_6928853, baseEnd_6928853] using wordTrace_append hprefix tailTrace_6928853
  have hstable : (prefixWord ++ tailWord_6928853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928853).length < 2 ^ (prefixWord ++ tailWord_6928853).sum := by decide
  have hdescent : baseEnd_6928853 < baseStart_6928853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928856 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 4, 5]
def baseStart_6928856 : Nat := 118140960795 + 6928856 * 2 ^ 59
def prefixEnd_6928856 : Nat := 4983230072969 + 3 ^ 40 * 6928856 * 2
def baseEnd_6928856 : Nat := 1185944504596416017578259

theorem tailTrace_6928856 : CollatzResearch.WordTrace tailWord_6928856 prefixEnd_6928856 1185944504596416017578259 := by
  unfold tailWord_6928856
  simp only [CollatzResearch.WordTrace]
  refine ⟨126358069892972770619127211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168477426523963694158836281 126358069892972770619127211)
  ·
    refine ⟨189537104839459155928690817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126358069892972770619127211 189537104839459155928690817)
    ·
      refine ⟨142152828629594366946518113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189537104839459155928690817 142152828629594366946518113)
      ·
        refine ⟨106614621472195775209888585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142152828629594366946518113 106614621472195775209888585)
        ·
          refine ⟨79960966104146831407416439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106614621472195775209888585 79960966104146831407416439)
          ·
            refine ⟨119941449156220247111124659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79960966104146831407416439 119941449156220247111124659)
            ·
              refine ⟨179912173734330370666686989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119941449156220247111124659 179912173734330370666686989)
              ·
                refine ⟨67467065150373889000007621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179912173734330370666686989 67467065150373889000007621)
                ·
                  refine ⟨12650074715695104187501429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67467065150373889000007621 12650074715695104187501429)
                  ·
                    refine ⟨1185944504596416017578259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12650074715695104187501429 1185944504596416017578259)
                    ·
                      rfl

theorem cell23_6928856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_6928856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928856 prefixEnd_6928856 := by exact prefixLift 6928856
  have htrace : WordTrace (prefixWord ++ tailWord_6928856) baseStart_6928856 baseEnd_6928856 := by
    simpa [prefixWord, tailWord_6928856, baseEnd_6928856] using wordTrace_append hprefix tailTrace_6928856
  have hstable : (prefixWord ++ tailWord_6928856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928856).length < 2 ^ (prefixWord ++ tailWord_6928856).sum := by decide
  have hdescent : baseEnd_6928856 < baseStart_6928856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928876 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_6928876 : Nat := 118140960795 + 6928876 * 2 ^ 59
def prefixEnd_6928876 : Nat := 4983230072969 + 3 ^ 40 * 6928876 * 2
def baseEnd_6928876 : Nat := 3557843783402337974484685

theorem tailTrace_6928876 : CollatzResearch.WordTrace tailWord_6928876 prefixEnd_6928876 3557843783402337974484685 := by
  unfold tailWord_6928876
  simp only [CollatzResearch.WordTrace]
  refine ⟨126358434622936542326991241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168477912830582056435988321 126358434622936542326991241)
  ·
    refine ⟨94768825967202406745243431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126358434622936542326991241 94768825967202406745243431)
    ·
      refine ⟨142153238950803610117865147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94768825967202406745243431 142153238950803610117865147)
      ·
        refine ⟨213229858426205415176797721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142153238950803610117865147 213229858426205415176797721)
        ·
          refine ⟨159922393819654061382598291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213229858426205415176797721 159922393819654061382598291)
          ·
            refine ⟨239883590729481092073897437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159922393819654061382598291 239883590729481092073897437)
            ·
              refine ⟨89956346523555409527711539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 239883590729481092073897437 89956346523555409527711539)
              ·
                refine ⟨134934519785333114291567309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89956346523555409527711539 134934519785333114291567309)
                ·
                  refine ⟨50600444919499917859337741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134934519785333114291567309 50600444919499917859337741)
                  ·
                    refine ⟨18975166844812469197251653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50600444919499917859337741 18975166844812469197251653)
                    ·
                      refine ⟨3557843783402337974484685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18975166844812469197251653 3557843783402337974484685)
                      ·
                        rfl

theorem cell23_6928876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_6928876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928876 prefixEnd_6928876 := by exact prefixLift 6928876
  have htrace : WordTrace (prefixWord ++ tailWord_6928876) baseStart_6928876 baseEnd_6928876 := by
    simpa [prefixWord, tailWord_6928876, baseEnd_6928876] using wordTrace_append hprefix tailTrace_6928876
  have hstable : (prefixWord ++ tailWord_6928876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928876).length < 2 ^ (prefixWord ++ tailWord_6928876).sum := by decide
  have hdescent : baseEnd_6928876 < baseStart_6928876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928893 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_6928893 : Nat := 118140960795 + 6928893 * 2 ^ 59
def prefixEnd_6928893 : Nat := 4983230072969 + 3 ^ 40 * 6928893 * 2
def baseEnd_6928893 : Nat := 3557852512573464407972107

theorem tailTrace_6928893 : CollatzResearch.WordTrace tailWord_6928893 prefixEnd_6928893 3557852512573464407972107 := by
  unfold tailWord_6928893
  simp only [CollatzResearch.WordTrace]
  refine ⟨252717489286811496557351333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168478326191207664371567555 252717489286811496557351333)
  ·
    refine ⟨47384529241277155604503375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252717489286811496557351333 47384529241277155604503375)
    ·
      refine ⟨71076793861915733406755063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47384529241277155604503375 71076793861915733406755063)
      ·
        refine ⟨106615190792873600110132595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71076793861915733406755063 106615190792873600110132595)
        ·
          refine ⟨159922786189310400165198893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106615190792873600110132595 159922786189310400165198893)
          ·
            refine ⟨59971044820991400061949585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159922786189310400165198893 59971044820991400061949585)
            ·
              refine ⟨44978283615743550046462189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59971044820991400061949585 44978283615743550046462189)
              ·
                refine ⟨16866856355903831267423321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44978283615743550046462189 16866856355903831267423321)
                ·
                  refine ⟨12650142266927873450567491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16866856355903831267423321 12650142266927873450567491)
                  ·
                    refine ⟨18975213400391810175851237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12650142266927873450567491 18975213400391810175851237)
                    ·
                      refine ⟨3557852512573464407972107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18975213400391810175851237 3557852512573464407972107)
                      ·
                        rfl

theorem cell23_6928893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_6928893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928893 prefixEnd_6928893 := by exact prefixLift 6928893
  have htrace : WordTrace (prefixWord ++ tailWord_6928893) baseStart_6928893 baseEnd_6928893 := by
    simpa [prefixWord, tailWord_6928893, baseEnd_6928893] using wordTrace_append hprefix tailTrace_6928893
  have hstable : (prefixWord ++ tailWord_6928893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928893).length < 2 ^ (prefixWord ++ tailWord_6928893).sum := by decide
  have hdescent : baseEnd_6928893 < baseStart_6928893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928910 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_6928910 : Nat := 118140960795 + 6928910 * 2 ^ 59
def prefixEnd_6928910 : Nat := 4983230072969 + 3 ^ 40 * 6928910 * 2
def baseEnd_6928910 : Nat := 3557861241744590841459529

theorem tailTrace_6928910 : CollatzResearch.WordTrace tailWord_6928910 prefixEnd_6928910 3557861241744590841459529 := by
  unfold tailWord_6928910
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589763665968738557590023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168478739551833272307146789 31589763665968738557590023)
  ·
    refine ⟨47384645498953107836385035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31589763665968738557590023 47384645498953107836385035)
    ·
      refine ⟨71076968248429661754577553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47384645498953107836385035 71076968248429661754577553)
      ·
        refine ⟨53307726186322246315933165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71076968248429661754577553 53307726186322246315933165)
        ·
          refine ⟨19990397319870842368474937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53307726186322246315933165 19990397319870842368474937)
          ·
            refine ⟨14992797989903131776356203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19990397319870842368474937 14992797989903131776356203)
            ·
              refine ⟨22489196984854697664534305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14992797989903131776356203 22489196984854697664534305)
              ·
                refine ⟨16866897738641023248400729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22489196984854697664534305 16866897738641023248400729)
                ·
                  refine ⟨12650173303980767436300547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16866897738641023248400729 12650173303980767436300547)
                  ·
                    refine ⟨18975259955971151154450821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12650173303980767436300547 18975259955971151154450821)
                    ·
                      refine ⟨3557861241744590841459529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18975259955971151154450821 3557861241744590841459529)
                      ·
                        rfl

theorem cell23_6928910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_6928910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928910 prefixEnd_6928910 := by exact prefixLift 6928910
  have htrace : WordTrace (prefixWord ++ tailWord_6928910) baseStart_6928910 baseEnd_6928910 := by
    simpa [prefixWord, tailWord_6928910, baseEnd_6928910] using wordTrace_append hprefix tailTrace_6928910
  have hstable : (prefixWord ++ tailWord_6928910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928910).length < 2 ^ (prefixWord ++ tailWord_6928910).sum := by decide
  have hdescent : baseEnd_6928910 < baseStart_6928910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928920 : List Nat := [2, 1, 2, 3, 3, 1, 3, 1, 3, 4]
def baseStart_6928920 : Nat := 118140960795 + 6928920 * 2 ^ 59
def prefixEnd_6928920 : Nat := 4983230072969 + 3 ^ 40 * 6928920 * 2
def baseEnd_6928920 : Nat := 1185955458850378600778161

theorem tailTrace_6928920 : CollatzResearch.WordTrace tailWord_6928920 prefixEnd_6928920 1185955458850378600778161 := by
  unfold tailWord_6928920
  simp only [CollatzResearch.WordTrace]
  refine ⟨126359237028856840084292107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168478982705142453445722809 126359237028856840084292107)
  ·
    refine ⟨189538855543285260126438161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126359237028856840084292107 189538855543285260126438161)
    ·
      refine ⟨142154141657463945094828621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189538855543285260126438161 142154141657463945094828621)
      ·
        refine ⟨53307803121548979410560733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142154141657463945094828621 53307803121548979410560733)
        ·
          refine ⟨19990426170580867278960275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53307803121548979410560733 19990426170580867278960275)
          ·
            refine ⟨29985639255871300918440413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19990426170580867278960275 29985639255871300918440413)
            ·
              refine ⟨11244614720951737844415155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29985639255871300918440413 11244614720951737844415155)
              ·
                refine ⟨16866922081427606766622733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11244614720951737844415155 16866922081427606766622733)
                ·
                  refine ⟨6325095780535352537483525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16866922081427606766622733 6325095780535352537483525)
                  ·
                    refine ⟨1185955458850378600778161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325095780535352537483525 1185955458850378600778161)
                    ·
                      rfl

theorem cell23_6928920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_6928920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928920 prefixEnd_6928920 := by exact prefixLift 6928920
  have htrace : WordTrace (prefixWord ++ tailWord_6928920) baseStart_6928920 baseEnd_6928920 := by
    simpa [prefixWord, tailWord_6928920, baseEnd_6928920] using wordTrace_append hprefix tailTrace_6928920
  have hstable : (prefixWord ++ tailWord_6928920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928920).length < 2 ^ (prefixWord ++ tailWord_6928920).sum := by decide
  have hdescent : baseEnd_6928920 < baseStart_6928920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928963 : List Nat := [1, 1, 1, 3, 1, 2, 1, 7, 1, 5]
def baseStart_6928963 : Nat := 118140960795 + 6928963 * 2 ^ 59
def prefixEnd_6928963 : Nat := 4983230072969 + 3 ^ 40 * 6928963 * 2
def baseEnd_6928963 : Nat := 1185962818739759711365595

theorem tailTrace_6928963 : CollatzResearch.WordTrace tailWord_6928963 prefixEnd_6928963 1185962818739759711365595 := by
  unfold tailWord_6928963
  simp only [CollatzResearch.WordTrace]
  refine ⟨252720042396557898512399543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168480028264371932341599695 252720042396557898512399543)
  ·
    refine ⟨379080063594836847768599315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252720042396557898512399543 379080063594836847768599315)
    ·
      refine ⟨568620095392255271652898973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379080063594836847768599315 568620095392255271652898973)
      ·
        refine ⟨213232535772095726869837115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568620095392255271652898973 213232535772095726869837115)
        ·
          refine ⟨319848803658143590304755673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213232535772095726869837115 319848803658143590304755673)
          ·
            refine ⟨239886602743607692728566755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319848803658143590304755673 239886602743607692728566755)
            ·
              refine ⟨359829904115411539092850133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239886602743607692728566755 359829904115411539092850133)
              ·
                refine ⟨8433513377704957947488675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 359829904115411539092850133 8433513377704957947488675)
                ·
                  refine ⟨12650270066557436921233013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433513377704957947488675 12650270066557436921233013)
                  ·
                    refine ⟨1185962818739759711365595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12650270066557436921233013 1185962818739759711365595)
                    ·
                      rfl

theorem cell23_6928963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 7, 1, 5].length) (baseStart_6928963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928963 prefixEnd_6928963 := by exact prefixLift 6928963
  have htrace : WordTrace (prefixWord ++ tailWord_6928963) baseStart_6928963 baseEnd_6928963 := by
    simpa [prefixWord, tailWord_6928963, baseEnd_6928963] using wordTrace_append hprefix tailTrace_6928963
  have hstable : (prefixWord ++ tailWord_6928963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928963).length < 2 ^ (prefixWord ++ tailWord_6928963).sum := by decide
  have hdescent : baseEnd_6928963 < baseStart_6928963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928983 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_6928983 : Nat := 118140960795 + 6928983 * 2 ^ 59
def prefixEnd_6928983 : Nat := 4983230072969 + 3 ^ 40 * 6928983 * 2
def baseEnd_6928983 : Nat := 3557898725832369055846693

theorem tailTrace_6928983 : CollatzResearch.WordTrace tailWord_6928983 prefixEnd_6928983 3557898725832369055846693 := by
  unfold tailWord_6928983
  simp only [CollatzResearch.WordTrace]
  refine ⟨252720771856485441928127603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168480514570990294618751735 252720771856485441928127603)
  ·
    refine ⟨379081157784728162892191405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252720771856485441928127603 379081157784728162892191405)
    ·
      refine ⟨142155434169273061084571777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379081157784728162892191405 142155434169273061084571777)
      ·
        refine ⟨106616575626954795813428833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142155434169273061084571777 106616575626954795813428833)
        ·
          refine ⟨79962431720216096860071625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106616575626954795813428833 79962431720216096860071625)
          ·
            refine ⟨59971823790162072645053719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79962431720216096860071625 59971823790162072645053719)
            ·
              refine ⟨89957735685243108967580579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59971823790162072645053719 89957735685243108967580579)
              ·
                refine ⟨134936603527864663451370869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89957735685243108967580579 134936603527864663451370869)
                ·
                  refine ⟨12650306580737312198566019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134936603527864663451370869 12650306580737312198566019)
                  ·
                    refine ⟨18975459871105968297849029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12650306580737312198566019 18975459871105968297849029)
                    ·
                      refine ⟨3557898725832369055846693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18975459871105968297849029 3557898725832369055846693)
                      ·
                        rfl

theorem cell23_6928983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_6928983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928983 prefixEnd_6928983 := by exact prefixLift 6928983
  have htrace : WordTrace (prefixWord ++ tailWord_6928983) baseStart_6928983 baseEnd_6928983 := by
    simpa [prefixWord, tailWord_6928983, baseEnd_6928983] using wordTrace_append hprefix tailTrace_6928983
  have hstable : (prefixWord ++ tailWord_6928983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928983).length < 2 ^ (prefixWord ++ tailWord_6928983).sum := by decide
  have hdescent : baseEnd_6928983 < baseStart_6928983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6928993 : List Nat := [1, 2, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_6928993 : Nat := 118140960795 + 6928993 * 2 ^ 59
def prefixEnd_6928993 : Nat := 4983230072969 + 3 ^ 40 * 6928993 * 2
def baseEnd_6928993 : Nat := 1185967953546304672240549

theorem tailTrace_6928993 : CollatzResearch.WordTrace tailWord_6928993 prefixEnd_6928993 1185967953546304672240549 := by
  unfold tailWord_6928993
  simp only [CollatzResearch.WordTrace]
  refine ⟨252721136586449213635991633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168480757724299475757327755 252721136586449213635991633)
  ·
    refine ⟨189540852439836910226993725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252721136586449213635991633 189540852439836910226993725)
    ·
      refine ⟨71077819664938841335122647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189540852439836910226993725 71077819664938841335122647)
      ·
        refine ⟨106616729497408262002683971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71077819664938841335122647 106616729497408262002683971)
        ·
          refine ⟨159925094246112393004025957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106616729497408262002683971 159925094246112393004025957)
          ·
            refine ⟨29985955171146073688254867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159925094246112393004025957 29985955171146073688254867)
            ·
              refine ⟨44978932756719110532382301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29985955171146073688254867 44978932756719110532382301)
              ·
                refine ⟨16867099783769666449643363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44978932756719110532382301 16867099783769666449643363)
                ·
                  refine ⟨25300649675654499674465045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16867099783769666449643363 25300649675654499674465045)
                  ·
                    refine ⟨1185967953546304672240549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25300649675654499674465045 1185967953546304672240549)
                    ·
                      rfl

theorem cell23_6928993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_6928993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6928993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6928993 prefixEnd_6928993 := by exact prefixLift 6928993
  have htrace : WordTrace (prefixWord ++ tailWord_6928993) baseStart_6928993 baseEnd_6928993 := by
    simpa [prefixWord, tailWord_6928993, baseEnd_6928993] using wordTrace_append hprefix tailTrace_6928993
  have hstable : (prefixWord ++ tailWord_6928993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6928993).length < 2 ^ (prefixWord ++ tailWord_6928993).sum := by decide
  have hdescent : baseEnd_6928993 < baseStart_6928993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6928993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929017 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 1, 1, 4]
def baseStart_6929017 : Nat := 118140960795 + 6929017 * 2 ^ 59
def prefixEnd_6929017 : Nat := 4983230072969 + 3 ^ 40 * 6929017 * 2
def baseEnd_6929017 : Nat := 3557916184174621922821537

theorem tailTrace_6929017 : CollatzResearch.WordTrace tailWord_6929017 prefixEnd_6929017 3557916184174621922821537 := by
  unfold tailWord_6929017
  simp only [CollatzResearch.WordTrace]
  refine ⟨252722011938362265734865305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168481341292241510489910203 252722011938362265734865305)
  ·
    refine ⟨189541508953771699301148979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252722011938362265734865305 189541508953771699301148979)
    ·
      refine ⟨284312263430657548951723469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189541508953771699301148979 284312263430657548951723469)
      ·
        refine ⟨106617098786496580856896301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284312263430657548951723469 106617098786496580856896301)
        ·
          refine ⟨39981412044936217821336113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106617098786496580856896301 39981412044936217821336113)
          ·
            refine ⟨29986059033702163366002085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39981412044936217821336113 29986059033702163366002085)
            ·
              refine ⟨5622386068819155631125391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29986059033702163366002085 5622386068819155631125391)
              ·
                refine ⟨8433579103228733446688087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622386068819155631125391 8433579103228733446688087)
                ·
                  refine ⟨12650368654843100170032131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433579103228733446688087 12650368654843100170032131)
                  ·
                    refine ⟨18975552982264650255048197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12650368654843100170032131 18975552982264650255048197)
                    ·
                      refine ⟨3557916184174621922821537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18975552982264650255048197 3557916184174621922821537)
                      ·
                        rfl

theorem cell23_6929017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_6929017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929017 prefixEnd_6929017 := by exact prefixLift 6929017
  have htrace : WordTrace (prefixWord ++ tailWord_6929017) baseStart_6929017 baseEnd_6929017 := by
    simpa [prefixWord, tailWord_6929017, baseEnd_6929017] using wordTrace_append hprefix tailTrace_6929017
  have hstable : (prefixWord ++ tailWord_6929017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929017).length < 2 ^ (prefixWord ++ tailWord_6929017).sum := by decide
  have hdescent : baseEnd_6929017 < baseStart_6929017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929053 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_6929053 : Nat := 118140960795 + 6929053 * 2 ^ 59
def prefixEnd_6929053 : Nat := 4983230072969 + 3 ^ 40 * 6929053 * 2
def baseEnd_6929053 : Nat := 1185978223159394593990457

theorem tailTrace_6929053 : CollatzResearch.WordTrace tailWord_6929053 prefixEnd_6929053 1185978223159394593990457 := by
  unfold tailWord_6929053
  simp only [CollatzResearch.WordTrace]
  refine ⟨252723324966231843883175813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168482216644154562588783875 252723324966231843883175813)
  ·
    refine ⟨47385623431168470728095465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252723324966231843883175813 47385623431168470728095465)
    ·
      refine ⟨35539217573376353046071599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47385623431168470728095465 35539217573376353046071599)
      ·
        refine ⟨53308826360064529569107399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35539217573376353046071599 53308826360064529569107399)
        ·
          refine ⟨79963239540096794353661099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53308826360064529569107399 79963239540096794353661099)
          ·
            refine ⟨119944859310145191530491649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79963239540096794353661099 119944859310145191530491649)
            ·
              refine ⟨89958644482608893647868737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119944859310145191530491649 89958644482608893647868737)
              ·
                refine ⟨67468983361956670235901553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89958644482608893647868737 67468983361956670235901553)
                ·
                  refine ⟨50601737521467502676926165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67468983361956670235901553 50601737521467502676926165)
                  ·
                    refine ⟨1185978223159394593990457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50601737521467502676926165 1185978223159394593990457)
                    ·
                      rfl

theorem cell23_6929053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_6929053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929053 prefixEnd_6929053 := by exact prefixLift 6929053
  have htrace : WordTrace (prefixWord ++ tailWord_6929053) baseStart_6929053 baseEnd_6929053 := by
    simpa [prefixWord, tailWord_6929053, baseEnd_6929053] using wordTrace_append hprefix tailTrace_6929053
  have hstable : (prefixWord ++ tailWord_6929053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929053).length < 2 ^ (prefixWord ++ tailWord_6929053).sum := by decide
  have hdescent : baseEnd_6929053 < baseStart_6929053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929054 : List Nat := [4, 3, 1, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6929054 : Nat := 118140960795 + 6929054 * 2 ^ 59
def prefixEnd_6929054 : Nat := 4983230072969 + 3 ^ 40 * 6929054 * 2
def baseEnd_6929054 : Nat := 3557935182958838278058867

theorem tailTrace_6929054 : CollatzResearch.WordTrace tailWord_6929054 prefixEnd_6929054 3557935182958838278058867 := by
  unfold tailWord_6929054
  simp only [CollatzResearch.WordTrace]
  refine ⟨31590420179903527631745277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168482240959485480702641477 31590420179903527631745277)
  ·
    refine ⟨11846407567463822861904479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31590420179903527631745277 11846407567463822861904479)
    ·
      refine ⟨17769611351195734292856719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11846407567463822861904479 17769611351195734292856719)
      ·
        refine ⟨26654417026793601439285079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17769611351195734292856719 26654417026793601439285079)
        ·
          refine ⟨39981625540190402158927619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26654417026793601439285079 39981625540190402158927619)
          ·
            refine ⟨59972438310285603238391429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39981625540190402158927619 59972438310285603238391429)
            ·
              refine ⟨11244832183178550607198393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59972438310285603238391429 11244832183178550607198393)
              ·
                refine ⟨8433624137383912955398795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11244832183178550607198393 8433624137383912955398795)
                ·
                  refine ⟨12650436206075869433098193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433624137383912955398795 12650436206075869433098193)
                  ·
                    refine ⟨9487827154556902074823645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12650436206075869433098193 9487827154556902074823645)
                    ·
                      refine ⟨3557935182958838278058867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9487827154556902074823645 3557935182958838278058867)
                      ·
                        rfl

theorem cell23_6929054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6929054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929054 prefixEnd_6929054 := by exact prefixLift 6929054
  have htrace : WordTrace (prefixWord ++ tailWord_6929054) baseStart_6929054 baseEnd_6929054 := by
    simpa [prefixWord, tailWord_6929054, baseEnd_6929054] using wordTrace_append hprefix tailTrace_6929054
  have hstable : (prefixWord ++ tailWord_6929054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929054).length < 2 ^ (prefixWord ++ tailWord_6929054).sum := by decide
  have hdescent : baseEnd_6929054 < baseStart_6929054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929057 : List Nat := [1, 2, 3, 3, 3, 2, 2, 7]
def baseStart_6929057 : Nat := 118140960795 + 6929057 * 2 ^ 59
def prefixEnd_6929057 : Nat := 4983230072969 + 3 ^ 40 * 6929057 * 2
def baseEnd_6929057 : Nat := 131775434200029695048939

theorem tailTrace_6929057 : CollatzResearch.WordTrace tailWord_6929057 prefixEnd_6929057 131775434200029695048939 := by
  unfold tailWord_6929057
  simp only [CollatzResearch.WordTrace]
  refine ⟨252723470858217352566321425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168482313905478235044214283 252723470858217352566321425)
  ·
    refine ⟨189542603143663014424741069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252723470858217352566321425 189542603143663014424741069)
    ·
      refine ⟨71078476178873630409277901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189542603143663014424741069 71078476178873630409277901)
      ·
        refine ⟨26654428567077611403479213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71078476178873630409277901 26654428567077611403479213)
        ·
          refine ⟨9995410712654104276304705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26654428567077611403479213 9995410712654104276304705)
          ·
            refine ⟨7496558034490578207228529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9995410712654104276304705 7496558034490578207228529)
            ·
              refine ⟨5622418525867933655421397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496558034490578207228529 5622418525867933655421397)
              ·
                refine ⟨131775434200029695048939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5622418525867933655421397 131775434200029695048939)
                ·
                  rfl

theorem cell23_6929057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 2, 7].length) (baseStart_6929057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929057 prefixEnd_6929057 := by exact prefixLift 6929057
  have htrace : WordTrace (prefixWord ++ tailWord_6929057) baseStart_6929057 baseEnd_6929057 := by
    simpa [prefixWord, tailWord_6929057, baseEnd_6929057] using wordTrace_append hprefix tailTrace_6929057
  have hstable : (prefixWord ++ tailWord_6929057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929057).length < 2 ^ (prefixWord ++ tailWord_6929057).sum := by decide
  have hdescent : baseEnd_6929057 < baseStart_6929057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929093 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_6929093 : Nat := 118140960795 + 6929093 * 2 ^ 59
def prefixEnd_6929093 : Nat := 4983230072969 + 3 ^ 40 * 6929093 * 2
def baseEnd_6929093 : Nat := 3557955208704363625471187

theorem tailTrace_6929093 : CollatzResearch.WordTrace tailWord_6929093 prefixEnd_6929093 3557955208704363625471187 := by
  unfold tailWord_6929093
  simp only [CollatzResearch.WordTrace]
  refine ⟨252724783886086930714631933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168483189257391287143087955 252724783886086930714631933)
  ·
    refine ⟨94771793957282599017986975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252724783886086930714631933 94771793957282599017986975)
    ·
      refine ⟨142157690935923898526980463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94771793957282599017986975 142157690935923898526980463)
      ·
        refine ⟨213236536403885847790470695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142157690935923898526980463 213236536403885847790470695)
        ·
          refine ⟨319854804605828771685706043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213236536403885847790470695 319854804605828771685706043)
          ·
            refine ⟨479782206908743157528559065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319854804605828771685706043 479782206908743157528559065)
            ·
              refine ⟨359836655181557368146419299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479782206908743157528559065 359836655181557368146419299)
              ·
                refine ⟨539754982772336052219628949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359836655181557368146419299 539754982772336052219628949)
                ·
                  refine ⟨25301014817453252447795107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 539754982772336052219628949 25301014817453252447795107)
                  ·
                    refine ⟨37951522226179878671692661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25301014817453252447795107 37951522226179878671692661)
                    ·
                      refine ⟨3557955208704363625471187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37951522226179878671692661 3557955208704363625471187)
                      ·
                        rfl

theorem cell23_6929093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_6929093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929093 prefixEnd_6929093 := by exact prefixLift 6929093
  have htrace : WordTrace (prefixWord ++ tailWord_6929093) baseStart_6929093 baseEnd_6929093 := by
    simpa [prefixWord, tailWord_6929093, baseEnd_6929093] using wordTrace_append hprefix tailTrace_6929093
  have hstable : (prefixWord ++ tailWord_6929093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929093).length < 2 ^ (prefixWord ++ tailWord_6929093).sum := by decide
  have hdescent : baseEnd_6929093 < baseStart_6929093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929113 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 9]
def baseStart_6929113 : Nat := 118140960795 + 6929113 * 2 ^ 59
def prefixEnd_6929113 : Nat := 4983230072969 + 3 ^ 40 * 6929113 * 2
def baseEnd_6929113 : Nat := 395329497590828171913455

theorem tailTrace_6929113 : CollatzResearch.WordTrace tailWord_6929113 prefixEnd_6929113 395329497590828171913455 := by
  unfold tailWord_6929113
  simp only [CollatzResearch.WordTrace]
  refine ⟨252725513346014474130359993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168483675564009649420239995 252725513346014474130359993)
  ·
    refine ⟨189544135009510855597769995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252725513346014474130359993 189544135009510855597769995)
    ·
      refine ⟨284316202514266283396654993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189544135009510855597769995 284316202514266283396654993)
      ·
        refine ⟨213237151885699712547491245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284316202514266283396654993 213237151885699712547491245)
        ·
          refine ⟨79963931957137392205309217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213237151885699712547491245 79963931957137392205309217)
          ·
            refine ⟨59972948967853044153981913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79963931957137392205309217 59972948967853044153981913)
            ·
              refine ⟨44979711725889783115486435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59972948967853044153981913 44979711725889783115486435)
              ·
                refine ⟨67469567588834674673229653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44979711725889783115486435 67469567588834674673229653)
                ·
                  refine ⟨395329497590828171913455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67469567588834674673229653 395329497590828171913455)
                  ·
                    rfl

theorem cell23_6929113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_6929113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929113 prefixEnd_6929113 := by exact prefixLift 6929113
  have htrace : WordTrace (prefixWord ++ tailWord_6929113) baseStart_6929113 baseEnd_6929113 := by
    simpa [prefixWord, tailWord_6929113, baseEnd_6929113] using wordTrace_append hprefix tailTrace_6929113
  have hstable : (prefixWord ++ tailWord_6929113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929113).length < 2 ^ (prefixWord ++ tailWord_6929113).sum := by decide
  have hdescent : baseEnd_6929113 < baseStart_6929113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929143 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 3, 7]
def baseStart_6929143 : Nat := 118140960795 + 6929143 * 2 ^ 59
def prefixEnd_6929143 : Nat := 4983230072969 + 3 ^ 40 * 6929143 * 2
def baseEnd_6929143 : Nat := 1185993627579029476615319

theorem tailTrace_6929143 : CollatzResearch.WordTrace tailWord_6929143 prefixEnd_6929143 1185993627579029476615319 := by
  unfold tailWord_6929143
  simp only [CollatzResearch.WordTrace]
  refine ⟨252726607535905789253952083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168484405023937192835968055 252726607535905789253952083)
  ·
    refine ⟨379089911303858683880928125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252726607535905789253952083 379089911303858683880928125)
    ·
      refine ⟨142158716738947006455348047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379089911303858683880928125 142158716738947006455348047)
      ·
        refine ⟨213238075108420509683022071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142158716738947006455348047 213238075108420509683022071)
        ·
          refine ⟨319857112662630764524533107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213238075108420509683022071 319857112662630764524533107)
          ·
            refine ⟨479785668993946146786799661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319857112662630764524533107 479785668993946146786799661)
            ·
              refine ⟨179919625872729805045049873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479785668993946146786799661 179919625872729805045049873)
              ·
                refine ⟨134939719404547353783787405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179919625872729805045049873 134939719404547353783787405)
                ·
                  refine ⟨50602394776705257668920277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134939719404547353783787405 50602394776705257668920277)
                  ·
                    refine ⟨1185993627579029476615319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50602394776705257668920277 1185993627579029476615319)
                    ·
                      rfl

theorem cell23_6929143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_6929143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929143 prefixEnd_6929143 := by exact prefixLift 6929143
  have htrace : WordTrace (prefixWord ++ tailWord_6929143) baseStart_6929143 baseEnd_6929143 := by
    simpa [prefixWord, tailWord_6929143, baseEnd_6929143] using wordTrace_append hprefix tailTrace_6929143
  have hstable : (prefixWord ++ tailWord_6929143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929143).length < 2 ^ (prefixWord ++ tailWord_6929143).sum := by decide
  have hdescent : baseEnd_6929143 < baseStart_6929143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929181 : List Nat := [1, 4, 2, 4, 1, 1, 2, 3, 5]
def baseStart_6929181 : Nat := 118140960795 + 6929181 * 2 ^ 59
def prefixEnd_6929181 : Nat := 4983230072969 + 3 ^ 40 * 6929181 * 2
def baseEnd_6929181 : Nat := 395333377222439920130087

theorem tailTrace_6929181 : CollatzResearch.WordTrace tailWord_6929181 prefixEnd_6929181 395333377222439920130087 := by
  unfold tailWord_6929181
  simp only [CollatzResearch.WordTrace]
  refine ⟨252727993509768121743835397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168485329006512081162556931 252727993509768121743835397)
  ·
    refine ⟨47386498783081522826969137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252727993509768121743835397 47386498783081522826969137)
    ·
      refine ⟨35539874087311142120226853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47386498783081522826969137 35539874087311142120226853)
      ·
        refine ⟨6663726391370839147542535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35539874087311142120226853 6663726391370839147542535)
        ·
          refine ⟨9995589587056258721313803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6663726391370839147542535 9995589587056258721313803)
          ·
            refine ⟨14993384380584388081970705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9995589587056258721313803 14993384380584388081970705)
            ·
              refine ⟨11245038285438291061478029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14993384380584388081970705 11245038285438291061478029)
              ·
                refine ⟨4216889357039359148054261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11245038285438291061478029 4216889357039359148054261)
                ·
                  refine ⟨395333377222439920130087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4216889357039359148054261 395333377222439920130087)
                  ·
                    rfl

theorem cell23_6929181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_6929181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929181 prefixEnd_6929181 := by exact prefixLift 6929181
  have htrace : WordTrace (prefixWord ++ tailWord_6929181) baseStart_6929181 baseEnd_6929181 := by
    simpa [prefixWord, tailWord_6929181, baseEnd_6929181] using wordTrace_append hprefix tailTrace_6929181
  have hstable : (prefixWord ++ tailWord_6929181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929181).length < 2 ^ (prefixWord ++ tailWord_6929181).sum := by decide
  have hdescent : baseEnd_6929181 < baseStart_6929181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929207 : List Nat := [1, 1, 3, 1, 2, 1, 6, 1, 3, 4]
def baseStart_6929207 : Nat := 118140960795 + 6929207 * 2 ^ 59
def prefixEnd_6929207 : Nat := 4983230072969 + 3 ^ 40 * 6929207 * 2
def baseEnd_6929207 : Nat := 1186004581832992059815221

theorem tailTrace_6929207 : CollatzResearch.WordTrace tailWord_6929207 prefixEnd_6929207 1186004581832992059815221 := by
  unfold tailWord_6929207
  simp only [CollatzResearch.WordTrace]
  refine ⟨252728941807673928184281875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168485961205115952122854583 252728941807673928184281875)
  ·
    refine ⟨379093412711510892276422813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252728941807673928184281875 379093412711510892276422813)
    ·
      refine ⟨142160029766816584603658555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379093412711510892276422813 142160029766816584603658555)
      ·
        refine ⟨213240044650224876905487833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142160029766816584603658555 213240044650224876905487833)
        ·
          refine ⟨159930033487668657679115875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213240044650224876905487833 159930033487668657679115875)
          ·
            refine ⟨239895050231502986518673813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159930033487668657679115875 239895050231502986518673813)
            ·
              refine ⟨11245080479601702493062835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239895050231502986518673813 11245080479601702493062835)
              ·
                refine ⟨16867620719402553739594253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245080479601702493062835 16867620719402553739594253)
                ·
                  refine ⟨6325357769775957652347845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16867620719402553739594253 6325357769775957652347845)
                  ·
                    refine ⟨1186004581832992059815221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325357769775957652347845 1186004581832992059815221)
                    ·
                      rfl

theorem cell23_6929207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 3, 4].length) (baseStart_6929207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929207 prefixEnd_6929207 := by exact prefixLift 6929207
  have htrace : WordTrace (prefixWord ++ tailWord_6929207) baseStart_6929207 baseEnd_6929207 := by
    simpa [prefixWord, tailWord_6929207, baseEnd_6929207] using wordTrace_append hprefix tailTrace_6929207
  have hstable : (prefixWord ++ tailWord_6929207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929207).length < 2 ^ (prefixWord ++ tailWord_6929207).sum := by decide
  have hdescent : baseEnd_6929207 < baseStart_6929207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929241 : List Nat := [1, 2, 1, 2, 2, 6, 1, 3, 1, 4]
def baseStart_6929241 : Nat := 118140960795 + 6929241 * 2 ^ 59
def prefixEnd_6929241 : Nat := 4983230072969 + 3 ^ 40 * 6929241 * 2
def baseEnd_6929241 : Nat := 1186010401280409682140169

theorem tailTrace_6929241 : CollatzResearch.WordTrace tailWord_6929241 prefixEnd_6929241 1186010401280409682140169 := by
  unfold tailWord_6929241
  simp only [CollatzResearch.WordTrace]
  refine ⟨252730181889550751991019577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168486787926367167994013051 252730181889550751991019577)
  ·
    refine ⟨189547636417163063993264683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252730181889550751991019577 189547636417163063993264683)
    ·
      refine ⟨284321454625744595989897025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189547636417163063993264683 284321454625744595989897025)
      ·
        refine ⟨213241090969308446992422769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284321454625744595989897025 213241090969308446992422769)
        ·
          refine ⟨159930818226981335244317077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213241090969308446992422769 159930818226981335244317077)
          ·
            refine ⟨7496757104389750089577363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159930818226981335244317077 7496757104389750089577363)
            ·
              refine ⟨11245135656584625134366045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7496757104389750089577363 11245135656584625134366045)
              ·
                refine ⟨4216925871219234425387267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11245135656584625134366045 4216925871219234425387267)
                ·
                  refine ⟨6325388806828851638080901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4216925871219234425387267 6325388806828851638080901)
                  ·
                    refine ⟨1186010401280409682140169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325388806828851638080901 1186010401280409682140169)
                    ·
                      rfl

theorem cell23_6929241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 1, 4].length) (baseStart_6929241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929241 prefixEnd_6929241 := by exact prefixLift 6929241
  have htrace : WordTrace (prefixWord ++ tailWord_6929241) baseStart_6929241 baseEnd_6929241 := by
    simpa [prefixWord, tailWord_6929241, baseEnd_6929241] using wordTrace_append hprefix tailTrace_6929241
  have hstable : (prefixWord ++ tailWord_6929241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929241).length < 2 ^ (prefixWord ++ tailWord_6929241).sum := by decide
  have hdescent : baseEnd_6929241 < baseStart_6929241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929264 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3]
def baseStart_6929264 : Nat := 118140960795 + 6929264 * 2 ^ 59
def prefixEnd_6929264 : Nat := 4983230072969 + 3 ^ 40 * 6929264 * 2
def baseEnd_6929264 : Nat := 3558043013896282456432901

theorem tailTrace_6929264 : CollatzResearch.WordTrace tailWord_6929264 prefixEnd_6929264 3558043013896282456432901 := by
  unfold tailWord_6929264
  simp only [CollatzResearch.WordTrace]
  refine ⟨126365510384233713459553423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168487347178978284612737897 126365510384233713459553423)
  ·
    refine ⟨189548265576350570189330135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126365510384233713459553423 189548265576350570189330135)
    ·
      refine ⟨284322398364525855283995203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189548265576350570189330135 284322398364525855283995203)
      ·
        refine ⟨426483597546788782925992805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284322398364525855283995203 426483597546788782925992805)
        ·
          refine ⟨79965674540022896798623651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426483597546788782925992805 79965674540022896798623651)
          ·
            refine ⟨119948511810034345197935477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79965674540022896798623651 119948511810034345197935477)
            ·
              refine ⟨11245172982190719862306451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119948511810034345197935477 11245172982190719862306451)
              ·
                refine ⟨16867759473286079793459677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245172982190719862306451 16867759473286079793459677)
                ·
                  refine ⟨6325409802482279922547379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16867759473286079793459677 6325409802482279922547379)
                  ·
                    refine ⟨9488114703723419883821069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6325409802482279922547379 9488114703723419883821069)
                    ·
                      refine ⟨3558043013896282456432901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9488114703723419883821069 3558043013896282456432901)
                      ·
                        rfl

theorem cell23_6929264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_6929264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929264 prefixEnd_6929264 := by exact prefixLift 6929264
  have htrace : WordTrace (prefixWord ++ tailWord_6929264) baseStart_6929264 baseEnd_6929264 := by
    simpa [prefixWord, tailWord_6929264, baseEnd_6929264] using wordTrace_append hprefix tailTrace_6929264
  have hstable : (prefixWord ++ tailWord_6929264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929264).length < 2 ^ (prefixWord ++ tailWord_6929264).sum := by decide
  have hdescent : baseEnd_6929264 < baseStart_6929264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929354 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3]
def baseStart_6929354 : Nat := 118140960795 + 6929354 * 2 ^ 59
def prefixEnd_6929354 : Nat := 4983230072969 + 3 ^ 40 * 6929354 * 2
def baseEnd_6929354 : Nat := 3558089227155187104307487

theorem tailTrace_6929354 : CollatzResearch.WordTrace tailWord_6929354 prefixEnd_6929354 3558089227155187104307487 := by
  unfold tailWord_6929354
  simp only [CollatzResearch.WordTrace]
  refine ⟨63183575834535343072470779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168489535558760914859922077 63183575834535343072470779)
  ·
    refine ⟨94775363751803014608706169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63183575834535343072470779 94775363751803014608706169)
    ·
      refine ⟨71081522813852260956529627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94775363751803014608706169 71081522813852260956529627)
      ·
        refine ⟨106622284220778391434794441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71081522813852260956529627 106622284220778391434794441)
        ·
          refine ⟨79966713165583793576095831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106622284220778391434794441 79966713165583793576095831)
          ·
            refine ⟨119950069748375690364143747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79966713165583793576095831 119950069748375690364143747)
            ·
              refine ⟨179925104622563535546215621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119950069748375690364143747 179925104622563535546215621)
              ·
                refine ⟨33735957116730662914915429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179925104622563535546215621 33735957116730662914915429)
                ·
                  refine ⟨6325491959386999296546643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33735957116730662914915429 6325491959386999296546643)
                  ·
                    refine ⟨9488237939080498944819965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6325491959386999296546643 9488237939080498944819965)
                    ·
                      refine ⟨3558089227155187104307487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9488237939080498944819965 3558089227155187104307487)
                      ·
                        rfl

theorem cell23_6929354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 4, 1, 3].length) (baseStart_6929354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929354 prefixEnd_6929354 := by exact prefixLift 6929354
  have htrace : WordTrace (prefixWord ++ tailWord_6929354) baseStart_6929354 baseEnd_6929354 := by
    simpa [prefixWord, tailWord_6929354, baseEnd_6929354] using wordTrace_append hprefix tailTrace_6929354
  have hstable : (prefixWord ++ tailWord_6929354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929354).length < 2 ^ (prefixWord ++ tailWord_6929354).sum := by decide
  have hdescent : baseEnd_6929354 < baseStart_6929354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929358 : List Nat := [4, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_6929358 : Nat := 118140960795 + 6929358 * 2 ^ 59
def prefixEnd_6929358 : Nat := 4983230072969 + 3 ^ 40 * 6929358 * 2
def baseEnd_6929358 : Nat := 3558091281077805088657469

theorem tailTrace_6929358 : CollatzResearch.WordTrace tailWord_6929358 prefixEnd_6929358 3558091281077805088657469 := by
  unfold tailWord_6929358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31591806153765860121628591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168489632820084587315352485 31591806153765860121628591)
  ·
    refine ⟨47387709230648790182442887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31591806153765860121628591 47387709230648790182442887)
    ·
      refine ⟨71081563845973185273664331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47387709230648790182442887 71081563845973185273664331)
      ·
        refine ⟨106622345768959777910496497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71081563845973185273664331 106622345768959777910496497)
        ·
          refine ⟨79966759326719833432872373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106622345768959777910496497 79966759326719833432872373)
          ·
            refine ⟨7496883686879984384331785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79966759326719833432872373 7496883686879984384331785)
            ·
              refine ⟨5622662765159988288248839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7496883686879984384331785 5622662765159988288248839)
              ·
                refine ⟨8433994147739982432373259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5622662765159988288248839 8433994147739982432373259)
                ·
                  refine ⟨12650991221609973648559889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8433994147739982432373259 12650991221609973648559889)
                  ·
                    refine ⟨9488243416207480236419917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12650991221609973648559889 9488243416207480236419917)
                    ·
                      refine ⟨3558091281077805088657469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9488243416207480236419917 3558091281077805088657469)
                      ·
                        rfl

theorem cell23_6929358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_6929358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929358 prefixEnd_6929358 := by exact prefixLift 6929358
  have htrace : WordTrace (prefixWord ++ tailWord_6929358) baseStart_6929358 baseEnd_6929358 := by
    simpa [prefixWord, tailWord_6929358, baseEnd_6929358] using wordTrace_append hprefix tailTrace_6929358
  have hstable : (prefixWord ++ tailWord_6929358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929358).length < 2 ^ (prefixWord ++ tailWord_6929358).sum := by decide
  have hdescent : baseEnd_6929358 < baseStart_6929358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929398 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_6929398 : Nat := 118140960795 + 6929398 * 2 ^ 59
def prefixEnd_6929398 : Nat := 4983230072969 + 3 ^ 40 * 6929398 * 2
def baseEnd_6929398 : Nat := 3558111820303984932157285

theorem tailTrace_6929398 : CollatzResearch.WordTrace tailWord_6929398 prefixEnd_6929398 3558111820303984932157285 := by
  unfold tailWord_6929398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15795994259373872987780303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168490605433321311869656565 15795994259373872987780303)
  ·
    refine ⟨23693991389060809481670455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15795994259373872987780303 23693991389060809481670455)
    ·
      refine ⟨35540987083591214222505683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23693991389060809481670455 35540987083591214222505683)
      ·
        refine ⟨53311480625386821333758525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35540987083591214222505683 53311480625386821333758525)
        ·
          refine ⟨19991805234520058000159447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53311480625386821333758525 19991805234520058000159447)
          ·
            refine ⟨29987707851780087000239171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19991805234520058000159447 29987707851780087000239171)
            ·
              refine ⟨44981561777670130500358757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29987707851780087000239171 44981561777670130500358757)
              ·
                refine ⟨8434042833313149468817267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44981561777670130500358757 8434042833313149468817267)
                ·
                  refine ⟨12651064249969724203225901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434042833313149468817267 12651064249969724203225901)
                  ·
                    refine ⟨4744149093738646576209713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12651064249969724203225901 4744149093738646576209713)
                    ·
                      refine ⟨3558111820303984932157285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744149093738646576209713 3558111820303984932157285)
                      ·
                        rfl

theorem cell23_6929398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_6929398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929398 prefixEnd_6929398 := by exact prefixLift 6929398
  have htrace : WordTrace (prefixWord ++ tailWord_6929398) baseStart_6929398 baseEnd_6929398 := by
    simpa [prefixWord, tailWord_6929398, baseEnd_6929398] using wordTrace_append hprefix tailTrace_6929398
  have hstable : (prefixWord ++ tailWord_6929398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929398).length < 2 ^ (prefixWord ++ tailWord_6929398).sum := by decide
  have hdescent : baseEnd_6929398 < baseStart_6929398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929457 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_6929457 : Nat := 118140960795 + 6929457 * 2 ^ 59
def prefixEnd_6929457 : Nat := 4983230072969 + 3 ^ 40 * 6929457 * 2
def baseEnd_6929457 : Nat := 3558142115662600201319513

theorem tailTrace_6929457 : CollatzResearch.WordTrace tailWord_6929457 prefixEnd_6929457 3558142115662600201319513 := by
  unfold tailWord_6929457
  simp only [CollatzResearch.WordTrace]
  refine ⟨252738060056768220880882625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168492040037845480587255083 252738060056768220880882625)
  ·
    refine ⟨189553545042576165660661969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252738060056768220880882625 189553545042576165660661969)
    ·
      refine ⟨142165158781932124245496477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189553545042576165660661969 142165158781932124245496477)
      ·
        refine ⟨53311934543224546592061179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142165158781932124245496477 53311934543224546592061179)
        ·
          refine ⟨79967901814836819888091769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53311934543224546592061179 79967901814836819888091769)
          ·
            refine ⟨59975926361127614916068827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79967901814836819888091769 59975926361127614916068827)
            ·
              refine ⟨89963889541691422374103241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59975926361127614916068827 89963889541691422374103241)
              ·
                refine ⟨67472917156268566780577431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89963889541691422374103241 67472917156268566780577431)
                ·
                  refine ⟨101209375734402850170866147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67472917156268566780577431 101209375734402850170866147)
                  ·
                    refine ⟨151814063601604275256299221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101209375734402850170866147 151814063601604275256299221)
                    ·
                      refine ⟨3558142115662600201319513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151814063601604275256299221 3558142115662600201319513)
                      ·
                        rfl

theorem cell23_6929457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_6929457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929457 prefixEnd_6929457 := by exact prefixLift 6929457
  have htrace : WordTrace (prefixWord ++ tailWord_6929457) baseStart_6929457 baseEnd_6929457 := by
    simpa [prefixWord, tailWord_6929457, baseEnd_6929457] using wordTrace_append hprefix tailTrace_6929457
  have hstable : (prefixWord ++ tailWord_6929457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929457).length < 2 ^ (prefixWord ++ tailWord_6929457).sum := by decide
  have hdescent : baseEnd_6929457 < baseStart_6929457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929464 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 2, 5]
def baseStart_6929464 : Nat := 118140960795 + 6929464 * 2 ^ 59
def prefixEnd_6929464 : Nat := 4983230072969 + 3 ^ 40 * 6929464 * 2
def baseEnd_6929464 : Nat := 1186048570009060557977327

theorem tailTrace_6929464 : CollatzResearch.WordTrace tailWord_6929464 prefixEnd_6929464 1186048570009060557977327 := by
  unfold tailWord_6929464
  simp only [CollatzResearch.WordTrace]
  refine ⟨126369157683871430538193723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168492210245161907384258297 126369157683871430538193723)
  ·
    refine ⟨189553736525807145807290585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126369157683871430538193723 189553736525807145807290585)
    ·
      refine ⟨142165302394355359355467939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189553736525807145807290585 142165302394355359355467939)
      ·
        refine ⟨213247953591533039033201909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142165302394355359355467939 213247953591533039033201909)
        ·
          refine ⟨19991995649206222409362679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213247953591533039033201909 19991995649206222409362679)
          ·
            refine ⟨29987993473809333614044019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19991995649206222409362679 29987993473809333614044019)
            ·
              refine ⟨44981990210714000421066029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29987993473809333614044019 44981990210714000421066029)
              ·
                refine ⟨16868246329017750157899761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44981990210714000421066029 16868246329017750157899761)
                ·
                  refine ⟨12651184746763312618424821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16868246329017750157899761 12651184746763312618424821)
                  ·
                    refine ⟨1186048570009060557977327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12651184746763312618424821 1186048570009060557977327)
                    ·
                      rfl

theorem cell23_6929464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_6929464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929464 prefixEnd_6929464 := by exact prefixLift 6929464
  have htrace : WordTrace (prefixWord ++ tailWord_6929464) baseStart_6929464 baseEnd_6929464 := by
    simpa [prefixWord, tailWord_6929464, baseEnd_6929464] using wordTrace_append hprefix tailTrace_6929464
  have hstable : (prefixWord ++ tailWord_6929464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929464).length < 2 ^ (prefixWord ++ tailWord_6929464).sum := by decide
  have hdescent : baseEnd_6929464 < baseStart_6929464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929485 : List Nat := [1, 6, 1, 1, 1, 4, 2, 2, 5]
def baseStart_6929485 : Nat := 118140960795 + 6929485 * 2 ^ 59
def prefixEnd_6929485 : Nat := 4983230072969 + 3 ^ 40 * 6929485 * 2
def baseEnd_6929485 : Nat := 395350721457880676863265

theorem tailTrace_6929485 : CollatzResearch.WordTrace tailWord_6929485 prefixEnd_6929485 395350721457880676863265 := by
  unfold tailWord_6929485
  simp only [CollatzResearch.WordTrace]
  refine ⟨252739081300666781662901909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168492720867111187775267939 252739081300666781662901909)
  ·
    refine ⟨11847144435968755390448527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252739081300666781662901909 11847144435968755390448527)
    ·
      refine ⟨17770716653953133085672791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11847144435968755390448527 17770716653953133085672791)
      ·
        refine ⟨26656074980929699628509187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17770716653953133085672791 26656074980929699628509187)
        ·
          refine ⟨39984112471394549442763781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26656074980929699628509187 39984112471394549442763781)
          ·
            refine ⟨7497021088386478020518209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39984112471394549442763781 7497021088386478020518209)
            ·
              refine ⟨5622765816289858515388657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7497021088386478020518209 5622765816289858515388657)
              ·
                refine ⟨4217074362217393886541493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5622765816289858515388657 4217074362217393886541493)
                ·
                  refine ⟨395350721457880676863265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4217074362217393886541493 395350721457880676863265)
                  ·
                    rfl

theorem cell23_6929485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_6929485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929485 prefixEnd_6929485 := by exact prefixLift 6929485
  have htrace : WordTrace (prefixWord ++ tailWord_6929485) baseStart_6929485 baseEnd_6929485 := by
    simpa [prefixWord, tailWord_6929485, baseEnd_6929485] using wordTrace_append hprefix tailTrace_6929485
  have hstable : (prefixWord ++ tailWord_6929485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929485).length < 2 ^ (prefixWord ++ tailWord_6929485).sum := by decide
  have hdescent : baseEnd_6929485 < baseStart_6929485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929497 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_6929497 : Nat := 118140960795 + 6929497 * 2 ^ 59
def prefixEnd_6929497 : Nat := 4983230072969 + 3 ^ 40 * 6929497 * 2
def baseEnd_6929497 : Nat := 3558162654888780044819329

theorem tailTrace_6929497 : CollatzResearch.WordTrace tailWord_6929497 prefixEnd_6929497 3558162654888780044819329 := by
  unfold tailWord_6929497
  simp only [CollatzResearch.WordTrace]
  refine ⟨252739518976623307712338745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168493012651082205141559163 252739518976623307712338745)
  ·
    refine ⟨189554639232467480784254059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252739518976623307712338745 189554639232467480784254059)
    ·
      refine ⟨284331958848701221176381089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189554639232467480784254059 284331958848701221176381089)
      ·
        refine ⟨213248969136525915882285817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284331958848701221176381089 213248969136525915882285817)
        ·
          refine ⟨159936726852394436911714363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213248969136525915882285817 159936726852394436911714363)
          ·
            refine ⟨239905090278591655367571545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159936726852394436911714363 239905090278591655367571545)
            ·
              refine ⟨179928817708943741525678659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239905090278591655367571545 179928817708943741525678659)
              ·
                refine ⟨269893226563415612288517989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179928817708943741525678659 269893226563415612288517989)
                ·
                  refine ⟨50604979980640427304097123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269893226563415612288517989 50604979980640427304097123)
                  ·
                    refine ⟨75907469970960640956145685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50604979980640427304097123 75907469970960640956145685)
                    ·
                      refine ⟨3558162654888780044819329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75907469970960640956145685 3558162654888780044819329)
                      ·
                        rfl

theorem cell23_6929497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_6929497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929497 prefixEnd_6929497 := by exact prefixLift 6929497
  have htrace : WordTrace (prefixWord ++ tailWord_6929497) baseStart_6929497 baseEnd_6929497 := by
    simpa [prefixWord, tailWord_6929497, baseEnd_6929497] using wordTrace_append hprefix tailTrace_6929497
  have hstable : (prefixWord ++ tailWord_6929497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929497).length < 2 ^ (prefixWord ++ tailWord_6929497).sum := by decide
  have hdescent : baseEnd_6929497 < baseStart_6929497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929504 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3]
def baseStart_6929504 : Nat := 118140960795 + 6929504 * 2 ^ 59
def prefixEnd_6929504 : Nat := 4983230072969 + 3 ^ 40 * 6929504 * 2
def baseEnd_6929504 : Nat := 3558166249253361517431797

theorem tailTrace_6929504 : CollatzResearch.WordTrace tailWord_6929504 prefixEnd_6929504 3558166249253361517431797 := by
  unfold tailWord_6929504
  simp only [CollatzResearch.WordTrace]
  refine ⟨126369887143798973953921783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168493182858398631938562377 126369887143798973953921783)
  ·
    refine ⟨189554830715698460930882675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126369887143798973953921783 189554830715698460930882675)
    ·
      refine ⟨284332246073547691396324013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189554830715698460930882675 284332246073547691396324013)
      ·
        refine ⟨106624592277580384273621505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284332246073547691396324013 106624592277580384273621505)
        ·
          refine ⟨79968444208185288205216129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106624592277580384273621505 79968444208185288205216129)
          ·
            refine ⟨59976333156138966153912097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79968444208185288205216129 59976333156138966153912097)
            ·
              refine ⟨44982249867104224615434073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59976333156138966153912097 44982249867104224615434073)
              ·
                refine ⟨33736687400328168461575555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44982249867104224615434073 33736687400328168461575555)
                ·
                  refine ⟨50605031100492252692363333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33736687400328168461575555 50605031100492252692363333)
                  ·
                    refine ⟨9488443331342297379818125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50605031100492252692363333 9488443331342297379818125)
                    ·
                      refine ⟨3558166249253361517431797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9488443331342297379818125 3558166249253361517431797)
                      ·
                        rfl

theorem cell23_6929504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_6929504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929504 prefixEnd_6929504 := by exact prefixLift 6929504
  have htrace : WordTrace (prefixWord ++ tailWord_6929504) baseStart_6929504 baseEnd_6929504 := by
    simpa [prefixWord, tailWord_6929504, baseEnd_6929504] using wordTrace_append hprefix tailTrace_6929504
  have hstable : (prefixWord ++ tailWord_6929504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929504).length < 2 ^ (prefixWord ++ tailWord_6929504).sum := by decide
  have hdescent : baseEnd_6929504 < baseStart_6929504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929507 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 10]
def baseStart_6929507 : Nat := 118140960795 + 6929507 * 2 ^ 59
def prefixEnd_6929507 : Nat := 4983230072969 + 3 ^ 40 * 6929507 * 2
def baseEnd_6929507 : Nat := 395351976632813889521587

theorem tailTrace_6929507 : CollatzResearch.WordTrace tailWord_6929507 prefixEnd_6929507 395351976632813889521587 := by
  unfold tailWord_6929507
  simp only [CollatzResearch.WordTrace]
  refine ⟨252739883706587079420202775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168493255804391386280135183 252739883706587079420202775)
  ·
    refine ⟨379109825559880619130304163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252739883706587079420202775 379109825559880619130304163)
    ·
      refine ⟨568664738339820928695456245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379109825559880619130304163 568664738339820928695456245)
      ·
        refine ⟨53312319219358212065199023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 568664738339820928695456245 53312319219358212065199023)
        ·
          refine ⟨79968478829037318097798535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53312319219358212065199023 79968478829037318097798535)
          ·
            refine ⟨119952718243555977146697803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79968478829037318097798535 119952718243555977146697803)
            ·
              refine ⟨179929077365333965720046705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119952718243555977146697803 179929077365333965720046705)
              ·
                refine ⟨134946808024000474290035029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179929077365333965720046705 134946808024000474290035029)
                ·
                  refine ⟨395351976632813889521587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134946808024000474290035029 395351976632813889521587)
                  ·
                    rfl

theorem cell23_6929507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 10].length) (baseStart_6929507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929507 prefixEnd_6929507 := by exact prefixLift 6929507
  have htrace : WordTrace (prefixWord ++ tailWord_6929507) baseStart_6929507 baseEnd_6929507 := by
    simpa [prefixWord, tailWord_6929507, baseEnd_6929507] using wordTrace_append hprefix tailTrace_6929507
  have hstable : (prefixWord ++ tailWord_6929507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929507).length < 2 ^ (prefixWord ++ tailWord_6929507).sum := by decide
  have hdescent : baseEnd_6929507 < baseStart_6929507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929511 : List Nat := [1, 1, 5, 1, 1, 4, 1, 2, 3, 4]
def baseStart_6929511 : Nat := 118140960795 + 6929511 * 2 ^ 59
def prefixEnd_6929511 : Nat := 4983230072969 + 3 ^ 40 * 6929511 * 2
def baseEnd_6929511 : Nat := 1186056614539314330014755

theorem tailTrace_6929511 : CollatzResearch.WordTrace tailWord_6929511 prefixEnd_6929511 1186056614539314330014755 := by
  unfold tailWord_6929511
  simp only [CollatzResearch.WordTrace]
  refine ⟨252740029598572588103348387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168493353065715058735565591 252740029598572588103348387)
  ·
    refine ⟨379110044397858882155022581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252740029598572588103348387 379110044397858882155022581)
    ·
      refine ⟨35541566662299270202033367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379110044397858882155022581 35541566662299270202033367)
      ·
        refine ⟨53312349993448905303050051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35541566662299270202033367 53312349993448905303050051)
        ·
          refine ⟨79968524990173357954575077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53312349993448905303050051 79968524990173357954575077)
          ·
            refine ⟨14994098435657504616482827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79968524990173357954575077 14994098435657504616482827)
            ·
              refine ⟨22491147653486256924724241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14994098435657504616482827 22491147653486256924724241)
              ·
                refine ⟨16868360740114692693543181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22491147653486256924724241 16868360740114692693543181)
                ·
                  refine ⟨6325635277543009760078693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16868360740114692693543181 6325635277543009760078693)
                  ·
                    refine ⟨1186056614539314330014755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325635277543009760078693 1186056614539314330014755)
                    ·
                      rfl

theorem cell23_6929511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_6929511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929511 prefixEnd_6929511 := by exact prefixLift 6929511
  have htrace : WordTrace (prefixWord ++ tailWord_6929511) baseStart_6929511 baseEnd_6929511 := by
    simpa [prefixWord, tailWord_6929511, baseEnd_6929511] using wordTrace_append hprefix tailTrace_6929511
  have hstable : (prefixWord ++ tailWord_6929511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929511).length < 2 ^ (prefixWord ++ tailWord_6929511).sum := by decide
  have hdescent : baseEnd_6929511 < baseStart_6929511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929518 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_6929518 : Nat := 118140960795 + 6929518 * 2 ^ 59
def prefixEnd_6929518 : Nat := 4983230072969 + 3 ^ 40 * 6929518 * 2
def baseEnd_6929518 : Nat := 3558173437982524462656733

theorem tailTrace_6929518 : CollatzResearch.WordTrace tailWord_6929518 prefixEnd_6929518 3558173437982524462656733 := by
  unfold tailWord_6929518
  simp only [CollatzResearch.WordTrace]
  refine ⟨31592535613693403537356651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168493523273031485532568805 31592535613693403537356651)
  ·
    refine ⟨47388803420540105306034977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31592535613693403537356651 47388803420540105306034977)
    ·
      refine ⟨35541602565405078979526233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47388803420540105306034977 35541602565405078979526233)
      ·
        refine ⟨26656201924053809234644675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35541602565405078979526233 26656201924053809234644675)
        ·
          refine ⟨39984302886080713851967013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26656201924053809234644675 39984302886080713851967013)
          ·
            refine ⟨7497056791140133847243815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39984302886080713851967013 7497056791140133847243815)
            ·
              refine ⟨11245585186710200770865723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497056791140133847243815 11245585186710200770865723)
              ·
                refine ⟨16868377780065301156298585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245585186710200770865723 16868377780065301156298585)
                ·
                  refine ⟨12651283335048975867223939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16868377780065301156298585 12651283335048975867223939)
                  ·
                    refine ⟨18976925002573463800835909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12651283335048975867223939 18976925002573463800835909)
                    ·
                      refine ⟨3558173437982524462656733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18976925002573463800835909 3558173437982524462656733)
                      ·
                        rfl

theorem cell23_6929518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_6929518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929518 prefixEnd_6929518 := by exact prefixLift 6929518
  have htrace : WordTrace (prefixWord ++ tailWord_6929518) baseStart_6929518 baseEnd_6929518 := by
    simpa [prefixWord, tailWord_6929518, baseEnd_6929518] using wordTrace_append hprefix tailTrace_6929518
  have hstable : (prefixWord ++ tailWord_6929518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929518).length < 2 ^ (prefixWord ++ tailWord_6929518).sum := by decide
  have hdescent : baseEnd_6929518 < baseStart_6929518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929591 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 4]
def baseStart_6929591 : Nat := 118140960795 + 6929591 * 2 ^ 59
def prefixEnd_6929591 : Nat := 4983230072969 + 3 ^ 40 * 6929591 * 2
def baseEnd_6929591 : Nat := 3558210922070302677043897

theorem tailTrace_6929591 : CollatzResearch.WordTrace tailWord_6929591 prefixEnd_6929591 3558210922070302677043897 := by
  unfold tailWord_6929591
  simp only [CollatzResearch.WordTrace]
  refine ⟨252742947438282761766260627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168495298292188507844173751 252742947438282761766260627)
  ·
    refine ⟨379114421157424142649390941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252742947438282761766260627 379114421157424142649390941)
    ·
      refine ⟨142167907934034053493521603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379114421157424142649390941 142167907934034053493521603)
      ·
        refine ⟨213251861901051080240282405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142167907934034053493521603 213251861901051080240282405)
        ·
          refine ⟨39984724106447077545052951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213251861901051080240282405 39984724106447077545052951)
          ·
            refine ⟨59977086159670616317579427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39984724106447077545052951 59977086159670616317579427)
            ·
              refine ⟨89965629239505924476369141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59977086159670616317579427 89965629239505924476369141)
              ·
                refine ⟨8434277741203680419659607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89965629239505924476369141 8434277741203680419659607)
                ·
                  refine ⟨12651416611805520629489411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434277741203680419659607 12651416611805520629489411)
                  ·
                    refine ⟨18977124917708280944234117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12651416611805520629489411 18977124917708280944234117)
                    ·
                      refine ⟨3558210922070302677043897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18977124917708280944234117 3558210922070302677043897)
                      ·
                        rfl

theorem cell23_6929591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 4].length) (baseStart_6929591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929591 prefixEnd_6929591 := by exact prefixLift 6929591
  have htrace : WordTrace (prefixWord ++ tailWord_6929591) baseStart_6929591 baseEnd_6929591 := by
    simpa [prefixWord, tailWord_6929591, baseEnd_6929591] using wordTrace_append hprefix tailTrace_6929591
  have hstable : (prefixWord ++ tailWord_6929591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929591).length < 2 ^ (prefixWord ++ tailWord_6929591).sum := by decide
  have hdescent : baseEnd_6929591 < baseStart_6929591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929618 : List Nat := [3, 2, 2, 2, 1, 1, 3, 3, 2, 4]
def baseStart_6929618 : Nat := 118140960795 + 6929618 * 2 ^ 59
def prefixEnd_6929618 : Nat := 4983230072969 + 3 ^ 40 * 6929618 * 2
def baseEnd_6929618 : Nat := 1186074928682658023802091

theorem tailTrace_6929618 : CollatzResearch.WordTrace tailWord_6929618 prefixEnd_6929618 1186074928682658023802091 := by
  unfold tailWord_6929618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63185983052296236344373377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168495954806123296918329005 63185983052296236344373377)
  ·
    refine ⟨47389487289222177258280033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63185983052296236344373377 47389487289222177258280033)
    ·
      refine ⟨35542115466916632943710025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47389487289222177258280033 35542115466916632943710025)
      ·
        refine ⟨26656586600187474707782519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35542115466916632943710025 26656586600187474707782519)
        ·
          refine ⟨39984879900281212061673779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26656586600187474707782519 39984879900281212061673779)
          ·
            refine ⟨59977319850421818092510669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39984879900281212061673779 59977319850421818092510669)
            ·
              refine ⟨22491494943908181784691501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59977319850421818092510669 22491494943908181784691501)
              ·
                refine ⟨8434310603965568169259313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22491494943908181784691501 8434310603965568169259313)
                ·
                  refine ⟨6325732952974176126944485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8434310603965568169259313 6325732952974176126944485)
                  ·
                    refine ⟨1186074928682658023802091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325732952974176126944485 1186074928682658023802091)
                    ·
                      rfl

theorem cell23_6929618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_6929618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929618 prefixEnd_6929618 := by exact prefixLift 6929618
  have htrace : WordTrace (prefixWord ++ tailWord_6929618) baseStart_6929618 baseEnd_6929618 := by
    simpa [prefixWord, tailWord_6929618, baseEnd_6929618] using wordTrace_append hprefix tailTrace_6929618
  have hstable : (prefixWord ++ tailWord_6929618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929618).length < 2 ^ (prefixWord ++ tailWord_6929618).sum := by decide
  have hdescent : baseEnd_6929618 < baseStart_6929618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929621 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6929621 : Nat := 118140960795 + 6929621 * 2 ^ 59
def prefixEnd_6929621 : Nat := 4983230072969 + 3 ^ 40 * 6929621 * 2
def baseEnd_6929621 : Nat := 3558226326489937559668759

theorem tailTrace_6929621 : CollatzResearch.WordTrace tailWord_6929621 prefixEnd_6929621 3558226326489937559668759 := by
  unfold tailWord_6929621
  simp only [CollatzResearch.WordTrace]
  refine ⟨252744041628174076889852717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168496027752116051259901811 252744041628174076889852717)
  ·
    refine ⟨94779015610565278833694769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252744041628174076889852717 94779015610565278833694769)
    ·
      refine ⟨71084261707923959125271077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94779015610565278833694769 71084261707923959125271077)
      ·
        refine ⟨13328299070235742335988327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71084261707923959125271077 13328299070235742335988327)
        ·
          refine ⟨19992448605353613503982491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13328299070235742335988327 19992448605353613503982491)
          ·
            refine ⟨29988672908030420255973737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19992448605353613503982491 29988672908030420255973737)
            ·
              refine ⟨22491504681022815191980303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29988672908030420255973737 22491504681022815191980303)
              ·
                refine ⟨33737257021534222787970455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491504681022815191980303 33737257021534222787970455)
                ·
                  refine ⟨50605885532301334181955683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33737257021534222787970455 50605885532301334181955683)
                  ·
                    refine ⟨75908828298452001272933525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50605885532301334181955683 75908828298452001272933525)
                    ·
                      refine ⟨3558226326489937559668759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75908828298452001272933525 3558226326489937559668759)
                      ·
                        rfl

theorem cell23_6929621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6929621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929621 prefixEnd_6929621 := by exact prefixLift 6929621
  have htrace : WordTrace (prefixWord ++ tailWord_6929621) baseStart_6929621 baseEnd_6929621 := by
    simpa [prefixWord, tailWord_6929621, baseEnd_6929621] using wordTrace_append hprefix tailTrace_6929621
  have hstable : (prefixWord ++ tailWord_6929621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929621).length < 2 ^ (prefixWord ++ tailWord_6929621).sum := by decide
  have hdescent : baseEnd_6929621 < baseStart_6929621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929622 : List Nat := [5, 2, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_6929622 : Nat := 118140960795 + 6929622 * 2 ^ 59
def prefixEnd_6929622 : Nat := 4983230072969 + 3 ^ 40 * 6929622 * 2
def baseEnd_6929622 : Nat := 1186075613323530685252085

theorem tailTrace_6929622 : CollatzResearch.WordTrace tailWord_6929622 prefixEnd_6929622 1186075613323530685252085 := by
  unfold tailWord_6929622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15796504881323153378789945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168496052067446969373759413 15796504881323153378789945)
  ·
    refine ⟨11847378660992365034092459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15796504881323153378789945 11847378660992365034092459)
    ·
      refine ⟨17771067991488547551138689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11847378660992365034092459 17771067991488547551138689)
      ·
        refine ⟨13328300993616410663354017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17771067991488547551138689 13328300993616410663354017)
        ·
          refine ⟨9996225745212307997515513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13328300993616410663354017 9996225745212307997515513)
          ·
            refine ⟨7497169308909230998136635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9996225745212307997515513 7497169308909230998136635)
            ·
              refine ⟨11245753963363846497204953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497169308909230998136635 11245753963363846497204953)
              ·
                refine ⟨8434315472522884872903715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11245753963363846497204953 8434315472522884872903715)
                ·
                  refine ⟨12651473208784327309355573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434315472522884872903715 12651473208784327309355573)
                  ·
                    refine ⟨1186075613323530685252085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12651473208784327309355573 1186075613323530685252085)
                    ·
                      rfl

theorem cell23_6929622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_6929622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929622 prefixEnd_6929622 := by exact prefixLift 6929622
  have htrace : WordTrace (prefixWord ++ tailWord_6929622) baseStart_6929622 baseEnd_6929622 := by
    simpa [prefixWord, tailWord_6929622, baseEnd_6929622] using wordTrace_append hprefix tailTrace_6929622
  have hstable : (prefixWord ++ tailWord_6929622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929622).length < 2 ^ (prefixWord ++ tailWord_6929622).sum := by decide
  have hdescent : baseEnd_6929622 < baseStart_6929622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929709 : List Nat := [1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_6929709 : Nat := 118140960795 + 6929709 * 2 ^ 59
def prefixEnd_6929709 : Nat := 4983230072969 + 3 ^ 40 * 6929709 * 2
def baseEnd_6929709 : Nat := 3558271512787533215368355

theorem tailTrace_6929709 : CollatzResearch.WordTrace tailWord_6929709 prefixEnd_6929709 3558271512787533215368355 := by
  unfold tailWord_6929709
  simp only [CollatzResearch.WordTrace]
  refine ⟨252747251251855267919056181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168498167501236845279370787 252747251251855267919056181)
  ·
    refine ⟨23695054804861431367411517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252747251251855267919056181 23695054804861431367411517)
    ·
      refine ⟨8885645551823036762779319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23695054804861431367411517 8885645551823036762779319)
      ·
        refine ⟨13328468327734555144168979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8885645551823036762779319 13328468327734555144168979)
        ·
          refine ⟨19992702491601832716253469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13328468327734555144168979 19992702491601832716253469)
          ·
            refine ⟨7497263434350687268595051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19992702491601832716253469 7497263434350687268595051)
            ·
              refine ⟨11245895151526030902892577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497263434350687268595051 11245895151526030902892577)
              ·
                refine ⟨8434421363644523177169433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11245895151526030902892577 8434421363644523177169433)
                ·
                  refine ⟨6325816022733392382877075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8434421363644523177169433 6325816022733392382877075)
                  ·
                    refine ⟨9488724034100088574315613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6325816022733392382877075 9488724034100088574315613)
                    ·
                      refine ⟨3558271512787533215368355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9488724034100088574315613 3558271512787533215368355)
                      ·
                        rfl

theorem cell23_6929709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_6929709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929709 prefixEnd_6929709 := by exact prefixLift 6929709
  have htrace : WordTrace (prefixWord ++ tailWord_6929709) baseStart_6929709 baseEnd_6929709 := by
    simpa [prefixWord, tailWord_6929709, baseEnd_6929709] using wordTrace_append hprefix tailTrace_6929709
  have hstable : (prefixWord ++ tailWord_6929709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929709).length < 2 ^ (prefixWord ++ tailWord_6929709).sum := by decide
  have hdescent : baseEnd_6929709 < baseStart_6929709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929715 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 4, 2, 2]
def baseStart_6929715 : Nat := 118140960795 + 6929715 * 2 ^ 59
def prefixEnd_6929715 : Nat := 4983230072969 + 3 ^ 40 * 6929715 * 2
def baseEnd_6929715 : Nat := 3558274593671460191893327

theorem tailTrace_6929715 : CollatzResearch.WordTrace tailWord_6929715 prefixEnd_6929715 3558274593671460191893327 := by
  unfold tailWord_6929715
  simp only [CollatzResearch.WordTrace]
  refine ⟨252747470089833530943774599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168498313393222353962516399 252747470089833530943774599)
  ·
    refine ⟨379121205134750296415661899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252747470089833530943774599 379121205134750296415661899)
    ·
      refine ⟨568681807702125444623492849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379121205134750296415661899 568681807702125444623492849)
      ·
        refine ⟨426511355776594083467619637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568681807702125444623492849 426511355776594083467619637)
        ·
          refine ⟨39985439604055695325089341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 426511355776594083467619637 39985439604055695325089341)
          ·
            refine ⟨14994539851520885746908503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39985439604055695325089341 14994539851520885746908503)
            ·
              refine ⟨22491809777281328620362755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14994539851520885746908503 22491809777281328620362755)
              ·
                refine ⟨33737714665921992930544133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491809777281328620362755 33737714665921992930544133)
                ·
                  refine ⟨6325821499860373674477025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33737714665921992930544133 6325821499860373674477025)
                  ·
                    refine ⟨4744366124895280255857769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6325821499860373674477025 4744366124895280255857769)
                    ·
                      refine ⟨3558274593671460191893327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744366124895280255857769 3558274593671460191893327)
                      ·
                        rfl

theorem cell23_6929715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 2, 2].length) (baseStart_6929715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929715 prefixEnd_6929715 := by exact prefixLift 6929715
  have htrace : WordTrace (prefixWord ++ tailWord_6929715) baseStart_6929715 baseEnd_6929715 := by
    simpa [prefixWord, tailWord_6929715, baseEnd_6929715] using wordTrace_append hprefix tailTrace_6929715
  have hstable : (prefixWord ++ tailWord_6929715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929715).length < 2 ^ (prefixWord ++ tailWord_6929715).sum := by decide
  have hdescent : baseEnd_6929715 < baseStart_6929715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929732 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_6929732 : Nat := 118140960795 + 6929732 * 2 ^ 59
def prefixEnd_6929732 : Nat := 4983230072969 + 3 ^ 40 * 6929732 * 2
def baseEnd_6929732 : Nat := 3558283322842586625380749

theorem tailTrace_6929732 : CollatzResearch.WordTrace tailWord_6929732 prefixEnd_6929732 3558283322842586625380749 := by
  unfold tailWord_6929732
  simp only [CollatzResearch.WordTrace]
  refine ⟨126374045065385971423571725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168498726753847961898095633 126374045065385971423571725)
  ·
    refine ⟨47390266899519739283839397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126374045065385971423571725 47390266899519739283839397)
    ·
      refine ⟨8885675043659951115719887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47390266899519739283839397 8885675043659951115719887)
      ·
        refine ⟨13328512565489926673579831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8885675043659951115719887 13328512565489926673579831)
        ·
          refine ⟨19992768848234890010369747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13328512565489926673579831 19992768848234890010369747)
          ·
            refine ⟨29989153272352335015554621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19992768848234890010369747 29989153272352335015554621)
            ·
              refine ⟨11245932477132125630832983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29989153272352335015554621 11245932477132125630832983)
              ·
                refine ⟨16868898715698188446249475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11245932477132125630832983 16868898715698188446249475)
                ·
                  refine ⟨25303348073547282669374213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16868898715698188446249475 25303348073547282669374213)
                  ·
                    refine ⟨4744377763790115500507665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25303348073547282669374213 4744377763790115500507665)
                    ·
                      refine ⟨3558283322842586625380749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744377763790115500507665 3558283322842586625380749)
                      ·
                        rfl

theorem cell23_6929732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_6929732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929732 prefixEnd_6929732 := by exact prefixLift 6929732
  have htrace : WordTrace (prefixWord ++ tailWord_6929732) baseStart_6929732 baseEnd_6929732 := by
    simpa [prefixWord, tailWord_6929732, baseEnd_6929732] using wordTrace_append hprefix tailTrace_6929732
  have hstable : (prefixWord ++ tailWord_6929732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929732).length < 2 ^ (prefixWord ++ tailWord_6929732).sum := by decide
  have hdescent : baseEnd_6929732 < baseStart_6929732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929751 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 1, 7]
def baseStart_6929751 : Nat := 118140960795 + 6929751 * 2 ^ 59
def prefixEnd_6929751 : Nat := 4983230072969 + 3 ^ 40 * 6929751 * 2
def baseEnd_6929751 : Nat := 1186097692991674017014387

theorem tailTrace_6929751 : CollatzResearch.WordTrace tailWord_6929751 prefixEnd_6929751 1186097692991674017014387 := by
  unfold tailWord_6929751
  simp only [CollatzResearch.WordTrace]
  refine ⟨252748783117703109092085107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168499188745135406061390071 252748783117703109092085107)
  ·
    refine ⟨379123174676554663638127661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252748783117703109092085107 379123174676554663638127661)
    ·
      refine ⟨142171190503707998864297873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379123174676554663638127661 142171190503707998864297873)
      ·
        refine ⟨106628392877780999148223405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142171190503707998864297873 106628392877780999148223405)
        ·
          refine ⟨39985647329167874680583777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106628392877780999148223405 39985647329167874680583777)
          ·
            refine ⟨29989235496875906010437833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39985647329167874680583777 29989235496875906010437833)
            ·
              refine ⟨22491926622656929507828375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29989235496875906010437833 22491926622656929507828375)
              ·
                refine ⟨33737889933985394261742563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491926622656929507828375 33737889933985394261742563)
                ·
                  refine ⟨50606834900978091392613845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33737889933985394261742563 50606834900978091392613845)
                  ·
                    refine ⟨1186097692991674017014387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50606834900978091392613845 1186097692991674017014387)
                    ·
                      rfl

theorem cell23_6929751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_6929751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929751 prefixEnd_6929751 := by exact prefixLift 6929751
  have htrace : WordTrace (prefixWord ++ tailWord_6929751) baseStart_6929751 baseEnd_6929751 := by
    simpa [prefixWord, tailWord_6929751, baseEnd_6929751] using wordTrace_append hprefix tailTrace_6929751
  have hstable : (prefixWord ++ tailWord_6929751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929751).length < 2 ^ (prefixWord ++ tailWord_6929751).sum := by decide
  have hdescent : baseEnd_6929751 < baseStart_6929751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929788 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 6, 2]
def baseStart_6929788 : Nat := 118140960795 + 6929788 * 2 ^ 59
def prefixEnd_6929788 : Nat := 4983230072969 + 3 ^ 40 * 6929788 * 2
def baseEnd_6929788 : Nat := 3558312077759238406280491

theorem tailTrace_6929788 : CollatzResearch.WordTrace tailWord_6929788 prefixEnd_6929788 3558312077759238406280491 := by
  unfold tailWord_6929788
  simp only [CollatzResearch.WordTrace]
  refine ⟨126375066309284532205591009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168500088412379376274121345 126375066309284532205591009)
  ·
    refine ⟨94781299731963399154193257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126375066309284532205591009 94781299731963399154193257)
    ·
      refine ⟨71085974798972549365644943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94781299731963399154193257 71085974798972549365644943)
      ·
        refine ⟨106628962198458824048467415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71085974798972549365644943 106628962198458824048467415)
        ·
          refine ⟨159943443297688236072701123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106628962198458824048467415 159943443297688236072701123)
          ·
            refine ⟨239915164946532354109051685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159943443297688236072701123 239915164946532354109051685)
            ·
              refine ⟨44984093427474816395447191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239915164946532354109051685 44984093427474816395447191)
              ·
                refine ⟨67476140141212224593170787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44984093427474816395447191 67476140141212224593170787)
                ·
                  refine ⟨101214210211818336889756181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67476140141212224593170787 101214210211818336889756181)
                  ·
                    refine ⟨4744416103678984541707321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101214210211818336889756181 4744416103678984541707321)
                    ·
                      refine ⟨3558312077759238406280491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744416103678984541707321 3558312077759238406280491)
                      ·
                        rfl

theorem cell23_6929788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 6, 2].length) (baseStart_6929788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929788 prefixEnd_6929788 := by exact prefixLift 6929788
  have htrace : WordTrace (prefixWord ++ tailWord_6929788) baseStart_6929788 baseEnd_6929788 := by
    simpa [prefixWord, tailWord_6929788, baseEnd_6929788] using wordTrace_append hprefix tailTrace_6929788
  have hstable : (prefixWord ++ tailWord_6929788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929788).length < 2 ^ (prefixWord ++ tailWord_6929788).sum := by decide
  have hdescent : baseEnd_6929788 < baseStart_6929788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929815 : List Nat := [1, 1, 3, 3, 1, 1, 1, 7, 1, 4]
def baseStart_6929815 : Nat := 118140960795 + 6929815 * 2 ^ 59
def prefixEnd_6929815 : Nat := 4983230072969 + 3 ^ 40 * 6929815 * 2
def baseEnd_6929815 : Nat := 1186108647245636600214289

theorem tailTrace_6929815 : CollatzResearch.WordTrace tailWord_6929815 prefixEnd_6929815 1186108647245636600214289 := by
  unfold tailWord_6929815
  simp only [CollatzResearch.WordTrace]
  refine ⟨252751117389471248022414899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168500744926314165348276599 252751117389471248022414899)
  ·
    refine ⟨379126676084206872033622349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252751117389471248022414899 379126676084206872033622349)
    ·
      refine ⟨142172503531577577012608381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379126676084206872033622349 142172503531577577012608381)
      ·
        refine ⟨53314688824341591379728143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142172503531577577012608381 53314688824341591379728143)
        ·
          refine ⟨79972033236512387069592215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53314688824341591379728143 79972033236512387069592215)
          ·
            refine ⟨119958049854768580604388323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79972033236512387069592215 119958049854768580604388323)
            ·
              refine ⟨179937074782152870906582485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119958049854768580604388323 179937074782152870906582485)
              ·
                refine ⟨4217275190206707911873027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 179937074782152870906582485 4217275190206707911873027)
                ·
                  refine ⟨6325912785310061867809541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217275190206707911873027 6325912785310061867809541)
                  ·
                    refine ⟨1186108647245636600214289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6325912785310061867809541 1186108647245636600214289)
                    ·
                      rfl

theorem cell23_6929815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 1, 4].length) (baseStart_6929815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929815 prefixEnd_6929815 := by exact prefixLift 6929815
  have htrace : WordTrace (prefixWord ++ tailWord_6929815) baseStart_6929815 baseEnd_6929815 := by
    simpa [prefixWord, tailWord_6929815, baseEnd_6929815] using wordTrace_append hprefix tailTrace_6929815
  have hstable : (prefixWord ++ tailWord_6929815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929815).length < 2 ^ (prefixWord ++ tailWord_6929815).sum := by decide
  have hdescent : baseEnd_6929815 < baseStart_6929815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929905 : List Nat := [1, 2, 2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_6929905 : Nat := 118140960795 + 6929905 * 2 ^ 59
def prefixEnd_6929905 : Nat := 4983230072969 + 3 ^ 40 * 6929905 * 2
def baseEnd_6929905 : Nat := 1186124051665271482839151

theorem tailTrace_6929905 : CollatzResearch.WordTrace tailWord_6929905 prefixEnd_6929905 1186124051665271482839151 := by
  unfold tailWord_6929905
  simp only [CollatzResearch.WordTrace]
  refine ⟨252754399959145193393191169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168502933306096795595460779 252754399959145193393191169)
  ·
    refine ⟨189565799969358895044893377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252754399959145193393191169 189565799969358895044893377)
    ·
      refine ⟨142174349977019171283670033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189565799969358895044893377 142174349977019171283670033)
      ·
        refine ⟨106630762482764378462752525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142174349977019171283670033 106630762482764378462752525)
        ·
          refine ⟨39986535931036641923532197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106630762482764378462752525 39986535931036641923532197)
          ·
            refine ⟨7497475487069370360662287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39986535931036641923532197 7497475487069370360662287)
            ·
              refine ⟨11246213230604055540993431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497475487069370360662287 11246213230604055540993431)
              ·
                refine ⟨16869319845906083311490147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11246213230604055540993431 16869319845906083311490147)
                ·
                  refine ⟨25303979768859124967235221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16869319845906083311490147 25303979768859124967235221)
                  ·
                    refine ⟨1186124051665271482839151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25303979768859124967235221 1186124051665271482839151)
                    ·
                      rfl

theorem cell23_6929905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_6929905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929905 prefixEnd_6929905 := by exact prefixLift 6929905
  have htrace : WordTrace (prefixWord ++ tailWord_6929905) baseStart_6929905 baseEnd_6929905 := by
    simpa [prefixWord, tailWord_6929905, baseEnd_6929905] using wordTrace_append hprefix tailTrace_6929905
  have hstable : (prefixWord ++ tailWord_6929905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929905).length < 2 ^ (prefixWord ++ tailWord_6929905).sum := by decide
  have hdescent : baseEnd_6929905 < baseStart_6929905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929912 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2]
def baseStart_6929912 : Nat := 118140960795 + 6929912 * 2 ^ 59
def prefixEnd_6929912 : Nat := 4983230072969 + 3 ^ 40 * 6929912 * 2
def baseEnd_6929912 : Nat := 3558375749360395921129921

theorem tailTrace_6929912 : CollatzResearch.WordTrace tailWord_6929912 prefixEnd_6929912 3558375749360395921129921 := by
  unfold tailWord_6929912
  simp only [CollatzResearch.WordTrace]
  refine ⟨126377327635059916794347995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168503103513413222392463993 126377327635059916794347995)
  ·
    refine ⟨189565991452589875191521993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126377327635059916794347995 189565991452589875191521993)
    ·
      refine ⟨142174493589442406393641495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189565991452589875191521993 142174493589442406393641495)
      ·
        refine ⟨213261740384163609590462243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142174493589442406393641495 213261740384163609590462243)
        ·
          refine ⟨319892610576245414385693365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213261740384163609590462243 319892610576245414385693365)
          ·
            refine ⟨29989932241523007598658753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 319892610576245414385693365 29989932241523007598658753)
            ·
              refine ⟨22492449181142255698994065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29989932241523007598658753 22492449181142255698994065)
              ·
                refine ⟨16869336885856691774245549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22492449181142255698994065 16869336885856691774245549)
                ·
                  refine ⟨6326001332196259415342081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16869336885856691774245549 6326001332196259415342081)
                  ·
                    refine ⟨4744500999147194561506561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6326001332196259415342081 4744500999147194561506561)
                    ·
                      refine ⟨3558375749360395921129921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744500999147194561506561 3558375749360395921129921)
                      ·
                        rfl

theorem cell23_6929912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 2, 2].length) (baseStart_6929912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929912 prefixEnd_6929912 := by exact prefixLift 6929912
  have htrace : WordTrace (prefixWord ++ tailWord_6929912) baseStart_6929912 baseEnd_6929912 := by
    simpa [prefixWord, tailWord_6929912, baseEnd_6929912] using wordTrace_append hprefix tailTrace_6929912
  have hstable : (prefixWord ++ tailWord_6929912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929912).length < 2 ^ (prefixWord ++ tailWord_6929912).sum := by decide
  have hdescent : baseEnd_6929912 < baseStart_6929912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929922 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 4, 4]
def baseStart_6929922 : Nat := 118140960795 + 6929922 * 2 ^ 59
def prefixEnd_6929922 : Nat := 4983230072969 + 3 ^ 40 * 6929922 * 2
def baseEnd_6929922 : Nat := 1186126961388980294001625

theorem tailTrace_6929922 : CollatzResearch.WordTrace tailWord_6929922 prefixEnd_6929922 1186126961388980294001625 := by
  unfold tailWord_6929922
  simp only [CollatzResearch.WordTrace]
  refine ⟨63188755000020901324140005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168503346666722403531040013 63188755000020901324140005)
  ·
    refine ⟨11847891562503918998276251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63188755000020901324140005 11847891562503918998276251)
    ·
      refine ⟨17771837343755878497414377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11847891562503918998276251 17771837343755878497414377)
      ·
        refine ⟨13328878007816908873060783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17771837343755878497414377 13328878007816908873060783)
        ·
          refine ⟨19993317011725363309591175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13328878007816908873060783 19993317011725363309591175)
          ·
            refine ⟨29989975517588044964386763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19993317011725363309591175 29989975517588044964386763)
            ·
              refine ⟨44984963276382067446580145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29989975517588044964386763 44984963276382067446580145)
              ·
                refine ⟨33738722457286550584935109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44984963276382067446580145 33738722457286550584935109)
                ·
                  refine ⟨6326010460741228234675333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33738722457286550584935109 6326010460741228234675333)
                  ·
                    refine ⟨1186126961388980294001625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326010460741228234675333 1186126961388980294001625)
                    ·
                      rfl

theorem cell23_6929922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_6929922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929922 prefixEnd_6929922 := by exact prefixLift 6929922
  have htrace : WordTrace (prefixWord ++ tailWord_6929922) baseStart_6929922 baseEnd_6929922 := by
    simpa [prefixWord, tailWord_6929922, baseEnd_6929922] using wordTrace_append hprefix tailTrace_6929922
  have hstable : (prefixWord ++ tailWord_6929922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929922).length < 2 ^ (prefixWord ++ tailWord_6929922).sum := by decide
  have hdescent : baseEnd_6929922 < baseStart_6929922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929948 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6929948 : Nat := 118140960795 + 6929948 * 2 ^ 59
def prefixEnd_6929948 : Nat := 4983230072969 + 3 ^ 40 * 6929948 * 2
def baseEnd_6929948 : Nat := 1186131411554652593426585

theorem tailTrace_6929948 : CollatzResearch.WordTrace tailWord_6929948 prefixEnd_6929948 1186131411554652593426585 := by
  unfold tailWord_6929948
  simp only [CollatzResearch.WordTrace]
  refine ⟨126377984148994705868503249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168503978865326274491337665 126377984148994705868503249)
  ·
    refine ⟨94783488111746029401377437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126377984148994705868503249 94783488111746029401377437)
    ·
      refine ⟨35543808041904761025516539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94783488111746029401377437 35543808041904761025516539)
      ·
        refine ⟨53315712062857141538274809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35543808041904761025516539 53315712062857141538274809)
        ·
          refine ⟨39986784047142856153706107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53315712062857141538274809 39986784047142856153706107)
          ·
            refine ⟨59980176070714284230559161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39986784047142856153706107 59980176070714284230559161)
            ·
              refine ⟨44985132053035713172919371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59980176070714284230559161 44985132053035713172919371)
              ·
                refine ⟨67477698079553569759379057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44985132053035713172919371 67477698079553569759379057)
                ·
                  refine ⟨50608273559665177319534293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67477698079553569759379057 50608273559665177319534293)
                  ·
                    refine ⟨1186131411554652593426585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50608273559665177319534293 1186131411554652593426585)
                    ·
                      rfl

theorem cell23_6929948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6929948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929948 prefixEnd_6929948 := by exact prefixLift 6929948
  have htrace : WordTrace (prefixWord ++ tailWord_6929948) baseStart_6929948 baseEnd_6929948 := by
    simpa [prefixWord, tailWord_6929948, baseEnd_6929948] using wordTrace_append hprefix tailTrace_6929948
  have hstable : (prefixWord ++ tailWord_6929948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929948).length < 2 ^ (prefixWord ++ tailWord_6929948).sum := by decide
  have hdescent : baseEnd_6929948 < baseStart_6929948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929989 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 1, 3, 2]
def baseStart_6929989 : Nat := 118140960795 + 6929989 * 2 ^ 59
def prefixEnd_6929989 : Nat := 4983230072969 + 3 ^ 40 * 6929989 * 2
def baseEnd_6929989 : Nat := 3558415287370792119867067

theorem tailTrace_6929989 : CollatzResearch.WordTrace tailWord_6929989 prefixEnd_6929989 3558415287370792119867067 := by
  unfold tailWord_6929989
  simp only [CollatzResearch.WordTrace]
  refine ⟨252757463690840875739249021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168504975793893917159499347 252757463690840875739249021)
  ·
    refine ⟨94784048884065328402218383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252757463690840875739249021 94784048884065328402218383)
    ·
      refine ⟨142176073326097992603327575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94784048884065328402218383 142176073326097992603327575)
      ·
        refine ⟨213264109989146988904991363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142176073326097992603327575 213264109989146988904991363)
        ·
          refine ⟨319896164983720483357487045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213264109989146988904991363 319896164983720483357487045)
          ·
            refine ⟨59980530934447590629528821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319896164983720483357487045 59980530934447590629528821)
            ·
              refine ⟨5623174775104461621518327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59980530934447590629528821 5623174775104461621518327)
              ·
                refine ⟨8434762162656692432277491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623174775104461621518327 8434762162656692432277491)
                ·
                  refine ⟨12652143243985038648416237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8434762162656692432277491 12652143243985038648416237)
                  ·
                    refine ⟨4744553716494389493156089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12652143243985038648416237 4744553716494389493156089)
                    ·
                      refine ⟨3558415287370792119867067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744553716494389493156089 3558415287370792119867067)
                      ·
                        rfl

theorem cell23_6929989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 3, 2].length) (baseStart_6929989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929989 prefixEnd_6929989 := by exact prefixLift 6929989
  have htrace : WordTrace (prefixWord ++ tailWord_6929989) baseStart_6929989 baseEnd_6929989 := by
    simpa [prefixWord, tailWord_6929989, baseEnd_6929989] using wordTrace_append hprefix tailTrace_6929989
  have hstable : (prefixWord ++ tailWord_6929989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929989).length < 2 ^ (prefixWord ++ tailWord_6929989).sum := by decide
  have hdescent : baseEnd_6929989 < baseStart_6929989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929997 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_6929997 : Nat := 118140960795 + 6929997 * 2 ^ 59
def prefixEnd_6929997 : Nat := 4983230072969 + 3 ^ 40 * 6929997 * 2
def baseEnd_6929997 : Nat := 3558419395216028088567031

theorem tailTrace_6929997 : CollatzResearch.WordTrace tailWord_6929997 prefixEnd_6929997 3558419395216028088567031 := by
  unfold tailWord_6929997
  simp only [CollatzResearch.WordTrace]
  refine ⟨252757755474811893105540245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168505170316541262070360163 252757755474811893105540245)
  ·
    refine ⟨11848019787881807489322199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252757755474811893105540245 11848019787881807489322199)
    ·
      refine ⟨17772029681822711233983299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11848019787881807489322199 17772029681822711233983299)
      ·
        refine ⟨26658044522734066850974949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17772029681822711233983299 26658044522734066850974949)
        ·
          refine ⟨4998383348012637534557803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26658044522734066850974949 4998383348012637534557803)
          ·
            refine ⟨7497575022018956301836705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4998383348012637534557803 7497575022018956301836705)
            ·
              refine ⟨5623181266514217226377529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7497575022018956301836705 5623181266514217226377529)
              ·
                refine ⟨4217385949885662919783147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623181266514217226377529 4217385949885662919783147)
                ·
                  refine ⟨6326078924828494379674721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217385949885662919783147 6326078924828494379674721)
                  ·
                    refine ⟨4744559193621370784756041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6326078924828494379674721 4744559193621370784756041)
                    ·
                      refine ⟨3558419395216028088567031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744559193621370784756041 3558419395216028088567031)
                      ·
                        rfl

theorem cell23_6929997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_6929997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929997 prefixEnd_6929997 := by exact prefixLift 6929997
  have htrace : WordTrace (prefixWord ++ tailWord_6929997) baseStart_6929997 baseEnd_6929997 := by
    simpa [prefixWord, tailWord_6929997, baseEnd_6929997] using wordTrace_append hprefix tailTrace_6929997
  have hstable : (prefixWord ++ tailWord_6929997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929997).length < 2 ^ (prefixWord ++ tailWord_6929997).sum := by decide
  have hdescent : baseEnd_6929997 < baseStart_6929997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6929998 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6929998 : Nat := 118140960795 + 6929998 * 2 ^ 59
def prefixEnd_6929998 : Nat := 4983230072969 + 3 ^ 40 * 6929998 * 2
def baseEnd_6929998 : Nat := 3558419908696682584654525

theorem tailTrace_6929998 : CollatzResearch.WordTrace tailWord_6929998 prefixEnd_6929998 3558419908696682584654525 := by
  unfold tailWord_6929998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31594723993476033784540831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168505194631872180184217765 31594723993476033784540831)
  ·
    refine ⟨47392085990214050676811247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31594723993476033784540831 47392085990214050676811247)
    ·
      refine ⟨71088128985321076015216871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47392085990214050676811247 71088128985321076015216871)
      ·
        refine ⟨106632193477981614022825307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71088128985321076015216871 106632193477981614022825307)
        ·
          refine ⟨159948290216972421034237961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106632193477981614022825307 159948290216972421034237961)
          ·
            refine ⟨119961217662729315775678471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159948290216972421034237961 119961217662729315775678471)
            ·
              refine ⟨179941826494093973663517707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119961217662729315775678471 179941826494093973663517707)
              ·
                refine ⟨269912739741140960495276561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179941826494093973663517707 269912739741140960495276561)
                ·
                  refine ⟨202434554805855720371457421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 269912739741140960495276561 202434554805855720371457421)
                  ·
                    refine ⟨75912958052195895139296533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202434554805855720371457421 75912958052195895139296533)
                    ·
                      refine ⟨3558419908696682584654525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75912958052195895139296533 3558419908696682584654525)
                      ·
                        rfl

theorem cell23_6929998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6929998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6929998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6929998 prefixEnd_6929998 := by exact prefixLift 6929998
  have htrace : WordTrace (prefixWord ++ tailWord_6929998) baseStart_6929998 baseEnd_6929998 := by
    simpa [prefixWord, tailWord_6929998, baseEnd_6929998] using wordTrace_append hprefix tailTrace_6929998
  have hstable : (prefixWord ++ tailWord_6929998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6929998).length < 2 ^ (prefixWord ++ tailWord_6929998).sum := by decide
  have hdescent : baseEnd_6929998 < baseStart_6929998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6929998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930008 : List Nat := [2, 1, 2, 2, 1, 2, 1, 5, 7]
def baseStart_6930008 : Nat := 118140960795 + 6930008 * 2 ^ 59
def prefixEnd_6930008 : Nat := 4983230072969 + 3 ^ 40 * 6930008 * 2
def baseEnd_6930008 : Nat := 395380560389247505058831

theorem tailTrace_6930008 : CollatzResearch.WordTrace tailWord_6930008 prefixEnd_6930008 395380560389247505058831 := by
  unfold tailWord_6930008
  simp only [CollatzResearch.WordTrace]
  refine ⟨126379078338886020992095339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168505437785181361322793785 126379078338886020992095339)
  ·
    refine ⟨189568617508329031488143009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126379078338886020992095339 189568617508329031488143009)
    ·
      refine ⟨142176463131246773616107257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189568617508329031488143009 142176463131246773616107257)
      ·
        refine ⟨106632347348435080212080443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142176463131246773616107257 106632347348435080212080443)
        ·
          refine ⟨159948521022652620318120665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106632347348435080212080443 159948521022652620318120665)
          ·
            refine ⟨119961390766989465238590499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159948521022652620318120665 119961390766989465238590499)
            ·
              refine ⟨179942086150484197857885749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119961390766989465238590499 179942086150484197857885749)
              ·
                refine ⟨16869570576607893549176789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 179942086150484197857885749 16869570576607893549176789)
                ·
                  refine ⟨395380560389247505058831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16869570576607893549176789 395380560389247505058831)
                  ·
                    rfl

theorem cell23_6930008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 7].length) (baseStart_6930008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930008 prefixEnd_6930008 := by exact prefixLift 6930008
  have htrace : WordTrace (prefixWord ++ tailWord_6930008) baseStart_6930008 baseEnd_6930008 := by
    simpa [prefixWord, tailWord_6930008, baseEnd_6930008] using wordTrace_append hprefix tailTrace_6930008
  have hstable : (prefixWord ++ tailWord_6930008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930008).length < 2 ^ (prefixWord ++ tailWord_6930008).sum := by decide
  have hdescent : baseEnd_6930008 < baseStart_6930008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930019 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 2, 2, 2]
def baseStart_6930019 : Nat := 118140960795 + 6930019 * 2 ^ 59
def prefixEnd_6930019 : Nat := 4983230072969 + 3 ^ 40 * 6930019 * 2
def baseEnd_6930019 : Nat := 3558430691790427002491929

theorem tailTrace_6930019 : CollatzResearch.WordTrace tailWord_6930019 prefixEnd_6930019 3558430691790427002491929 := by
  unfold tailWord_6930019
  simp only [CollatzResearch.WordTrace]
  refine ⟨252758557880732190862841111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168505705253821460575227407 252758557880732190862841111)
  ·
    refine ⟨379137836821098286294261667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252758557880732190862841111 379137836821098286294261667)
    ·
      refine ⟨568706755231647429441392501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379137836821098286294261667 568706755231647429441392501)
      ·
        refine ⟨53316258302966946510130547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 568706755231647429441392501 53316258302966946510130547)
        ·
          refine ⟨79974387454450419765195821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53316258302966946510130547 79974387454450419765195821)
          ·
            refine ⟨29990395295418907411948433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79974387454450419765195821 29990395295418907411948433)
            ·
              refine ⟨22492796471564180558961325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29990395295418907411948433 22492796471564180558961325)
              ·
                refine ⟨8434798676836567709610497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22492796471564180558961325 8434798676836567709610497)
                ·
                  refine ⟨6326099007627425782207873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8434798676836567709610497 6326099007627425782207873)
                  ·
                    refine ⟨4744574255720569336655905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6326099007627425782207873 4744574255720569336655905)
                    ·
                      refine ⟨3558430691790427002491929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744574255720569336655905 3558430691790427002491929)
                      ·
                        rfl

theorem cell23_6930019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 2, 2].length) (baseStart_6930019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930019 prefixEnd_6930019 := by exact prefixLift 6930019
  have htrace : WordTrace (prefixWord ++ tailWord_6930019) baseStart_6930019 baseEnd_6930019 := by
    simpa [prefixWord, tailWord_6930019, baseEnd_6930019] using wordTrace_append hprefix tailTrace_6930019
  have hstable : (prefixWord ++ tailWord_6930019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930019).length < 2 ^ (prefixWord ++ tailWord_6930019).sum := by decide
  have hdescent : baseEnd_6930019 < baseStart_6930019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930095 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_6930095 : Nat := 118140960795 + 6930095 * 2 ^ 59
def prefixEnd_6930095 : Nat := 4983230072969 + 3 ^ 40 * 6930095 * 2
def baseEnd_6930095 : Nat := 3558469716320168705141579

theorem tailTrace_6930095 : CollatzResearch.WordTrace tailWord_6930095 prefixEnd_6930095 3558469716320168705141579 := by
  unfold tailWord_6930095
  simp only [CollatzResearch.WordTrace]
  refine ⟨252761329828456855842607739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168507553218971237228405159 252761329828456855842607739)
  ·
    refine ⟨379141994742685283763911609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252761329828456855842607739 379141994742685283763911609)
    ·
      refine ⟨284356496057013962822933707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379141994742685283763911609 284356496057013962822933707)
      ·
        refine ⟨426534744085520944234400561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284356496057013962822933707 426534744085520944234400561)
        ·
          refine ⟨319901058064140708175800421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426534744085520944234400561 319901058064140708175800421)
          ·
            refine ⟨59981448387026382782962579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319901058064140708175800421 59981448387026382782962579)
            ·
              refine ⟨89972172580539574174443869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59981448387026382782962579 89972172580539574174443869)
              ·
                refine ⟨33739564717702340315416451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89972172580539574174443869 33739564717702340315416451)
                ·
                  refine ⟨50609347076553510473124677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33739564717702340315416451 50609347076553510473124677)
                  ·
                    refine ⟨9489252576853783213710877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50609347076553510473124677 9489252576853783213710877)
                    ·
                      refine ⟨3558469716320168705141579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9489252576853783213710877 3558469716320168705141579)
                      ·
                        rfl

theorem cell23_6930095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_6930095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930095 prefixEnd_6930095 := by exact prefixLift 6930095
  have htrace : WordTrace (prefixWord ++ tailWord_6930095) baseStart_6930095 baseEnd_6930095 := by
    simpa [prefixWord, tailWord_6930095, baseEnd_6930095] using wordTrace_append hprefix tailTrace_6930095
  have hstable : (prefixWord ++ tailWord_6930095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930095).length < 2 ^ (prefixWord ++ tailWord_6930095).sum := by decide
  have hdescent : baseEnd_6930095 < baseStart_6930095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930112 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3]
def baseStart_6930112 : Nat := 118140960795 + 6930112 * 2 ^ 59
def prefixEnd_6930112 : Nat := 4983230072969 + 3 ^ 40 * 6930112 * 2
def baseEnd_6930112 : Nat := 3558478445491295138629001

theorem tailTrace_6930112 : CollatzResearch.WordTrace tailWord_6930112 prefixEnd_6930112 3558478445491295138629001 := by
  unfold tailWord_6930112
  simp only [CollatzResearch.WordTrace]
  refine ⟨126380974934697633872988295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168507966579596845163984393 126380974934697633872988295)
  ·
    refine ⟨189571462402046450809482443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126380974934697633872988295 189571462402046450809482443)
    ·
      refine ⟨284357193603069676214223665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189571462402046450809482443 284357193603069676214223665)
      ·
        refine ⟨213267895202302257160667749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284357193603069676214223665 213267895202302257160667749)
        ·
          refine ⟨39987730350431673217625203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213267895202302257160667749 39987730350431673217625203)
          ·
            refine ⟨59981595525647509826437805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39987730350431673217625203 59981595525647509826437805)
            ·
              refine ⟨22493098322117816184914177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59981595525647509826437805 22493098322117816184914177)
              ·
                refine ⟨16869823741588362138685633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22493098322117816184914177 16869823741588362138685633)
                ·
                  refine ⟨12652367806191271604014225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16869823741588362138685633 12652367806191271604014225)
                  ·
                    refine ⟨9489275854643453703010669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12652367806191271604014225 9489275854643453703010669)
                    ·
                      refine ⟨3558478445491295138629001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9489275854643453703010669 3558478445491295138629001)
                      ·
                        rfl

theorem cell23_6930112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_6930112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930112 prefixEnd_6930112 := by exact prefixLift 6930112
  have htrace : WordTrace (prefixWord ++ tailWord_6930112) baseStart_6930112 baseEnd_6930112 := by
    simpa [prefixWord, tailWord_6930112, baseEnd_6930112] using wordTrace_append hprefix tailTrace_6930112
  have hstable : (prefixWord ++ tailWord_6930112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930112).length < 2 ^ (prefixWord ++ tailWord_6930112).sum := by decide
  have hdescent : baseEnd_6930112 < baseStart_6930112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930185 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_6930185 : Nat := 118140960795 + 6930185 * 2 ^ 59
def prefixEnd_6930185 : Nat := 4983230072969 + 3 ^ 40 * 6930185 * 2
def baseEnd_6930185 : Nat := 3558515929579073353016165

theorem tailTrace_6930185 : CollatzResearch.WordTrace tailWord_6930185 prefixEnd_6930185 3558515929579073353016165 := by
  unfold tailWord_6930185
  simp only [CollatzResearch.WordTrace]
  refine ⟨252764612398130801213384009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168509741598753867475589339 252764612398130801213384009)
  ·
    refine ⟨189573459298598100910038007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252764612398130801213384009 189573459298598100910038007)
    ·
      refine ⟨284360188947897151365057011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189573459298598100910038007 284360188947897151365057011)
      ·
        refine ⟨426540283421845727047585517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284360188947897151365057011 426540283421845727047585517)
        ·
          refine ⟨159952606283192147642844569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426540283421845727047585517 159952606283192147642844569)
          ·
            refine ⟨119964454712394110732133427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159952606283192147642844569 119964454712394110732133427)
            ·
              refine ⟨179946682068591166098200141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119964454712394110732133427 179946682068591166098200141)
              ·
                refine ⟨67480005775721687286825053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179946682068591166098200141 67480005775721687286825053)
                ·
                  refine ⟨25305002165895632732559395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67480005775721687286825053 25305002165895632732559395)
                  ·
                    refine ⟨37957503248843449098839093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25305002165895632732559395 37957503248843449098839093)
                    ·
                      refine ⟨3558515929579073353016165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37957503248843449098839093 3558515929579073353016165)
                      ·
                        rfl

theorem cell23_6930185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_6930185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930185 prefixEnd_6930185 := by exact prefixLift 6930185
  have htrace : WordTrace (prefixWord ++ tailWord_6930185) baseStart_6930185 baseEnd_6930185 := by
    simpa [prefixWord, tailWord_6930185, baseEnd_6930185] using wordTrace_append hprefix tailTrace_6930185
  have hstable : (prefixWord ++ tailWord_6930185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930185).length < 2 ^ (prefixWord ++ tailWord_6930185).sum := by decide
  have hdescent : baseEnd_6930185 < baseStart_6930185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930216 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4]
def baseStart_6930216 : Nat := 118140960795 + 6930216 * 2 ^ 59
def prefixEnd_6930216 : Nat := 4983230072969 + 3 ^ 40 * 6930216 * 2
def baseEnd_6930216 : Nat := 3558531847479362731728523

theorem tailTrace_6930216 : CollatzResearch.WordTrace tailWord_6930216 prefixEnd_6930216 3558531847479362731728523 := by
  unfold tailWord_6930216
  simp only [CollatzResearch.WordTrace]
  refine ⟨126382871530509246753881251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168510495374012329005175001 126382871530509246753881251)
  ·
    refine ⟨189574307295763870130821877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126382871530509246753881251 189574307295763870130821877)
    ·
      refine ⟨17772591308977862824764551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 189574307295763870130821877 17772591308977862824764551)
      ·
        refine ⟨26658886963466794237146827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17772591308977862824764551 26658886963466794237146827)
        ·
          refine ⟨39988330445200191355720241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26658886963466794237146827 39988330445200191355720241)
          ·
            refine ⟨29991247833900143516790181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39988330445200191355720241 29991247833900143516790181)
            ·
              refine ⟨5623358968856276909398159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29991247833900143516790181 5623358968856276909398159)
              ·
                refine ⟨8435038453284415364097239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623358968856276909398159 8435038453284415364097239)
                ·
                  refine ⟨12652557679926623046145859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435038453284415364097239 12652557679926623046145859)
                  ·
                    refine ⟨18978836519889934569218789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12652557679926623046145859 18978836519889934569218789)
                    ·
                      refine ⟨3558531847479362731728523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18978836519889934569218789 3558531847479362731728523)
                      ·
                        rfl

theorem cell23_6930216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_6930216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930216 prefixEnd_6930216 := by exact prefixLift 6930216
  have htrace : WordTrace (prefixWord ++ tailWord_6930216) baseStart_6930216 baseEnd_6930216 := by
    simpa [prefixWord, tailWord_6930216, baseEnd_6930216] using wordTrace_append hprefix tailTrace_6930216
  have hstable : (prefixWord ++ tailWord_6930216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930216).length < 2 ^ (prefixWord ++ tailWord_6930216).sum := by decide
  have hdescent : baseEnd_6930216 < baseStart_6930216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930226 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 2, 4]
def baseStart_6930226 : Nat := 118140960795 + 6930226 * 2 ^ 59
def prefixEnd_6930226 : Nat := 4983230072969 + 3 ^ 40 * 6930226 * 2
def baseEnd_6930226 : Nat := 1186178994095302564201159

theorem tailTrace_6930226 : CollatzResearch.WordTrace tailWord_6930226 prefixEnd_6930226 1186178994095302564201159 := by
  unfold tailWord_6930226
  simp only [CollatzResearch.WordTrace]
  refine ⟨63191526947745566303906633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168510738527321510143751021 63191526947745566303906633)
  ·
    refine ⟨47393645210809174727929975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63191526947745566303906633 47393645210809174727929975)
    ·
      refine ⟨71090467816213762091894963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47393645210809174727929975 71090467816213762091894963)
      ·
        refine ⟨106635701724320643137842445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71090467816213762091894963 106635701724320643137842445)
        ·
          refine ⟨39988388146620241176690917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106635701724320643137842445 39988388146620241176690917)
          ·
            refine ⟨7497822777491295220629547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39988388146620241176690917 7497822777491295220629547)
            ·
              refine ⟨11246734166236942830944321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497822777491295220629547 11246734166236942830944321)
              ·
                refine ⟨8435050624677707123208241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11246734166236942830944321 8435050624677707123208241)
                ·
                  refine ⟨6326287968508280342406181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8435050624677707123208241 6326287968508280342406181)
                  ·
                    refine ⟨1186178994095302564201159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326287968508280342406181 1186178994095302564201159)
                    ·
                      rfl

theorem cell23_6930226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 2, 4].length) (baseStart_6930226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930226 prefixEnd_6930226 := by exact prefixLift 6930226
  have htrace : WordTrace (prefixWord ++ tailWord_6930226) baseStart_6930226 baseEnd_6930226 := by
    simpa [prefixWord, tailWord_6930226, baseEnd_6930226] using wordTrace_append hprefix tailTrace_6930226
  have hstable : (prefixWord ++ tailWord_6930226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930226).length < 2 ^ (prefixWord ++ tailWord_6930226).sum := by decide
  have hdescent : baseEnd_6930226 < baseStart_6930226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930246 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_6930246 : Nat := 118140960795 + 6930246 * 2 ^ 59
def prefixEnd_6930246 : Nat := 4983230072969 + 3 ^ 40 * 6930246 * 2
def baseEnd_6930246 : Nat := 3558547251898997614353385

theorem tailTrace_6930246 : CollatzResearch.WordTrace tailWord_6930246 prefixEnd_6930246 3558547251898997614353385 := by
  unfold tailWord_6930246
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898963664090931519729831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168511224833939872420903061 7898963664090931519729831)
  ·
    refine ⟨11848445496136397279594747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7898963664090931519729831 11848445496136397279594747)
    ·
      refine ⟨17772668244204595919392121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11848445496136397279594747 17772668244204595919392121)
      ·
        refine ⟨13329501183153446939544091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17772668244204595919392121 13329501183153446939544091)
        ·
          refine ⟨19994251774730170409316137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13329501183153446939544091 19994251774730170409316137)
          ·
            refine ⟨14995688831047627806987103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19994251774730170409316137 14995688831047627806987103)
            ·
              refine ⟨22493533246571441710480655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14995688831047627806987103 22493533246571441710480655)
              ·
                refine ⟨33740299869857162565720983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22493533246571441710480655 33740299869857162565720983)
                ·
                  refine ⟨50610449804785743848581475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33740299869857162565720983 50610449804785743848581475)
                  ·
                    refine ⟨75915674707178615772872213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50610449804785743848581475 75915674707178615772872213)
                    ·
                      refine ⟨3558547251898997614353385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75915674707178615772872213 3558547251898997614353385)
                      ·
                        rfl

theorem cell23_6930246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_6930246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930246 prefixEnd_6930246 := by exact prefixLift 6930246
  have htrace : WordTrace (prefixWord ++ tailWord_6930246) baseStart_6930246 baseEnd_6930246 := by
    simpa [prefixWord, tailWord_6930246, baseEnd_6930246] using wordTrace_append hprefix tailTrace_6930246
  have hstable : (prefixWord ++ tailWord_6930246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930246).length < 2 ^ (prefixWord ++ tailWord_6930246).sum := by decide
  have hdescent : baseEnd_6930246 < baseStart_6930246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930253 : List Nat := [1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6930253 : Nat := 118140960795 + 6930253 * 2 ^ 59
def prefixEnd_6930253 : Nat := 4983230072969 + 3 ^ 40 * 6930253 * 2
def baseEnd_6930253 : Nat := 3558550846263579086965853

theorem tailTrace_6930253 : CollatzResearch.WordTrace tailWord_6930253 prefixEnd_6930253 3558550846263579086965853 := by
  unfold tailWord_6930253
  simp only [CollatzResearch.WordTrace]
  refine ⟨252767092561884448826859413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168511395041256299217906275 252767092561884448826859413)
  ·
    refine ⟨11848457463838333538759035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 252767092561884448826859413 11848457463838333538759035)
    ·
      refine ⟨17772686195757500308138553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11848457463838333538759035 17772686195757500308138553)
      ·
        refine ⟨13329514646818125231103915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17772686195757500308138553 13329514646818125231103915)
        ·
          refine ⟨19994271970227187846655873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13329514646818125231103915 19994271970227187846655873)
          ·
            refine ⟨14995703977670390884991905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19994271970227187846655873 14995703977670390884991905)
            ·
              refine ⟨11246777983252793163743929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14995703977670390884991905 11246777983252793163743929)
              ·
                refine ⟨8435083487439594872807947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11246777983252793163743929 8435083487439594872807947)
                ·
                  refine ⟨12652625231159392309211921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435083487439594872807947 12652625231159392309211921)
                  ·
                    refine ⟨9489468923369544231908941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12652625231159392309211921 9489468923369544231908941)
                    ·
                      refine ⟨3558550846263579086965853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9489468923369544231908941 3558550846263579086965853)
                      ·
                        rfl

theorem cell23_6930253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6930253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930253 prefixEnd_6930253 := by exact prefixLift 6930253
  have htrace : WordTrace (prefixWord ++ tailWord_6930253) baseStart_6930253 baseEnd_6930253 := by
    simpa [prefixWord, tailWord_6930253, baseEnd_6930253] using wordTrace_append hprefix tailTrace_6930253
  have hstable : (prefixWord ++ tailWord_6930253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930253).length < 2 ^ (prefixWord ++ tailWord_6930253).sum := by decide
  have hdescent : baseEnd_6930253 < baseStart_6930253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930376 : List Nat := [2, 1, 3, 1, 4, 3, 1, 1, 2, 5]
def baseStart_6930376 : Nat := 118140960795 + 6930376 * 2 ^ 59
def prefixEnd_6930376 : Nat := 4983230072969 + 3 ^ 40 * 6930376 * 2
def baseEnd_6930376 : Nat := 1186204668128027368575929

theorem tailTrace_6930376 : CollatzResearch.WordTrace tailWord_6930376 prefixEnd_6930376 1186204668128027368575929 := by
  unfold tailWord_6930376
  simp only [CollatzResearch.WordTrace]
  refine ⟨126385789370219420416793491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168514385826959227222391321 126385789370219420416793491)
  ·
    refine ⟨189578684055329130625190237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126385789370219420416793491 189578684055329130625190237)
    ·
      refine ⟨71092006520748423984446339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189578684055329130625190237 71092006520748423984446339)
      ·
        refine ⟨106638009781122635976669509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71092006520748423984446339 106638009781122635976669509)
        ·
          refine ⟨19994626833960494245625533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106638009781122635976669509 19994626833960494245625533)
          ·
            refine ⟨7497985062735185342109575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19994626833960494245625533 7497985062735185342109575)
            ·
              refine ⟨11246977594102778013164363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7497985062735185342109575 11246977594102778013164363)
              ·
                refine ⟨16870466391154167019746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11246977594102778013164363 16870466391154167019746545)
                ·
                  refine ⟨12652849793365625264809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16870466391154167019746545 12652849793365625264809909)
                  ·
                    refine ⟨1186204668128027368575929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12652849793365625264809909 1186204668128027368575929)
                    ·
                      rfl

theorem cell23_6930376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_6930376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930376 prefixEnd_6930376 := by exact prefixLift 6930376
  have htrace : WordTrace (prefixWord ++ tailWord_6930376) baseStart_6930376 baseEnd_6930376 := by
    simpa [prefixWord, tailWord_6930376, baseEnd_6930376] using wordTrace_append hprefix tailTrace_6930376
  have hstable : (prefixWord ++ tailWord_6930376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930376).length < 2 ^ (prefixWord ++ tailWord_6930376).sum := by decide
  have hdescent : baseEnd_6930376 < baseStart_6930376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930379 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 6, 2]
def baseStart_6930379 : Nat := 118140960795 + 6930379 * 2 ^ 59
def prefixEnd_6930379 : Nat := 4983230072969 + 3 ^ 40 * 6930379 * 2
def baseEnd_6930379 : Nat := 3558615544826045593990273

theorem tailTrace_6930379 : CollatzResearch.WordTrace tailWord_6930379 prefixEnd_6930379 3558615544826045593990273 := by
  unfold tailWord_6930379
  simp only [CollatzResearch.WordTrace]
  refine ⟨252771688159427972345946191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168514458772951981563964127 252771688159427972345946191)
  ·
    refine ⟨379157532239141958518919287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252771688159427972345946191 379157532239141958518919287)
    ·
      refine ⟨568736298358712937778378931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379157532239141958518919287 568736298358712937778378931)
      ·
        refine ⟨853104447538069406667568397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568736298358712937778378931 853104447538069406667568397)
        ·
          refine ⟨319914167826776027500338149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853104447538069406667568397 319914167826776027500338149)
          ·
            refine ⟨59983906467520505156313403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 319914167826776027500338149 59983906467520505156313403)
            ·
              refine ⟨89975859701280757734470105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59983906467520505156313403 89975859701280757734470105)
              ·
                refine ⟨67481894775960568300852579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89975859701280757734470105 67481894775960568300852579)
                ·
                  refine ⟨101222842163940852451278869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67481894775960568300852579 101222842163940852451278869)
                  ·
                    refine ⟨4744820726434727458653697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101222842163940852451278869 4744820726434727458653697)
                    ·
                      refine ⟨3558615544826045593990273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4744820726434727458653697 3558615544826045593990273)
                      ·
                        rfl

theorem cell23_6930379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 6, 2].length) (baseStart_6930379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930379 prefixEnd_6930379 := by exact prefixLift 6930379
  have htrace : WordTrace (prefixWord ++ tailWord_6930379) baseStart_6930379 baseEnd_6930379 := by
    simpa [prefixWord, tailWord_6930379, baseEnd_6930379] using wordTrace_append hprefix tailTrace_6930379
  have hstable : (prefixWord ++ tailWord_6930379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930379).length < 2 ^ (prefixWord ++ tailWord_6930379).sum := by decide
  have hdescent : baseEnd_6930379 < baseStart_6930379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930392 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_6930392 : Nat := 118140960795 + 6930392 * 2 ^ 59
def prefixEnd_6930392 : Nat := 4983230072969 + 3 ^ 40 * 6930392 * 2
def baseEnd_6930392 : Nat := 3558622220074554043127713

theorem tailTrace_6930392 : CollatzResearch.WordTrace tailWord_6930392 prefixEnd_6930392 3558622220074554043127713 := by
  unfold tailWord_6930392
  simp only [CollatzResearch.WordTrace]
  refine ⟨126386081154190437783084715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168514774872253917044112953 126386081154190437783084715)
  ·
    refine ⟨189579121731285656674627073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126386081154190437783084715 189579121731285656674627073)
    ·
      refine ⟨142184341298464242505970305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189579121731285656674627073 142184341298464242505970305)
      ·
        refine ⟨106638255973848181879477729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142184341298464242505970305 106638255973848181879477729)
        ·
          refine ⟨79978691980386136409608297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106638255973848181879477729 79978691980386136409608297)
          ·
            refine ⟨59984018985289602307206223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79978691980386136409608297 59984018985289602307206223)
            ·
              refine ⟨89976028477934403460809335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59984018985289602307206223 89976028477934403460809335)
              ·
                refine ⟨134964042716901605191214003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89976028477934403460809335 134964042716901605191214003)
                ·
                  refine ⟨202446064075352407786821005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134964042716901605191214003 202446064075352407786821005)
                  ·
                    refine ⟨75917274028257152920057877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202446064075352407786821005 75917274028257152920057877)
                    ·
                      refine ⟨3558622220074554043127713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75917274028257152920057877 3558622220074554043127713)
                      ·
                        rfl

theorem cell23_6930392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_6930392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930392 prefixEnd_6930392 := by exact prefixLift 6930392
  have htrace : WordTrace (prefixWord ++ tailWord_6930392) baseStart_6930392 baseEnd_6930392 := by
    simpa [prefixWord, tailWord_6930392, baseEnd_6930392] using wordTrace_append hprefix tailTrace_6930392
  have hstable : (prefixWord ++ tailWord_6930392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930392).length < 2 ^ (prefixWord ++ tailWord_6930392).sum := by decide
  have hdescent : baseEnd_6930392 < baseStart_6930392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930479 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 6, 4]
def baseStart_6930479 : Nat := 118140960795 + 6930479 * 2 ^ 59
def prefixEnd_6930479 : Nat := 4983230072969 + 3 ^ 40 * 6930479 * 2
def baseEnd_6930479 : Nat := 1186222297630498400913271

theorem tailTrace_6930479 : CollatzResearch.WordTrace tailWord_6930479 prefixEnd_6930479 1186222297630498400913271 := by
  unfold tailWord_6930479
  simp only [CollatzResearch.WordTrace]
  refine ⟨252775335459065689424586491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168516890306043792949724327 252775335459065689424586491)
  ·
    refine ⟨379163003188598534136879737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252775335459065689424586491 379163003188598534136879737)
    ·
      refine ⟨284372252391448900602659803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379163003188598534136879737 284372252391448900602659803)
      ·
        refine ⟨426558378587173350903989705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284372252391448900602659803 426558378587173350903989705)
        ·
          refine ⟨319918783940380013177992279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426558378587173350903989705 319918783940380013177992279)
          ·
            refine ⟨479878175910570019766988419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319918783940380013177992279 479878175910570019766988419)
            ·
              refine ⟨719817263865855029650482629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479878175910570019766988419 719817263865855029650482629)
              ·
                refine ⟨134965736974847818059465493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 719817263865855029650482629 134965736974847818059465493)
                ·
                  refine ⟨6326518920695991471537445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134965736974847818059465493 6326518920695991471537445)
                  ·
                    refine ⟨1186222297630498400913271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326518920695991471537445 1186222297630498400913271)
                    ·
                      rfl

theorem cell23_6930479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 6, 4].length) (baseStart_6930479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930479 prefixEnd_6930479 := by exact prefixLift 6930479
  have htrace : WordTrace (prefixWord ++ tailWord_6930479) baseStart_6930479 baseEnd_6930479 := by
    simpa [prefixWord, tailWord_6930479, baseEnd_6930479] using wordTrace_append hprefix tailTrace_6930479
  have hstable : (prefixWord ++ tailWord_6930479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930479).length < 2 ^ (prefixWord ++ tailWord_6930479).sum := by decide
  have hdescent : baseEnd_6930479 < baseStart_6930479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930503 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 1, 1, 4]
def baseStart_6930503 : Nat := 118140960795 + 6930503 * 2 ^ 59
def prefixEnd_6930503 : Nat := 4983230072969 + 3 ^ 40 * 6930503 * 2
def baseEnd_6930503 : Nat := 3558679216427203108839703

theorem tailTrace_6930503 : CollatzResearch.WordTrace tailWord_6930503 prefixEnd_6930503 3558679216427203108839703 := by
  unfold tailWord_6930503
  simp only [CollatzResearch.WordTrace]
  refine ⟨252776210810978741523460163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168517473873985827682306775 252776210810978741523460163)
  ·
    refine ⟨379164316216468112285190245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252776210810978741523460163 379164316216468112285190245)
    ·
      refine ⟨71093309290587771053473171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379164316216468112285190245 71093309290587771053473171)
      ·
        refine ⟨106639963935881656580209757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71093309290587771053473171 106639963935881656580209757)
        ·
          refine ⟨39989986475955621217578659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106639963935881656580209757 39989986475955621217578659)
          ·
            refine ⟨59984979713933431826367989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39989986475955621217578659 59984979713933431826367989)
            ·
              refine ⟨5623591848181259233721999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59984979713933431826367989 5623591848181259233721999)
              ·
                refine ⟨8435387772271888850582999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623591848181259233721999 8435387772271888850582999)
                ·
                  refine ⟨12653081658407833275874499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435387772271888850582999 12653081658407833275874499)
                  ·
                    refine ⟨18979622487611749913811749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12653081658407833275874499 18979622487611749913811749)
                    ·
                      refine ⟨3558679216427203108839703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18979622487611749913811749 3558679216427203108839703)
                      ·
                        rfl

theorem cell23_6930503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_6930503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930503 prefixEnd_6930503 := by exact prefixLift 6930503
  have htrace : WordTrace (prefixWord ++ tailWord_6930503) baseStart_6930503 baseEnd_6930503 := by
    simpa [prefixWord, tailWord_6930503, baseEnd_6930503] using wordTrace_append hprefix tailTrace_6930503
  have hstable : (prefixWord ++ tailWord_6930503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930503).length < 2 ^ (prefixWord ++ tailWord_6930503).sum := by decide
  have hdescent : baseEnd_6930503 < baseStart_6930503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930514 : List Nat := [3, 2, 2, 1, 4, 2, 2, 2, 1, 1, 3]
def baseStart_6930514 : Nat := 118140960795 + 6930514 * 2 ^ 59
def prefixEnd_6930514 : Nat := 4983230072969 + 3 ^ 40 * 6930514 * 2
def baseEnd_6930514 : Nat := 3558684864714402565802153

theorem tailTrace_6930514 : CollatzResearch.WordTrace tailWord_6930514 prefixEnd_6930514 3558684864714402565802153 := by
  unfold tailWord_6930514
  simp only [CollatzResearch.WordTrace]
  refine ⟨63194153003484722600527649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168517741342625926934740397 63194153003484722600527649)
  ·
    refine ⟨47395614752613541950395737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63194153003484722600527649 47395614752613541950395737)
    ·
      refine ⟨35546711064460156462796803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47395614752613541950395737 35546711064460156462796803)
      ·
        refine ⟨53320066596690234694195205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35546711064460156462796803 53320066596690234694195205)
        ·
          refine ⟨9997512486879419005161601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53320066596690234694195205 9997512486879419005161601)
          ·
            refine ⟨7498134365159564253871201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9997512486879419005161601 7498134365159564253871201)
            ·
              refine ⟨5623600773869673190403401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498134365159564253871201 5623600773869673190403401)
              ·
                refine ⟨4217700580402254892802551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5623600773869673190403401 4217700580402254892802551)
                ·
                  refine ⟨6326550870603382339203827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4217700580402254892802551 6326550870603382339203827)
                  ·
                    refine ⟨9489826305905073508805741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6326550870603382339203827 9489826305905073508805741)
                    ·
                      refine ⟨3558684864714402565802153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9489826305905073508805741 3558684864714402565802153)
                      ·
                        rfl

theorem cell23_6930514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_6930514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930514 prefixEnd_6930514 := by exact prefixLift 6930514
  have htrace : WordTrace (prefixWord ++ tailWord_6930514) baseStart_6930514 baseEnd_6930514 := by
    simpa [prefixWord, tailWord_6930514, baseEnd_6930514] using wordTrace_append hprefix tailTrace_6930514
  have hstable : (prefixWord ++ tailWord_6930514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930514).length < 2 ^ (prefixWord ++ tailWord_6930514).sum := by decide
  have hdescent : baseEnd_6930514 < baseStart_6930514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930569 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_6930569 : Nat := 118140960795 + 6930569 * 2 ^ 59
def prefixEnd_6930569 : Nat := 4983230072969 + 3 ^ 40 * 6930569 * 2
def baseEnd_6930569 : Nat := 1186237702050133283538133

theorem tailTrace_6930569 : CollatzResearch.WordTrace tailWord_6930569 prefixEnd_6930569 1186237702050133283538133 := by
  unfold tailWord_6930569
  simp only [CollatzResearch.WordTrace]
  refine ⟨252778618028739634795362761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168519078685826423196908507 252778618028739634795362761)
  ·
    refine ⟨189583963521554726096522071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252778618028739634795362761 189583963521554726096522071)
    ·
      refine ⟨284375945282332089144783107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189583963521554726096522071 284375945282332089144783107)
      ·
        refine ⟨426563917923498133717174661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284375945282332089144783107 426563917923498133717174661)
        ·
          refine ⟨79980734610655900071970249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 426563917923498133717174661 79980734610655900071970249)
          ·
            refine ⟨59985550957991925053977687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79980734610655900071970249 59985550957991925053977687)
            ·
              refine ⟨89978326436987887580966531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59985550957991925053977687 89978326436987887580966531)
              ·
                refine ⟨134967489655481831371449797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89978326436987887580966531 134967489655481831371449797)
                ·
                  refine ⟨25306404310402843382146837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134967489655481831371449797 25306404310402843382146837)
                  ·
                    refine ⟨1186237702050133283538133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25306404310402843382146837 1186237702050133283538133)
                    ·
                      rfl

theorem cell23_6930569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_6930569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930569 prefixEnd_6930569 := by exact prefixLift 6930569
  have htrace : WordTrace (prefixWord ++ tailWord_6930569) baseStart_6930569 baseEnd_6930569 := by
    simpa [prefixWord, tailWord_6930569, baseEnd_6930569] using wordTrace_append hprefix tailTrace_6930569
  have hstable : (prefixWord ++ tailWord_6930569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930569).length < 2 ^ (prefixWord ++ tailWord_6930569).sum := by decide
  have hdescent : baseEnd_6930569 < baseStart_6930569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930570 : List Nat := [3, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3]
def baseStart_6930570 : Nat := 118140960795 + 6930570 * 2 ^ 59
def prefixEnd_6930570 : Nat := 4983230072969 + 3 ^ 40 * 6930570 * 2
def baseEnd_6930570 : Nat := 3558713619631054346701895

theorem tailTrace_6930570 : CollatzResearch.WordTrace tailWord_6930570 prefixEnd_6930570 3558713619631054346701895 := by
  unfold tailWord_6930570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63194663625434002991537291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168519103001157341310766109 63194663625434002991537291)
  ·
    refine ⟨94791995438151004487305937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63194663625434002991537291 94791995438151004487305937)
    ·
      refine ⟨71093996578613253365479453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94791995438151004487305937 71093996578613253365479453)
      ·
        refine ⟨26660248716979970012054795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71093996578613253365479453 26660248716979970012054795)
        ·
          refine ⟨39990373075469955018082193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26660248716979970012054795 39990373075469955018082193)
          ·
            refine ⟨29992779806602466263561645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39990373075469955018082193 29992779806602466263561645)
            ·
              refine ⟨11247292427475924848835617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29992779806602466263561645 11247292427475924848835617)
              ·
                refine ⟨8435469320606943636626713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11247292427475924848835617 8435469320606943636626713)
                ·
                  refine ⟨6326601990455207727470035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8435469320606943636626713 6326601990455207727470035)
                  ·
                    refine ⟨9489902985682811591205053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6326601990455207727470035 9489902985682811591205053)
                    ·
                      refine ⟨3558713619631054346701895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9489902985682811591205053 3558713619631054346701895)
                      ·
                        rfl

theorem cell23_6930570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_6930570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930570 prefixEnd_6930570 := by exact prefixLift 6930570
  have htrace : WordTrace (prefixWord ++ tailWord_6930570) baseStart_6930570 baseEnd_6930570 := by
    simpa [prefixWord, tailWord_6930570, baseEnd_6930570] using wordTrace_append hprefix tailTrace_6930570
  have hstable : (prefixWord ++ tailWord_6930570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930570).length < 2 ^ (prefixWord ++ tailWord_6930570).sum := by decide
  have hdescent : baseEnd_6930570 < baseStart_6930570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930579 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_6930579 : Nat := 118140960795 + 6930579 * 2 ^ 59
def prefixEnd_6930579 : Nat := 4983230072969 + 3 ^ 40 * 6930579 * 2
def baseEnd_6930579 : Nat := 3558718240956944811489353

theorem tailTrace_6930579 : CollatzResearch.WordTrace tailWord_6930579 prefixEnd_6930579 3558718240956944811489353 := by
  unfold tailWord_6930579
  simp only [CollatzResearch.WordTrace]
  refine ⟨252778982758703406503226791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168519321839135604335484527 252778982758703406503226791)
  ·
    refine ⟨379168474138055109754840187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252778982758703406503226791 379168474138055109754840187)
    ·
      refine ⟨568752711207082664632260281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379168474138055109754840187 568752711207082664632260281)
      ·
        refine ⟨426564533405311998474195211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568752711207082664632260281 426564533405311998474195211)
        ·
          refine ⟨639846800107967997711292817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426564533405311998474195211 639846800107967997711292817)
          ·
            refine ⟨479885100080975998283469613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 639846800107967997711292817 479885100080975998283469613)
            ·
              refine ⟨179956912530365999356301105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479885100080975998283469613 179956912530365999356301105)
              ·
                refine ⟨134967684397774499517225829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179956912530365999356301105 134967684397774499517225829)
                ·
                  refine ⟨25306440824582718659479843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134967684397774499517225829 25306440824582718659479843)
                  ·
                    refine ⟨37959661236874077989219765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25306440824582718659479843 37959661236874077989219765)
                    ·
                      refine ⟨3558718240956944811489353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37959661236874077989219765 3558718240956944811489353)
                      ·
                        rfl

theorem cell23_6930579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_6930579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930579 prefixEnd_6930579 := by exact prefixLift 6930579
  have htrace : WordTrace (prefixWord ++ tailWord_6930579) baseStart_6930579 baseEnd_6930579 := by
    simpa [prefixWord, tailWord_6930579, baseEnd_6930579] using wordTrace_append hprefix tailTrace_6930579
  have hstable : (prefixWord ++ tailWord_6930579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930579).length < 2 ^ (prefixWord ++ tailWord_6930579).sum := by decide
  have hdescent : baseEnd_6930579 < baseStart_6930579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930663 : List Nat := [1, 1, 5, 3, 1, 1, 1, 3, 2, 5]
def baseStart_6930663 : Nat := 118140960795 + 6930663 * 2 ^ 59
def prefixEnd_6930663 : Nat := 4983230072969 + 3 ^ 40 * 6930663 * 2
def baseEnd_6930663 : Nat := 1186253791110640827612989

theorem tailTrace_6930663 : CollatzResearch.WordTrace tailWord_6930663 prefixEnd_6930663 1186253791110640827612989 := by
  unfold tailWord_6930663
  simp only [CollatzResearch.WordTrace]
  refine ⟨252782046490399088849284643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168521364326932725899523095 252782046490399088849284643)
  ·
    refine ⟨379173069735598633273926965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252782046490399088849284643 379173069735598633273926965)
    ·
      refine ⟨35547475287712371869430653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379173069735598633273926965 35547475287712371869430653)
      ·
        refine ⟨13330303232892139451036495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35547475287712371869430653 13330303232892139451036495)
        ·
          refine ⟨19995454849338209176554743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330303232892139451036495 19995454849338209176554743)
          ·
            refine ⟨29993182274007313764832115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19995454849338209176554743 29993182274007313764832115)
            ·
              refine ⟨44989773411010970647248173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29993182274007313764832115 44989773411010970647248173)
              ·
                refine ⟨16871165029129113992718065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44989773411010970647248173 16871165029129113992718065)
                ·
                  refine ⟨12653373771846835494538549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16871165029129113992718065 12653373771846835494538549)
                  ·
                    refine ⟨1186253791110640827612989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12653373771846835494538549 1186253791110640827612989)
                    ·
                      rfl

theorem cell23_6930663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_6930663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930663 prefixEnd_6930663 := by exact prefixLift 6930663
  have htrace : WordTrace (prefixWord ++ tailWord_6930663) baseStart_6930663 baseEnd_6930663 := by
    simpa [prefixWord, tailWord_6930663, baseEnd_6930663] using wordTrace_append hprefix tailTrace_6930663
  have hstable : (prefixWord ++ tailWord_6930663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930663).length < 2 ^ (prefixWord ++ tailWord_6930663).sum := by decide
  have hdescent : baseEnd_6930663 < baseStart_6930663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930717 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_6930717 : Nat := 118140960795 + 6930717 * 2 ^ 59
def prefixEnd_6930717 : Nat := 4983230072969 + 3 ^ 40 * 6930717 * 2
def baseEnd_6930717 : Nat := 3558789101287265271563719

theorem tailTrace_6930717 : CollatzResearch.WordTrace tailWord_6930717 prefixEnd_6930717 3558789101287265271563719 := by
  unfold tailWord_6930717
  simp only [CollatzResearch.WordTrace]
  refine ⟨252784016032203456071750405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168522677354802304047833603 252784016032203456071750405)
  ·
    refine ⟨47397003006038148013453201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252784016032203456071750405 47397003006038148013453201)
    ·
      refine ⟨35547752254528611010089901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47397003006038148013453201 35547752254528611010089901)
      ·
        refine ⟨13330407095448229128783713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35547752254528611010089901 13330407095448229128783713)
        ·
          refine ⟨9997805321586171846587785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13330407095448229128783713 9997805321586171846587785)
          ·
            refine ⟨7498353991189628884940839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9997805321586171846587785 7498353991189628884940839)
            ·
              refine ⟨11247530986784443327411259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498353991189628884940839 11247530986784443327411259)
              ·
                refine ⟨16871296480176664991116889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11247530986784443327411259 16871296480176664991116889)
                ·
                  refine ⟨12653472360132498743337667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16871296480176664991116889 12653472360132498743337667)
                  ·
                    refine ⟨18980208540198748115006501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12653472360132498743337667 18980208540198748115006501)
                    ·
                      refine ⟨3558789101287265271563719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18980208540198748115006501 3558789101287265271563719)
                      ·
                        rfl

theorem cell23_6930717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_6930717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930717 prefixEnd_6930717 := by exact prefixLift 6930717
  have htrace : WordTrace (prefixWord ++ tailWord_6930717) baseStart_6930717 baseEnd_6930717 := by
    simpa [prefixWord, tailWord_6930717, baseEnd_6930717] using wordTrace_append hprefix tailTrace_6930717
  have hstable : (prefixWord ++ tailWord_6930717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930717).length < 2 ^ (prefixWord ++ tailWord_6930717).sum := by decide
  have hdescent : baseEnd_6930717 < baseStart_6930717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930720 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6930720 : Nat := 118140960795 + 6930720 * 2 ^ 59
def prefixEnd_6930720 : Nat := 4983230072969 + 3 ^ 40 * 6930720 * 2
def baseEnd_6930720 : Nat := 3558790641729228759826205

theorem tailTrace_6930720 : CollatzResearch.WordTrace tailWord_6930720 prefixEnd_6930720 3558790641729228759826205 := by
  unfold tailWord_6930720
  simp only [CollatzResearch.WordTrace]
  refine ⟨126392062725596293792054807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168522750300795058389406409 126392062725596293792054807)
  ·
    refine ⟨189588094088394440688082211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126392062725596293792054807 189588094088394440688082211)
    ·
      refine ⟨284382141132591661032123317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189588094088394440688082211 284382141132591661032123317)
      ·
        refine ⟨26660825731180468221761561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284382141132591661032123317 26660825731180468221761561)
        ·
          refine ⟨19995619298385351166321171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26660825731180468221761561 19995619298385351166321171)
          ·
            refine ⟨29993428947578026749481757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19995619298385351166321171 29993428947578026749481757)
            ·
              refine ⟨11247535855341760031055659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29993428947578026749481757 11247535855341760031055659)
              ·
                refine ⟨16871303783012640046583489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11247535855341760031055659 16871303783012640046583489)
                ·
                  refine ⟨12653477837259480034937617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16871303783012640046583489 12653477837259480034937617)
                  ·
                    refine ⟨9490108377944610026203213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12653477837259480034937617 9490108377944610026203213)
                    ·
                      refine ⟨3558790641729228759826205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490108377944610026203213 3558790641729228759826205)
                      ·
                        rfl

theorem cell23_6930720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6930720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930720 prefixEnd_6930720 := by exact prefixLift 6930720
  have htrace : WordTrace (prefixWord ++ tailWord_6930720) baseStart_6930720 baseEnd_6930720 := by
    simpa [prefixWord, tailWord_6930720, baseEnd_6930720] using wordTrace_append hprefix tailTrace_6930720
  have hstable : (prefixWord ++ tailWord_6930720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930720).length < 2 ^ (prefixWord ++ tailWord_6930720).sum := by decide
  have hdescent : baseEnd_6930720 < baseStart_6930720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930736 : List Nat := [2, 1, 1, 1, 2, 2, 2, 2, 5, 5]
def baseStart_6930736 : Nat := 118140960795 + 6930736 * 2 ^ 59
def prefixEnd_6930736 : Nat := 4983230072969 + 3 ^ 40 * 6930736 * 2
def baseEnd_6930736 : Nat := 1186266285806566899075377

theorem tailTrace_6930736 : CollatzResearch.WordTrace tailWord_6930736 prefixEnd_6930736 1186266285806566899075377 := by
  unfold tailWord_6930736
  simp only [CollatzResearch.WordTrace]
  refine ⟨126392354509567311158346031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168523139346089748211128041 126392354509567311158346031)
  ·
    refine ⟨189588531764350966737519047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126392354509567311158346031 189588531764350966737519047)
    ·
      refine ⟨284382797646526450106278571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189588531764350966737519047 284382797646526450106278571)
      ·
        refine ⟨426574196469789675159417857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284382797646526450106278571 426574196469789675159417857)
        ·
          refine ⟨319930647352342256369563393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426574196469789675159417857 319930647352342256369563393)
          ·
            refine ⟨239947985514256692277172545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 319930647352342256369563393 239947985514256692277172545)
            ·
              refine ⟨179960989135692519207879409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239947985514256692277172545 179960989135692519207879409)
              ·
                refine ⟨134970741851769389405909557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 179960989135692519207879409 134970741851769389405909557)
                ·
                  refine ⟨12653507048603380256804021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134970741851769389405909557 12653507048603380256804021)
                  ·
                    refine ⟨1186266285806566899075377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12653507048603380256804021 1186266285806566899075377)
                    ·
                      rfl

theorem cell23_6930736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 5, 5].length) (baseStart_6930736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930736 prefixEnd_6930736 := by exact prefixLift 6930736
  have htrace : WordTrace (prefixWord ++ tailWord_6930736) baseStart_6930736 baseEnd_6930736 := by
    simpa [prefixWord, tailWord_6930736, baseEnd_6930736] using wordTrace_append hprefix tailTrace_6930736
  have hstable : (prefixWord ++ tailWord_6930736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930736).length < 2 ^ (prefixWord ++ tailWord_6930736).sum := by decide
  have hdescent : baseEnd_6930736 < baseStart_6930736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930740 : List Nat := [2, 5, 1, 1, 1, 2, 3, 2, 6]
def baseStart_6930740 : Nat := 118140960795 + 6930740 * 2 ^ 59
def prefixEnd_6930740 : Nat := 4983230072969 + 3 ^ 40 * 6930740 * 2
def baseEnd_6930740 : Nat := 395422323482479853508457

theorem tailTrace_6930740 : CollatzResearch.WordTrace tailWord_6930740 prefixEnd_6930740 395422323482479853508457 := by
  unfold tailWord_6930740
  simp only [CollatzResearch.WordTrace]
  refine ⟨126392427455560065499918837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168523236607413420666558449 126392427455560065499918837)
  ·
    refine ⟨11849290073958756140617391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126392427455560065499918837 11849290073958756140617391)
    ·
      refine ⟨17773935110938134210926087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11849290073958756140617391 17773935110938134210926087)
      ·
        refine ⟨26660902666407201316389131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17773935110938134210926087 26660902666407201316389131)
        ·
          refine ⟨39991353999610801974583697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26660902666407201316389131 39991353999610801974583697)
          ·
            refine ⟨29993515499708101480937773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39991353999610801974583697 29993515499708101480937773)
            ·
              refine ⟨11247568312390538055351665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29993515499708101480937773 11247568312390538055351665)
              ·
                refine ⟨8435676234292903541513749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11247568312390538055351665 8435676234292903541513749)
                ·
                  refine ⟨395422323482479853508457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8435676234292903541513749 395422323482479853508457)
                  ·
                    rfl

theorem cell23_6930740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_6930740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930740 prefixEnd_6930740 := by exact prefixLift 6930740
  have htrace : WordTrace (prefixWord ++ tailWord_6930740) baseStart_6930740 baseEnd_6930740 := by
    simpa [prefixWord, tailWord_6930740, baseEnd_6930740] using wordTrace_append hprefix tailTrace_6930740
  have hstable : (prefixWord ++ tailWord_6930740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930740).length < 2 ^ (prefixWord ++ tailWord_6930740).sum := by decide
  have hdescent : baseEnd_6930740 < baseStart_6930740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930783 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 4, 4]
def baseStart_6930783 : Nat := 118140960795 + 6930783 * 2 ^ 59
def prefixEnd_6930783 : Nat := 4983230072969 + 3 ^ 40 * 6930783 * 2
def baseEnd_6930783 : Nat := 1186274330336820671112805

theorem tailTrace_6930783 : CollatzResearch.WordTrace tailWord_6930783 prefixEnd_6930783 1186274330336820671112805 := by
  unfold tailWord_6930783
  simp only [CollatzResearch.WordTrace]
  refine ⟨252786423249964349343653003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168524282166642899562435335 252786423249964349343653003)
  ·
    refine ⟨379179634874946524015479505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252786423249964349343653003 379179634874946524015479505)
    ·
      refine ⟨284384726156209893011609629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379179634874946524015479505 284384726156209893011609629)
      ·
        refine ⟨106644272308578709879353611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284384726156209893011609629 106644272308578709879353611)
        ·
          refine ⟨159966408462868064819030417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106644272308578709879353611 159966408462868064819030417)
          ·
            refine ⟨119974806347151048614272813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 159966408462868064819030417 119974806347151048614272813)
            ·
              refine ⟨44990552380181643230352305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119974806347151048614272813 44990552380181643230352305)
              ·
                refine ⟨33742914285136232422764229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44990552380181643230352305 33742914285136232422764229)
                ·
                  refine ⟨6326796428463043579268293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33742914285136232422764229 6326796428463043579268293)
                  ·
                    refine ⟨1186274330336820671112805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326796428463043579268293 1186274330336820671112805)
                    ·
                      rfl

theorem cell23_6930783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 4, 4].length) (baseStart_6930783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930783 prefixEnd_6930783 := by exact prefixLift 6930783
  have htrace : WordTrace (prefixWord ++ tailWord_6930783) baseStart_6930783 baseEnd_6930783 := by
    simpa [prefixWord, tailWord_6930783, baseEnd_6930783] using wordTrace_append hprefix tailTrace_6930783
  have hstable : (prefixWord ++ tailWord_6930783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930783).length < 2 ^ (prefixWord ++ tailWord_6930783).sum := by decide
  have hdescent : baseEnd_6930783 < baseStart_6930783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930793 : List Nat := [1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_6930793 : Nat := 118140960795 + 6930793 * 2 ^ 59
def prefixEnd_6930793 : Nat := 4983230072969 + 3 ^ 40 * 6930793 * 2
def baseEnd_6930793 : Nat := 3558828125817006974213369

theorem tailTrace_6930793 : CollatzResearch.WordTrace tailWord_6930793 prefixEnd_6930793 3558828125817006974213369 := by
  unfold tailWord_6930793
  simp only [CollatzResearch.WordTrace]
  refine ⟨252786787979928121051517033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168524525319952080701011355 252786787979928121051517033)
  ·
    refine ⟨189590090984946090788637775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252786787979928121051517033 189590090984946090788637775)
    ·
      refine ⟨284385136477419136182956663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189590090984946090788637775 284385136477419136182956663)
      ·
        refine ⟨426577704716128704274434995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284385136477419136182956663 426577704716128704274434995)
        ·
          refine ⟨639866557074193056411652493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426577704716128704274434995 639866557074193056411652493)
          ·
            refine ⟨239949958902822396154369685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639866557074193056411652493 239949958902822396154369685)
            ·
              refine ⟨11247654323569799819736079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 239949958902822396154369685 11247654323569799819736079)
              ·
                refine ⟨16871481485354699729604119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11247654323569799819736079 16871481485354699729604119)
                ·
                  refine ⟨25307222228032049594406179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16871481485354699729604119 25307222228032049594406179)
                  ·
                    refine ⟨37960833342048074391609269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25307222228032049594406179 37960833342048074391609269)
                    ·
                      refine ⟨3558828125817006974213369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37960833342048074391609269 3558828125817006974213369)
                      ·
                        rfl

theorem cell23_6930793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_6930793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930793 prefixEnd_6930793 := by exact prefixLift 6930793
  have htrace : WordTrace (prefixWord ++ tailWord_6930793) baseStart_6930793 baseEnd_6930793 := by
    simpa [prefixWord, tailWord_6930793, baseEnd_6930793] using wordTrace_append hprefix tailTrace_6930793
  have hstable : (prefixWord ++ tailWord_6930793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930793).length < 2 ^ (prefixWord ++ tailWord_6930793).sum := by decide
  have hdescent : baseEnd_6930793 < baseStart_6930793 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930813 : List Nat := [1, 4, 1, 1, 2, 4, 2, 8]
def baseStart_6930813 : Nat := 118140960795 + 6930813 * 2 ^ 59
def prefixEnd_6930813 : Nat := 4983230072969 + 3 ^ 40 * 6930813 * 2
def baseEnd_6930813 : Nat := 131808829460373959109751

theorem tailTrace_6930813 : CollatzResearch.WordTrace tailWord_6930813 prefixEnd_6930813 131808829460373959109751 := by
  unfold tailWord_6930813
  simp only [CollatzResearch.WordTrace]
  refine ⟨252787517439855664467245093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168525011626570442978163395 252787517439855664467245093)
  ·
    refine ⟨47397659519972937087608455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252787517439855664467245093 47397659519972937087608455)
    ·
      refine ⟨71096489279959405631412683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47397659519972937087608455 71096489279959405631412683)
      ·
        refine ⟨106644733919939108447119025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71096489279959405631412683 106644733919939108447119025)
        ·
          refine ⟨79983550439954331335339269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106644733919939108447119025 79983550439954331335339269)
          ·
            refine ⟨14996915707491437125376113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79983550439954331335339269 14996915707491437125376113)
            ·
              refine ⟨11247686780618577844032085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14996915707491437125376113 11247686780618577844032085)
              ·
                refine ⟨131808829460373959109751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11247686780618577844032085 131808829460373959109751)
                ·
                  rfl

theorem cell23_6930813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 2, 8].length) (baseStart_6930813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930813 prefixEnd_6930813 := by exact prefixLift 6930813
  have htrace : WordTrace (prefixWord ++ tailWord_6930813) baseStart_6930813 baseEnd_6930813 := by
    simpa [prefixWord, tailWord_6930813, baseEnd_6930813] using wordTrace_append hprefix tailTrace_6930813
  have hstable : (prefixWord ++ tailWord_6930813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930813).length < 2 ^ (prefixWord ++ tailWord_6930813).sum := by decide
  have hdescent : baseEnd_6930813 < baseStart_6930813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930817 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_6930817 : Nat := 118140960795 + 6930817 * 2 ^ 59
def prefixEnd_6930817 : Nat := 4983230072969 + 3 ^ 40 * 6930817 * 2
def baseEnd_6930817 : Nat := 1186280149784238293437753

theorem tailTrace_6930817 : CollatzResearch.WordTrace tailWord_6930817 prefixEnd_6930817 1186280149784238293437753 := by
  unfold tailWord_6930817
  simp only [CollatzResearch.WordTrace]
  refine ⟨252787663331841173150390705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168525108887894115433593803 252787663331841173150390705)
  ·
    refine ⟨189590747498880879862793029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252787663331841173150390705 189590747498880879862793029)
    ·
      refine ⟨35548265156040164974273693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189590747498880879862793029 35548265156040164974273693)
      ·
        refine ⟨13330599433515061865352635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35548265156040164974273693 13330599433515061865352635)
        ·
          refine ⟨19995899150272592798028953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330599433515061865352635 19995899150272592798028953)
          ·
            refine ⟨14996924362704444598521715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19995899150272592798028953 14996924362704444598521715)
            ·
              refine ⟨22495386544056666897782573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14996924362704444598521715 22495386544056666897782573)
              ·
                refine ⟨8435769954021250086668465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22495386544056666897782573 8435769954021250086668465)
                ·
                  refine ⟨6326827465515937565001349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8435769954021250086668465 6326827465515937565001349)
                  ·
                    refine ⟨1186280149784238293437753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6326827465515937565001349 1186280149784238293437753)
                    ·
                      rfl

theorem cell23_6930817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_6930817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930817 prefixEnd_6930817 := by exact prefixLift 6930817
  have htrace : WordTrace (prefixWord ++ tailWord_6930817) baseStart_6930817 baseEnd_6930817 := by
    simpa [prefixWord, tailWord_6930817, baseEnd_6930817] using wordTrace_append hprefix tailTrace_6930817
  have hstable : (prefixWord ++ tailWord_6930817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930817).length < 2 ^ (prefixWord ++ tailWord_6930817).sum := by decide
  have hdescent : baseEnd_6930817 < baseStart_6930817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930827 : List Nat := [1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 3]
def baseStart_6930827 : Nat := 118140960795 + 6930827 * 2 ^ 59
def prefixEnd_6930827 : Nat := 4983230072969 + 3 ^ 40 * 6930827 * 2
def baseEnd_6930827 : Nat := 3558845584159259841188213

theorem tailTrace_6930827 : CollatzResearch.WordTrace tailWord_6930827 prefixEnd_6930827 3558845584159259841188213 := by
  unfold tailWord_6930827
  simp only [CollatzResearch.WordTrace]
  refine ⟨252788028061804944858254735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168525352041203296572169823 252788028061804944858254735)
  ·
    refine ⟨379182042092707417287382103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252788028061804944858254735 379182042092707417287382103)
    ·
      refine ⟨568773063139061125931073155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379182042092707417287382103 568773063139061125931073155)
      ·
        refine ⟨853159594708591688896609733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568773063139061125931073155 853159594708591688896609733)
        ·
          refine ⟨159967424007860941668114325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 853159594708591688896609733 159967424007860941668114325)
          ·
            refine ⟨7498473000368481640692859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 159967424007860941668114325 7498473000368481640692859)
            ·
              refine ⟨11247709500552722461039289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498473000368481640692859 11247709500552722461039289)
              ·
                refine ⟨8435782125414541845779467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11247709500552722461039289 8435782125414541845779467)
                ·
                  refine ⟨12653673188121812768669201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435782125414541845779467 12653673188121812768669201)
                  ·
                    refine ⟨9490254891091359576501901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12653673188121812768669201 9490254891091359576501901)
                    ·
                      refine ⟨3558845584159259841188213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490254891091359576501901 3558845584159259841188213)
                      ·
                        rfl

theorem cell23_6930827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 2, 3].length) (baseStart_6930827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930827 prefixEnd_6930827 := by exact prefixLift 6930827
  have htrace : WordTrace (prefixWord ++ tailWord_6930827) baseStart_6930827 baseEnd_6930827 := by
    simpa [prefixWord, tailWord_6930827, baseEnd_6930827] using wordTrace_append hprefix tailTrace_6930827
  have hstable : (prefixWord ++ tailWord_6930827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930827).length < 2 ^ (prefixWord ++ tailWord_6930827).sum := by decide
  have hdescent : baseEnd_6930827 < baseStart_6930827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930838 : List Nat := [5, 3, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6930838 : Nat := 118140960795 + 6930838 * 2 ^ 59
def prefixEnd_6930838 : Nat := 4983230072969 + 3 ^ 40 * 6930838 * 2
def baseEnd_6930838 : Nat := 1186283744148819766050221

theorem tailTrace_6930838 : CollatzResearch.WordTrace tailWord_6930838 prefixEnd_6930838 1186283744148819766050221 := by
  unfold tailWord_6930838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15799276829047818358556573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168525619509843395824603445 15799276829047818358556573)
  ·
    refine ⟨5924728810892931884458715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15799276829047818358556573 5924728810892931884458715)
    ·
      refine ⟨8887093216339397826688073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5924728810892931884458715 8887093216339397826688073)
      ·
        refine ⟨6665319912254548370016055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8887093216339397826688073 6665319912254548370016055)
        ·
          refine ⟨9997979868381822555024083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665319912254548370016055 9997979868381822555024083)
          ·
            refine ⟨14996969802572733832536125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9997979868381822555024083 14996969802572733832536125)
            ·
              refine ⟨5623863675964775187201047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14996969802572733832536125 5623863675964775187201047)
              ·
                refine ⟨8435795513947162780801571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623863675964775187201047 8435795513947162780801571)
                ·
                  refine ⟨12653693270920744171202357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435795513947162780801571 12653693270920744171202357)
                  ·
                    refine ⟨1186283744148819766050221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12653693270920744171202357 1186283744148819766050221)
                    ·
                      rfl

theorem cell23_6930838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6930838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930838 prefixEnd_6930838 := by exact prefixLift 6930838
  have htrace : WordTrace (prefixWord ++ tailWord_6930838) baseStart_6930838 baseEnd_6930838 := by
    simpa [prefixWord, tailWord_6930838, baseEnd_6930838] using wordTrace_append hprefix tailTrace_6930838
  have hstable : (prefixWord ++ tailWord_6930838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930838).length < 2 ^ (prefixWord ++ tailWord_6930838).sum := by decide
  have hdescent : baseEnd_6930838 < baseStart_6930838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930840 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6930840 : Nat := 118140960795 + 6930840 * 2 ^ 59
def prefixEnd_6930840 : Nat := 4983230072969 + 3 ^ 40 * 6930840 * 2
def baseEnd_6930840 : Nat := 3558852259407768290325653

theorem tailTrace_6930840 : CollatzResearch.WordTrace tailWord_6930840 prefixEnd_6930840 3558852259407768290325653 := by
  unfold tailWord_6930840
  simp only [CollatzResearch.WordTrace]
  refine ⟨126394251105378924039238987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168525668140505232052318649 126394251105378924039238987)
  ·
    refine ⟨189591376658068386058858481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126394251105378924039238987 189591376658068386058858481)
    ·
      refine ⟨142193532493551289544143861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189591376658068386058858481 142193532493551289544143861)
      ·
        refine ⟨13330643671270433394763487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 142193532493551289544143861 13330643671270433394763487)
        ·
          refine ⟨19995965506905650092145231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13330643671270433394763487 19995965506905650092145231)
          ·
            refine ⟨29993948260358475138217847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19995965506905650092145231 29993948260358475138217847)
            ·
              refine ⟨44990922390537712707326771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29993948260358475138217847 44990922390537712707326771)
              ·
                refine ⟨67486383585806569060990157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44990922390537712707326771 67486383585806569060990157)
                ·
                  refine ⟨25307393844677463397871309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67486383585806569060990157 25307393844677463397871309)
                  ·
                    refine ⟨9490272691754048774201741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25307393844677463397871309 9490272691754048774201741)
                    ·
                      refine ⟨3558852259407768290325653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490272691754048774201741 3558852259407768290325653)
                      ·
                        rfl

theorem cell23_6930840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6930840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930840 prefixEnd_6930840 := by exact prefixLift 6930840
  have htrace : WordTrace (prefixWord ++ tailWord_6930840) baseStart_6930840 baseEnd_6930840 := by
    simpa [prefixWord, tailWord_6930840, baseEnd_6930840] using wordTrace_append hprefix tailTrace_6930840
  have hstable : (prefixWord ++ tailWord_6930840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930840).length < 2 ^ (prefixWord ++ tailWord_6930840).sum := by decide
  have hdescent : baseEnd_6930840 < baseStart_6930840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930873 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_6930873 : Nat := 118140960795 + 6930873 * 2 ^ 59
def prefixEnd_6930873 : Nat := 4983230072969 + 3 ^ 40 * 6930873 * 2
def baseEnd_6930873 : Nat := 1186289734756455553737667

theorem tailTrace_6930873 : CollatzResearch.WordTrace tailWord_6930873 prefixEnd_6930873 1186289734756455553737667 := by
  unfold tailWord_6930873
  simp only [CollatzResearch.WordTrace]
  refine ⟨252789705819638294714429273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168526470546425529809619515 252789705819638294714429273)
  ·
    refine ⟨189592279364728721035821955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252789705819638294714429273 189592279364728721035821955)
    ·
      refine ⟨284388419047093081553732933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189592279364728721035821955 284388419047093081553732933)
      ·
        refine ⟨53322828571329952791324925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284388419047093081553732933 53322828571329952791324925)
        ·
          refine ⟨19996060714248732296746847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53322828571329952791324925 19996060714248732296746847)
          ·
            refine ⟨29994091071373098445120271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19996060714248732296746847 29994091071373098445120271)
            ·
              refine ⟨44991136607059647667680407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29994091071373098445120271 44991136607059647667680407)
              ·
                refine ⟨67486704910589471501520611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44991136607059647667680407 67486704910589471501520611)
                ·
                  refine ⟨101230057365884207252280917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67486704910589471501520611 101230057365884207252280917)
                  ·
                    refine ⟨1186289734756455553737667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 101230057365884207252280917 1186289734756455553737667)
                    ·
                      rfl

theorem cell23_6930873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_6930873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930873 prefixEnd_6930873 := by exact prefixLift 6930873
  have htrace : WordTrace (prefixWord ++ tailWord_6930873) baseStart_6930873 baseEnd_6930873 := by
    simpa [prefixWord, tailWord_6930873, baseEnd_6930873] using wordTrace_append hprefix tailTrace_6930873
  have hstable : (prefixWord ++ tailWord_6930873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930873).length < 2 ^ (prefixWord ++ tailWord_6930873).sum := by decide
  have hdescent : baseEnd_6930873 < baseStart_6930873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930883 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3]
def baseStart_6930883 : Nat := 118140960795 + 6930883 * 2 ^ 59
def prefixEnd_6930883 : Nat := 4983230072969 + 3 ^ 40 * 6930883 * 2
def baseEnd_6930883 : Nat := 3558874339075911622087955

theorem tailTrace_6930883 : CollatzResearch.WordTrace tailWord_6930883 prefixEnd_6930883 3558874339075911622087955 := by
  unfold tailWord_6930883
  simp only [CollatzResearch.WordTrace]
  refine ⟨252790070549602066422293303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168526713699734710948195535 252790070549602066422293303)
  ·
    refine ⟨379185105824403099633439955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252790070549602066422293303 379185105824403099633439955)
    ·
      refine ⟨568777658736604649450159933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379185105824403099633439955 568777658736604649450159933)
      ·
        refine ⟨213291622026226743543809975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 568777658736604649450159933 213291622026226743543809975)
        ·
          refine ⟨319937433039340115315714963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213291622026226743543809975 319937433039340115315714963)
          ·
            refine ⟨479906149559010172973572445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319937433039340115315714963 479906149559010172973572445)
            ·
              refine ⟨179964806084628814865089667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 479906149559010172973572445 179964806084628814865089667)
              ·
                refine ⟨269947209126943222297634501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 179964806084628814865089667 269947209126943222297634501)
                ·
                  refine ⟨50615101711301854180806469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 269947209126943222297634501 50615101711301854180806469)
                  ·
                    refine ⟨9490331570869097658901213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50615101711301854180806469 9490331570869097658901213)
                    ·
                      refine ⟨3558874339075911622087955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490331570869097658901213 3558874339075911622087955)
                      ·
                        rfl

theorem cell23_6930883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 3].length) (baseStart_6930883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930883 prefixEnd_6930883 := by exact prefixLift 6930883
  have htrace : WordTrace (prefixWord ++ tailWord_6930883) baseStart_6930883 baseEnd_6930883 := by
    simpa [prefixWord, tailWord_6930883, baseEnd_6930883] using wordTrace_append hprefix tailTrace_6930883
  have hstable : (prefixWord ++ tailWord_6930883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930883).length < 2 ^ (prefixWord ++ tailWord_6930883).sum := by decide
  have hdescent : baseEnd_6930883 < baseStart_6930883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930901 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6930901 : Nat := 118140960795 + 6930901 * 2 ^ 59
def prefixEnd_6930901 : Nat := 4983230072969 + 3 ^ 40 * 6930901 * 2
def baseEnd_6930901 : Nat := 3558883581727692551662873

theorem tailTrace_6930901 : CollatzResearch.WordTrace tailWord_6930901 prefixEnd_6930901 3558883581727692551662873 := by
  unfold tailWord_6930901
  simp only [CollatzResearch.WordTrace]
  refine ⟨252790727063536855496448557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168527151375691236997632371 252790727063536855496448557)
  ·
    refine ⟨94796522648826320811168209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252790727063536855496448557 94796522648826320811168209)
    ·
      refine ⟨71097391986619740608376157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94796522648826320811168209 71097391986619740608376157)
      ·
        refine ⟨26661521994982402728141059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71097391986619740608376157 26661521994982402728141059)
        ·
          refine ⟨39992282992473604092211589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26661521994982402728141059 39992282992473604092211589)
          ·
            refine ⟨7498553061088800767289673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39992282992473604092211589 7498553061088800767289673)
            ·
              refine ⟨5623914795816600575467255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7498553061088800767289673 5623914795816600575467255)
              ·
                refine ⟨8435872193724900863200883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5623914795816600575467255 8435872193724900863200883)
                ·
                  refine ⟨12653808290587351294801325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8435872193724900863200883 12653808290587351294801325)
                  ·
                    refine ⟨4745178108970256735550497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12653808290587351294801325 4745178108970256735550497)
                    ·
                      refine ⟨3558883581727692551662873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745178108970256735550497 3558883581727692551662873)
                      ·
                        rfl

theorem cell23_6930901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6930901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930901 prefixEnd_6930901 := by exact prefixLift 6930901
  have htrace : WordTrace (prefixWord ++ tailWord_6930901) baseStart_6930901 baseEnd_6930901 := by
    simpa [prefixWord, tailWord_6930901, baseEnd_6930901] using wordTrace_append hprefix tailTrace_6930901
  have hstable : (prefixWord ++ tailWord_6930901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930901).length < 2 ^ (prefixWord ++ tailWord_6930901).sum := by decide
  have hdescent : baseEnd_6930901 < baseStart_6930901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930920 : List Nat := [2, 1, 4, 1, 1, 4, 2, 1, 7]
def baseStart_6930920 : Nat := 118140960795 + 6930920 * 2 ^ 59
def prefixEnd_6930920 : Nat := 4983230072969 + 3 ^ 40 * 6930920 * 2
def baseEnd_6930920 : Nat := 395432593095569775258365

theorem tailTrace_6930920 : CollatzResearch.WordTrace tailWord_6930920 prefixEnd_6930920 395432593095569775258365 := by
  unfold tailWord_6930920
  simp only [CollatzResearch.WordTrace]
  refine ⟨126395710025234010870695107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168527613366978681160926809 126395710025234010870695107)
  ·
    refine ⟨189593565037851016306042661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126395710025234010870695107 189593565037851016306042661)
    ·
      refine ⟨35548793444597065557382999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189593565037851016306042661 35548793444597065557382999)
      ·
        refine ⟨53323190166895598336074499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35548793444597065557382999 53323190166895598336074499)
        ·
          refine ⟨79984785250343397504111749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53323190166895598336074499 79984785250343397504111749)
          ·
            refine ⟨14997147234439387032020953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79984785250343397504111749 14997147234439387032020953)
            ·
              refine ⟨11247860425829540274015715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14997147234439387032020953 11247860425829540274015715)
              ·
                refine ⟨16871790638744310411023573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11247860425829540274015715 16871790638744310411023573)
                ·
                  refine ⟨395432593095569775258365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16871790638744310411023573 395432593095569775258365)
                  ·
                    rfl

theorem cell23_6930920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 7].length) (baseStart_6930920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930920 prefixEnd_6930920 := by exact prefixLift 6930920
  have htrace : WordTrace (prefixWord ++ tailWord_6930920) baseStart_6930920 baseEnd_6930920 := by
    simpa [prefixWord, tailWord_6930920, baseEnd_6930920] using wordTrace_append hprefix tailTrace_6930920
  have hstable : (prefixWord ++ tailWord_6930920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930920).length < 2 ^ (prefixWord ++ tailWord_6930920).sum := by decide
  have hdescent : baseEnd_6930920 < baseStart_6930920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6930970 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_6930970 : Nat := 118140960795 + 6930970 * 2 ^ 59
def prefixEnd_6930970 : Nat := 4983230072969 + 3 ^ 40 * 6930970 * 2
def baseEnd_6930970 : Nat := 3558919011892852781700055

theorem tailTrace_6930970 : CollatzResearch.WordTrace tailWord_6930970 prefixEnd_6930970 3558919011892852781700055 := by
  unfold tailWord_6930970
  simp only [CollatzResearch.WordTrace]
  refine ⟨63198310925071720070177591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168528829133524586853806909 63198310925071720070177591)
  ·
    refine ⟨94797466387607580105266387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63198310925071720070177591 94797466387607580105266387)
    ·
      refine ⟨142196199581411370157899581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94797466387607580105266387 142196199581411370157899581)
      ·
        refine ⟨53323574843029263809212343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142196199581411370157899581 53323574843029263809212343)
        ·
          refine ⟨79985362264543895713818515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53323574843029263809212343 79985362264543895713818515)
          ·
            refine ⟨119978043396815843570727773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79985362264543895713818515 119978043396815843570727773)
            ·
              refine ⟨44991766273805941339022915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119978043396815843570727773 44991766273805941339022915)
              ·
                refine ⟨67487649410708912008534373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44991766273805941339022915 67487649410708912008534373)
                ·
                  refine ⟨12653934264507921001600195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67487649410708912008534373 12653934264507921001600195)
                  ·
                    refine ⟨18980901396761881502400293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12653934264507921001600195 18980901396761881502400293)
                    ·
                      refine ⟨3558919011892852781700055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18980901396761881502400293 3558919011892852781700055)
                      ·
                        rfl

theorem cell23_6930970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_6930970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6930970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6930970 prefixEnd_6930970 := by exact prefixLift 6930970
  have htrace : WordTrace (prefixWord ++ tailWord_6930970) baseStart_6930970 baseEnd_6930970 := by
    simpa [prefixWord, tailWord_6930970, baseEnd_6930970] using wordTrace_append hprefix tailTrace_6930970
  have hstable : (prefixWord ++ tailWord_6930970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6930970).length < 2 ^ (prefixWord ++ tailWord_6930970).sum := by decide
  have hdescent : baseEnd_6930970 < baseStart_6930970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6930970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931007 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_6931007 : Nat := 118140960795 + 6931007 * 2 ^ 59
def prefixEnd_6931007 : Nat := 4983230072969 + 3 ^ 40 * 6931007 * 2
def baseEnd_6931007 : Nat := 3558938010677069136937385

theorem tailTrace_6931007 : CollatzResearch.WordTrace tailWord_6931007 prefixEnd_6931007 3558938010677069136937385 := by
  unfold tailWord_6931007
  simp only [CollatzResearch.WordTrace]
  refine ⟨252794593201152835599807275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168529728800768557066538183 252794593201152835599807275)
  ·
    refine ⟨379191889801729253399710913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252794593201152835599807275 379191889801729253399710913)
    ·
      refine ⟨284393917351296940049783185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379191889801729253399710913 284393917351296940049783185)
      ·
        refine ⟨213295438013472705037337389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284393917351296940049783185 213295438013472705037337389)
        ·
          refine ⟨79985789255052264389001521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213295438013472705037337389 79985789255052264389001521)
          ·
            refine ⟨59989341941289198291751141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79985789255052264389001521 59989341941289198291751141)
            ·
              refine ⟨11248001613991724679703339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59989341941289198291751141 11248001613991724679703339)
              ·
                refine ⟨16872002420987587019555009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248001613991724679703339 16872002420987587019555009)
                ·
                  refine ⟨12654001815740690264666257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16872002420987587019555009 12654001815740690264666257)
                  ·
                    refine ⟨9490501361805517698499693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12654001815740690264666257 9490501361805517698499693)
                    ·
                      refine ⟨3558938010677069136937385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490501361805517698499693 3558938010677069136937385)
                      ·
                        rfl

theorem cell23_6931007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_6931007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931007 prefixEnd_6931007 := by exact prefixLift 6931007
  have htrace : WordTrace (prefixWord ++ tailWord_6931007) baseStart_6931007 baseEnd_6931007 := by
    simpa [prefixWord, tailWord_6931007, baseEnd_6931007] using wordTrace_append hprefix tailTrace_6931007
  have hstable : (prefixWord ++ tailWord_6931007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931007).length < 2 ^ (prefixWord ++ tailWord_6931007).sum := by decide
  have hdescent : baseEnd_6931007 < baseStart_6931007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931040 : List Nat := [2, 1, 1, 3, 2, 1, 3, 2, 3, 5]
def baseStart_6931040 : Nat := 118140960795 + 6931040 * 2 ^ 59
def prefixEnd_6931040 : Nat := 4983230072969 + 3 ^ 40 * 6931040 * 2
def baseEnd_6931040 : Nat := 1186318318512889169274911

theorem tailTrace_6931040 : CollatzResearch.WordTrace tailWord_6931040 prefixEnd_6931040 1186318318512889169274911 := by
  unfold tailWord_6931040
  simp only [CollatzResearch.WordTrace]
  refine ⟨126397898405016641117879287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168530531206688854823839049 126397898405016641117879287)
  ·
    refine ⟨189596847607524961676818931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126397898405016641117879287 189596847607524961676818931)
    ·
      refine ⟨284395271411287442515228397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189596847607524961676818931 284395271411287442515228397)
      ·
        refine ⟨106648226779232790943210649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284395271411287442515228397 106648226779232790943210649)
        ·
          refine ⟨79986170084424593207407987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106648226779232790943210649 79986170084424593207407987)
          ·
            refine ⟨119979255126636889811111981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79986170084424593207407987 119979255126636889811111981)
            ·
              refine ⟨44992220672488833679166993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119979255126636889811111981 44992220672488833679166993)
              ·
                refine ⟨33744165504366625259375245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44992220672488833679166993 33744165504366625259375245)
                ·
                  refine ⟨12654062064137484472265717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33744165504366625259375245 12654062064137484472265717)
                  ·
                    refine ⟨1186318318512889169274911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12654062064137484472265717 1186318318512889169274911)
                    ·
                      rfl

theorem cell23_6931040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3, 5].length) (baseStart_6931040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931040 prefixEnd_6931040 := by exact prefixLift 6931040
  have htrace : WordTrace (prefixWord ++ tailWord_6931040) baseStart_6931040 baseEnd_6931040 := by
    simpa [prefixWord, tailWord_6931040, baseEnd_6931040] using wordTrace_append hprefix tailTrace_6931040
  have hstable : (prefixWord ++ tailWord_6931040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931040).length < 2 ^ (prefixWord ++ tailWord_6931040).sum := by decide
  have hdescent : baseEnd_6931040 < baseStart_6931040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931047 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_6931047 : Nat := 118140960795 + 6931047 * 2 ^ 59
def prefixEnd_6931047 : Nat := 4983230072969 + 3 ^ 40 * 6931047 * 2
def baseEnd_6931047 : Nat := 3558958549903248980437201

theorem tailTrace_6931047 : CollatzResearch.WordTrace tailWord_6931047 prefixEnd_6931047 3558958549903248980437201 := by
  unfold tailWord_6931047
  simp only [CollatzResearch.WordTrace]
  refine ⟨252796052121007922431263395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168530701414005281620842263 252796052121007922431263395)
  ·
    refine ⟨379194078181511883646895093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252796052121007922431263395 379194078181511883646895093)
    ·
      refine ⟨35549444829516739091896415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379194078181511883646895093 35549444829516739091896415)
      ·
        refine ⟨53324167244275108637844623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35549444829516739091896415 53324167244275108637844623)
        ·
          refine ⟨79986250866412662956766935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53324167244275108637844623 79986250866412662956766935)
          ·
            refine ⟨119979376299618994435150403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79986250866412662956766935 119979376299618994435150403)
            ·
              refine ⟨179969064449428491652725605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119979376299618994435150403 179969064449428491652725605)
              ·
                refine ⟨33744199584267842184886051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 179969064449428491652725605 33744199584267842184886051)
                ·
                  refine ⟨50616299376401763277329077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33744199584267842184886051 50616299376401763277329077)
                  ·
                    refine ⟨4745278066537665307249601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50616299376401763277329077 4745278066537665307249601)
                    ·
                      refine ⟨3558958549903248980437201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745278066537665307249601 3558958549903248980437201)
                      ·
                        rfl

theorem cell23_6931047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_6931047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931047 prefixEnd_6931047 := by exact prefixLift 6931047
  have htrace : WordTrace (prefixWord ++ tailWord_6931047) baseStart_6931047 baseEnd_6931047 := by
    simpa [prefixWord, tailWord_6931047, baseEnd_6931047] using wordTrace_append hprefix tailTrace_6931047
  have hstable : (prefixWord ++ tailWord_6931047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931047).length < 2 ^ (prefixWord ++ tailWord_6931047).sum := by decide
  have hdescent : baseEnd_6931047 < baseStart_6931047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931050 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_6931050 : Nat := 118140960795 + 6931050 * 2 ^ 59
def prefixEnd_6931050 : Nat := 4983230072969 + 3 ^ 40 * 6931050 * 2
def baseEnd_6931050 : Nat := 3558960090345212468699687

theorem tailTrace_6931050 : CollatzResearch.WordTrace tailWord_6931050 prefixEnd_6931050 3558960090345212468699687 := by
  unfold tailWord_6931050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63199040384999263485905651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168530774359998035962415069 63199040384999263485905651)
  ·
    refine ⟨94798560577498895228858477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63199040384999263485905651 94798560577498895228858477)
    ·
      refine ⟨35549460216562085710821929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94798560577498895228858477 35549460216562085710821929)
      ·
        refine ⟨26662095162421564283116447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35549460216562085710821929 26662095162421564283116447)
        ·
          refine ⟨39993142743632346424674671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26662095162421564283116447 39993142743632346424674671)
          ·
            refine ⟨59989714115448519637012007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39993142743632346424674671 59989714115448519637012007)
            ·
              refine ⟨89984571173172779455518011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59989714115448519637012007 89984571173172779455518011)
              ·
                refine ⟨134976856759759169183277017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89984571173172779455518011 134976856759759169183277017)
                ·
                  refine ⟨101232642569819376887457763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134976856759759169183277017 101232642569819376887457763)
                  ·
                    refine ⟨151848963854729065331186645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101232642569819376887457763 151848963854729065331186645)
                    ·
                      refine ⟨3558960090345212468699687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 151848963854729065331186645 3558960090345212468699687)
                      ·
                        rfl

theorem cell23_6931050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_6931050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931050 prefixEnd_6931050 := by exact prefixLift 6931050
  have htrace : WordTrace (prefixWord ++ tailWord_6931050) baseStart_6931050 baseEnd_6931050 := by
    simpa [prefixWord, tailWord_6931050, baseEnd_6931050] using wordTrace_append hprefix tailTrace_6931050
  have hstable : (prefixWord ++ tailWord_6931050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931050).length < 2 ^ (prefixWord ++ tailWord_6931050).sum := by decide
  have hdescent : baseEnd_6931050 < baseStart_6931050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931054 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_6931054 : Nat := 118140960795 + 6931054 * 2 ^ 59
def prefixEnd_6931054 : Nat := 4983230072969 + 3 ^ 40 * 6931054 * 2
def baseEnd_6931054 : Nat := 3558962144267830453049669

theorem tailTrace_6931054 : CollatzResearch.WordTrace tailWord_6931054 prefixEnd_6931054 3558962144267830453049669 := by
  unfold tailWord_6931054
  simp only [CollatzResearch.WordTrace]
  refine ⟨31599538428997820328346027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168530871621321708417845477 31599538428997820328346027)
  ·
    refine ⟨47399307643496730492519041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31599538428997820328346027 47399307643496730492519041)
    ·
      refine ⟨35549480732622547869389281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47399307643496730492519041 35549480732622547869389281)
      ·
        refine ⟨26662110549466910902041961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35549480732622547869389281 26662110549466910902041961)
        ·
          refine ⟨19996582912100183176531471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26662110549466910902041961 19996582912100183176531471)
          ·
            refine ⟨29994874368150274764797207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19996582912100183176531471 29994874368150274764797207)
            ·
              refine ⟨44992311552225412147195811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29994874368150274764797207 44992311552225412147195811)
              ·
                refine ⟨67488467328338118220793717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44992311552225412147195811 67488467328338118220793717)
                ·
                  refine ⟨6327043812031698583199411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67488467328338118220793717 6327043812031698583199411)
                  ·
                    refine ⟨9490565718047547874799117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6327043812031698583199411 9490565718047547874799117)
                    ·
                      refine ⟨3558962144267830453049669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490565718047547874799117 3558962144267830453049669)
                      ·
                        rfl

theorem cell23_6931054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_6931054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931054 prefixEnd_6931054 := by exact prefixLift 6931054
  have htrace : WordTrace (prefixWord ++ tailWord_6931054) baseStart_6931054 baseEnd_6931054 := by
    simpa [prefixWord, tailWord_6931054, baseEnd_6931054] using wordTrace_append hprefix tailTrace_6931054
  have hstable : (prefixWord ++ tailWord_6931054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931054).length < 2 ^ (prefixWord ++ tailWord_6931054).sum := by decide
  have hdescent : baseEnd_6931054 < baseStart_6931054 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931104 : List Nat := [2, 1, 1, 4, 4, 2, 1, 1, 1, 6]
def baseStart_6931104 : Nat := 118140960795 + 6931104 * 2 ^ 59
def prefixEnd_6931104 : Nat := 4983230072969 + 3 ^ 40 * 6931104 * 2
def baseEnd_6931104 : Nat := 1186329272766851752474813

theorem tailTrace_6931104 : CollatzResearch.WordTrace tailWord_6931104 prefixEnd_6931104 1186329272766851752474813 := by
  unfold tailWord_6931104
  simp only [CollatzResearch.WordTrace]
  refine ⟨126399065540900710583044183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168532087387867614110725577 126399065540900710583044183)
  ·
    refine ⟨189598598311351065874566275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126399065540900710583044183 189598598311351065874566275)
    ·
      refine ⟨284397897467026598811849413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189598598311351065874566275 284397897467026598811849413)
      ·
        refine ⟨53324605775067487277221765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 284397897467026598811849413 53324605775067487277221765)
        ·
          refine ⟨9998363582825153864479081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53324605775067487277221765 9998363582825153864479081)
          ·
            refine ⟨7498772687118865398359311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998363582825153864479081 7498772687118865398359311)
            ·
              refine ⟨11248159030678298097538967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498772687118865398359311 11248159030678298097538967)
              ·
                refine ⟨16872238546017447146308451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248159030678298097538967 16872238546017447146308451)
                ·
                  refine ⟨25308357819026170719462677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16872238546017447146308451 25308357819026170719462677)
                  ·
                    refine ⟨1186329272766851752474813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25308357819026170719462677 1186329272766851752474813)
                    ·
                      rfl

theorem cell23_6931104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 1, 1, 6].length) (baseStart_6931104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931104 prefixEnd_6931104 := by exact prefixLift 6931104
  have htrace : WordTrace (prefixWord ++ tailWord_6931104) baseStart_6931104 baseEnd_6931104 := by
    simpa [prefixWord, tailWord_6931104, baseEnd_6931104] using wordTrace_append hprefix tailTrace_6931104
  have hstable : (prefixWord ++ tailWord_6931104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931104).length < 2 ^ (prefixWord ++ tailWord_6931104).sum := by decide
  have hdescent : baseEnd_6931104 < baseStart_6931104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931117 : List Nat := [1, 5, 2, 1, 1, 3, 1, 9]
def baseStart_6931117 : Nat := 118140960795 + 6931117 * 2 ^ 59
def prefixEnd_6931117 : Nat := 4983230072969 + 3 ^ 40 * 6931117 * 2
def baseEnd_6931117 : Nat := 131814610872187544687477

theorem tailTrace_6931117 : CollatzResearch.WordTrace tailWord_6931117 prefixEnd_6931117 131814610872187544687477 := by
  unfold tailWord_6931117
  simp only [CollatzResearch.WordTrace]
  refine ⟨252798605230754324386311605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168532403487169549590874403 252798605230754324386311605)
  ·
    refine ⟨23699869240383217911216713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 252798605230754324386311605 23699869240383217911216713)
    ·
      refine ⟨17774901930287413433412535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23699869240383217911216713 17774901930287413433412535)
      ·
        refine ⟨26662352895431120150118803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17774901930287413433412535 26662352895431120150118803)
        ·
          refine ⟨39993529343146680225178205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26662352895431120150118803 39993529343146680225178205)
          ·
            refine ⟨14997573503680005084441827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39993529343146680225178205 14997573503680005084441827)
            ·
              refine ⟨22496360255520007626662741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14997573503680005084441827 22496360255520007626662741)
              ·
                refine ⟨131814610872187544687477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22496360255520007626662741 131814610872187544687477)
                ·
                  rfl

theorem cell23_6931117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 9].length) (baseStart_6931117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931117 prefixEnd_6931117 := by exact prefixLift 6931117
  have htrace : WordTrace (prefixWord ++ tailWord_6931117) baseStart_6931117 baseEnd_6931117 := by
    simpa [prefixWord, tailWord_6931117, baseEnd_6931117] using wordTrace_append hprefix tailTrace_6931117
  have hstable : (prefixWord ++ tailWord_6931117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931117).length < 2 ^ (prefixWord ++ tailWord_6931117).sum := by decide
  have hdescent : baseEnd_6931117 < baseStart_6931117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931144 : List Nat := [2, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3]
def baseStart_6931144 : Nat := 118140960795 + 6931144 * 2 ^ 59
def prefixEnd_6931144 : Nat := 4983230072969 + 3 ^ 40 * 6931144 * 2
def baseEnd_6931144 : Nat := 3559008357526735100924255

theorem tailTrace_6931144 : CollatzResearch.WordTrace tailWord_6931144 prefixEnd_6931144 3559008357526735100924255 := by
  unfold tailWord_6931144
  simp only [CollatzResearch.WordTrace]
  refine ⟨126399795000828253998772243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168533060001104338665029657 126399795000828253998772243)
  ·
    refine ⟨189599692501242380998158365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126399795000828253998772243 189599692501242380998158365)
    ·
      refine ⟨71099884687965892874309387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189599692501242380998158365 71099884687965892874309387)
      ·
        refine ⟨106649827031948839311464081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71099884687965892874309387 106649827031948839311464081)
        ·
          refine ⟨79987370273961629483598061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106649827031948839311464081 79987370273961629483598061)
          ·
            refine ⟨29995263852735611056349273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79987370273961629483598061 29995263852735611056349273)
            ·
              refine ⟨22496447889551708292261955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29995263852735611056349273 22496447889551708292261955)
              ·
                refine ⟨33744671834327562438392933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22496447889551708292261955 33744671834327562438392933)
                ·
                  refine ⟨6327125968936417957198675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33744671834327562438392933 6327125968936417957198675)
                  ·
                    refine ⟨9490688953404626935798013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6327125968936417957198675 9490688953404626935798013)
                    ·
                      refine ⟨3559008357526735100924255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490688953404626935798013 3559008357526735100924255)
                      ·
                        rfl

theorem cell23_6931144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_6931144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931144 prefixEnd_6931144 := by exact prefixLift 6931144
  have htrace : WordTrace (prefixWord ++ tailWord_6931144) baseStart_6931144 baseEnd_6931144 := by
    simpa [prefixWord, tailWord_6931144, baseEnd_6931144] using wordTrace_append hprefix tailTrace_6931144
  have hstable : (prefixWord ++ tailWord_6931144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931144).length < 2 ^ (prefixWord ++ tailWord_6931144).sum := by decide
  have hdescent : baseEnd_6931144 < baseStart_6931144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931171 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 3, 3, 2]
def baseStart_6931171 : Nat := 118140960795 + 6931171 * 2 ^ 59
def prefixEnd_6931171 : Nat := 4983230072969 + 3 ^ 40 * 6931171 * 2
def baseEnd_6931171 : Nat := 3559022221504406495286631

theorem tailTrace_6931171 : CollatzResearch.WordTrace tailWord_6931171 prefixEnd_6931171 3559022221504406495286631 := by
  unfold tailWord_6931171
  simp only [CollatzResearch.WordTrace]
  refine ⟨252800574772558691608777367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168533716515039127739184911 252800574772558691608777367)
  ·
    refine ⟨379200862158838037413166051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252800574772558691608777367 379200862158838037413166051)
    ·
      refine ⟨568801293238257056119749077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379200862158838037413166051 568801293238257056119749077)
      ·
        refine ⟨13331280310271649752806619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 568801293238257056119749077 13331280310271649752806619)
        ·
          refine ⟨19996920465407474629209929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13331280310271649752806619 19996920465407474629209929)
          ·
            refine ⟨14997690349055605971907447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19996920465407474629209929 14997690349055605971907447)
            ·
              refine ⟨22496535523583408957861171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14997690349055605971907447 22496535523583408957861171)
              ·
                refine ⟨33744803285375113436791757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22496535523583408957861171 33744803285375113436791757)
                ·
                  refine ⟨12654301232015667538796909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33744803285375113436791757 12654301232015667538796909)
                  ·
                    refine ⟨4745362962005875327048841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12654301232015667538796909 4745362962005875327048841)
                    ·
                      refine ⟨3559022221504406495286631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745362962005875327048841 3559022221504406495286631)
                      ·
                        rfl

theorem cell23_6931171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_6931171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931171 prefixEnd_6931171 := by exact prefixLift 6931171
  have htrace : WordTrace (prefixWord ++ tailWord_6931171) baseStart_6931171 baseEnd_6931171 := by
    simpa [prefixWord, tailWord_6931171, baseEnd_6931171] using wordTrace_append hprefix tailTrace_6931171
  have hstable : (prefixWord ++ tailWord_6931171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931171).length < 2 ^ (prefixWord ++ tailWord_6931171).sum := by decide
  have hdescent : baseEnd_6931171 < baseStart_6931171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931184 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2]
def baseStart_6931184 : Nat := 118140960795 + 6931184 * 2 ^ 59
def prefixEnd_6931184 : Nat := 4983230072969 + 3 ^ 40 * 6931184 * 2
def baseEnd_6931184 : Nat := 3559028896752914944424071

theorem tailTrace_6931184 : CollatzResearch.WordTrace tailWord_6931184 prefixEnd_6931184 3559028896752914944424071 := by
  unfold tailWord_6931184
  simp only [CollatzResearch.WordTrace]
  refine ⟨126400524460755797414500303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168534032614341063219333737 126400524460755797414500303)
  ·
    refine ⟨189600786691133696121750455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126400524460755797414500303 189600786691133696121750455)
    ·
      refine ⟨284401180036700544182625683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189600786691133696121750455 284401180036700544182625683)
      ·
        refine ⟨426601770055050816273938525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284401180036700544182625683 426601770055050816273938525)
        ·
          refine ⟨159975663770644056102726947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426601770055050816273938525 159975663770644056102726947)
          ·
            refine ⟨239963495655966084154090421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159975663770644056102726947 239963495655966084154090421)
            ·
              refine ⟨22496577717746820389445977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 239963495655966084154090421 22496577717746820389445977)
              ·
                refine ⟨16872433288310115292084483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22496577717746820389445977 16872433288310115292084483)
                ·
                  refine ⟨25308649932465172938126725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16872433288310115292084483 25308649932465172938126725)
                  ·
                    refine ⟨4745371862337219925898761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25308649932465172938126725 4745371862337219925898761)
                    ·
                      refine ⟨3559028896752914944424071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745371862337219925898761 3559028896752914944424071)
                      ·
                        rfl

theorem cell23_6931184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 4, 2].length) (baseStart_6931184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931184 prefixEnd_6931184 := by exact prefixLift 6931184
  have htrace : WordTrace (prefixWord ++ tailWord_6931184) baseStart_6931184 baseEnd_6931184 := by
    simpa [prefixWord, tailWord_6931184, baseEnd_6931184] using wordTrace_append hprefix tailTrace_6931184
  have hstable : (prefixWord ++ tailWord_6931184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931184).length < 2 ^ (prefixWord ++ tailWord_6931184).sum := by decide
  have hdescent : baseEnd_6931184 < baseStart_6931184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931197 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_6931197 : Nat := 118140960795 + 6931197 * 2 ^ 59
def prefixEnd_6931197 : Nat := 4983230072969 + 3 ^ 40 * 6931197 * 2
def baseEnd_6931197 : Nat := 3559035572001423393561511

theorem tailTrace_6931197 : CollatzResearch.WordTrace tailWord_6931197 prefixEnd_6931197 3559035572001423393561511 := by
  unfold tailWord_6931197
  simp only [CollatzResearch.WordTrace]
  refine ⟨252801523070464498049223845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168534348713642998699482563 252801523070464498049223845)
  ·
    refine ⟨47400285575712093384229471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 252801523070464498049223845 47400285575712093384229471)
    ·
      refine ⟨71100428363568140076344207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47400285575712093384229471 71100428363568140076344207)
      ·
        refine ⟨106650642545352210114516311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71100428363568140076344207 106650642545352210114516311)
        ·
          refine ⟨159975963818028315171774467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106650642545352210114516311 159975963818028315171774467)
          ·
            refine ⟨239963945727042472757661701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159975963818028315171774467 239963945727042472757661701)
            ·
              refine ⟨44993239823820463642061569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 239963945727042472757661701 44993239823820463642061569)
              ·
                refine ⟨33744929867865347731546177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44993239823820463642061569 33744929867865347731546177)
                ·
                  refine ⟨25308697400899010798659633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33744929867865347731546177 25308697400899010798659633)
                  ·
                    refine ⟨18981523050674258098994725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25308697400899010798659633 18981523050674258098994725)
                    ·
                      refine ⟨3559035572001423393561511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18981523050674258098994725 3559035572001423393561511)
                      ·
                        rfl

theorem cell23_6931197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_6931197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931197 prefixEnd_6931197 := by exact prefixLift 6931197
  have htrace : WordTrace (prefixWord ++ tailWord_6931197) baseStart_6931197 baseEnd_6931197 := by
    simpa [prefixWord, tailWord_6931197, baseEnd_6931197] using wordTrace_append hprefix tailTrace_6931197
  have hstable : (prefixWord ++ tailWord_6931197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931197).length < 2 ^ (prefixWord ++ tailWord_6931197).sum := by decide
  have hdescent : baseEnd_6931197 < baseStart_6931197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931217 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_6931217 : Nat := 118140960795 + 6931217 * 2 ^ 59
def prefixEnd_6931217 : Nat := 4983230072969 + 3 ^ 40 * 6931217 * 2
def baseEnd_6931217 : Nat := 3559045841614513315311419

theorem tailTrace_6931217 : CollatzResearch.WordTrace tailWord_6931217 prefixEnd_6931217 3559045841614513315311419 := by
  unfold tailWord_6931217
  simp only [CollatzResearch.WordTrace]
  refine ⟨252802252530392041464951905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168534835020261360976634603 252802252530392041464951905)
  ·
    refine ⟨189601689397794031098713929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252802252530392041464951905 189601689397794031098713929)
    ·
      refine ⟨142201267048345523324035447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189601689397794031098713929 142201267048345523324035447)
      ·
        refine ⟨213301900572518284986053171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142201267048345523324035447 213301900572518284986053171)
        ·
          refine ⟨319952850858777427479079757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213301900572518284986053171 319952850858777427479079757)
          ·
            refine ⟨119982319072041535304654909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319952850858777427479079757 119982319072041535304654909)
            ·
              refine ⟨44993369652015575739245591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119982319072041535304654909 44993369652015575739245591)
              ·
                refine ⟨67490054478023363608868387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44993369652015575739245591 67490054478023363608868387)
                ·
                  refine ⟨101235081717035045413302581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67490054478023363608868387 101235081717035045413302581)
                  ·
                    refine ⟨9490788910972035507497117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101235081717035045413302581 9490788910972035507497117)
                    ·
                      refine ⟨3559045841614513315311419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9490788910972035507497117 3559045841614513315311419)
                      ·
                        rfl

theorem cell23_6931217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_6931217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931217 prefixEnd_6931217 := by exact prefixLift 6931217
  have htrace : WordTrace (prefixWord ++ tailWord_6931217) baseStart_6931217 baseEnd_6931217 := by
    simpa [prefixWord, tailWord_6931217, baseEnd_6931217] using wordTrace_append hprefix tailTrace_6931217
  have hstable : (prefixWord ++ tailWord_6931217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931217).length < 2 ^ (prefixWord ++ tailWord_6931217).sum := by decide
  have hdescent : baseEnd_6931217 < baseStart_6931217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931237 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_6931237 : Nat := 118140960795 + 6931237 * 2 ^ 59
def prefixEnd_6931237 : Nat := 4983230072969 + 3 ^ 40 * 6931237 * 2
def baseEnd_6931237 : Nat := 1186352037075867745687109

theorem tailTrace_6931237 : CollatzResearch.WordTrace tailWord_6931237 prefixEnd_6931237 1186352037075867745687109 := by
  unfold tailWord_6931237
  simp only [CollatzResearch.WordTrace]
  refine ⟨252802981990319584880679965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168535321326879723253786643 252802981990319584880679965)
  ·
    refine ⟨94801118246369844330254987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252802981990319584880679965 94801118246369844330254987)
    ·
      refine ⟨142201677369554766495382481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94801118246369844330254987 142201677369554766495382481)
      ·
        refine ⟨106651258027166074871536861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142201677369554766495382481 106651258027166074871536861)
        ·
          refine ⟨39994221760187278076826323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106651258027166074871536861 39994221760187278076826323)
          ·
            refine ⟨59991332640280917115239485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39994221760187278076826323 59991332640280917115239485)
            ·
              refine ⟨22496749740105343918214807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59991332640280917115239485 22496749740105343918214807)
              ·
                refine ⟨33745124610158015877322211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22496749740105343918214807 33745124610158015877322211)
                ·
                  refine ⟨50617686915237023815983317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33745124610158015877322211 50617686915237023815983317)
                  ·
                    refine ⟨1186352037075867745687109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50617686915237023815983317 1186352037075867745687109)
                    ·
                      rfl

theorem cell23_6931237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_6931237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931237 prefixEnd_6931237 := by exact prefixLift 6931237
  have htrace : WordTrace (prefixWord ++ tailWord_6931237) baseStart_6931237 baseEnd_6931237 := by
    simpa [prefixWord, tailWord_6931237, baseEnd_6931237] using wordTrace_append hprefix tailTrace_6931237
  have hstable : (prefixWord ++ tailWord_6931237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931237).length < 2 ^ (prefixWord ++ tailWord_6931237).sum := by decide
  have hdescent : baseEnd_6931237 < baseStart_6931237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931252 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_6931252 : Nat := 118140960795 + 6931252 * 2 ^ 59
def prefixEnd_6931252 : Nat := 4983230072969 + 3 ^ 40 * 6931252 * 2
def baseEnd_6931252 : Nat := 3559063813437420678373759

theorem tailTrace_6931252 : CollatzResearch.WordTrace tailWord_6931252 prefixEnd_6931252 3559063813437420678373759 := by
  unfold tailWord_6931252
  simp only [CollatzResearch.WordTrace]
  refine ⟨126401764542632621221238005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168535686056843494961650673 126401764542632621221238005)
  ·
    refine ⟨11850165425871808239491063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126401764542632621221238005 11850165425871808239491063)
    ·
      refine ⟨17775248138807712359236595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850165425871808239491063 17775248138807712359236595)
      ·
        refine ⟨26662872208211568538854893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17775248138807712359236595 26662872208211568538854893)
        ·
          refine ⟨9998577078079338202070585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26662872208211568538854893 9998577078079338202070585)
          ·
            refine ⟨7498932808559503651552939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998577078079338202070585 7498932808559503651552939)
            ·
              refine ⟨11248399212839255477329409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7498932808559503651552939 11248399212839255477329409)
              ·
                refine ⟨8436299409629441607997057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11248399212839255477329409 8436299409629441607997057)
                ·
                  refine ⟨6327224557222081205997793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436299409629441607997057 6327224557222081205997793)
                  ·
                    refine ⟨4745418417916560904498345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327224557222081205997793 4745418417916560904498345)
                    ·
                      refine ⟨3559063813437420678373759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745418417916560904498345 3559063813437420678373759)
                      ·
                        rfl

theorem cell23_6931252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_6931252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931252 prefixEnd_6931252 := by exact prefixLift 6931252
  have htrace : WordTrace (prefixWord ++ tailWord_6931252) baseStart_6931252 baseEnd_6931252 := by
    simpa [prefixWord, tailWord_6931252, baseEnd_6931252] using wordTrace_append hprefix tailTrace_6931252
  have hstable : (prefixWord ++ tailWord_6931252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931252).length < 2 ^ (prefixWord ++ tailWord_6931252).sum := by decide
  have hdescent : baseEnd_6931252 < baseStart_6931252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931274 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2]
def baseStart_6931274 : Nat := 118140960795 + 6931274 * 2 ^ 59
def prefixEnd_6931274 : Nat := 4983230072969 + 3 ^ 40 * 6931274 * 2
def baseEnd_6931274 : Nat := 3559075110011819592298657

theorem tailTrace_6931274 : CollatzResearch.WordTrace tailWord_6931274 prefixEnd_6931274 3559075110011819592298657 := by
  unfold tailWord_6931274
  simp only [CollatzResearch.WordTrace]
  refine ⟨63201082872796385049944219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168536220994123693466517917 63201082872796385049944219)
  ·
    refine ⟨94801624309194577574916329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63201082872796385049944219 94801624309194577574916329)
    ·
      refine ⟨71101218231895933181187247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94801624309194577574916329 71101218231895933181187247)
      ·
        refine ⟨106651827347843899771780871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71101218231895933181187247 106651827347843899771780871)
        ·
          refine ⟨159977741021765849657671307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106651827347843899771780871 159977741021765849657671307)
          ·
            refine ⟨239966611532648774486506961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 159977741021765849657671307 239966611532648774486506961)
            ·
              refine ⟨179974958649486580864880221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239966611532648774486506961 179974958649486580864880221)
              ·
                refine ⟨67490609493557467824330083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179974958649486580864880221 67490609493557467824330083)
                ·
                  refine ⟨101235914240336201736495125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67490609493557467824330083 101235914240336201736495125)
                  ·
                    refine ⟨4745433480015759456398209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101235914240336201736495125 4745433480015759456398209)
                    ·
                      refine ⟨3559075110011819592298657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745433480015759456398209 3559075110011819592298657)
                      ·
                        rfl

theorem cell23_6931274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2].length) (baseStart_6931274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931274 prefixEnd_6931274 := by exact prefixLift 6931274
  have htrace : WordTrace (prefixWord ++ tailWord_6931274) baseStart_6931274 baseEnd_6931274 := by
    simpa [prefixWord, tailWord_6931274, baseEnd_6931274] using wordTrace_append hprefix tailTrace_6931274
  have hstable : (prefixWord ++ tailWord_6931274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931274).length < 2 ^ (prefixWord ++ tailWord_6931274).sum := by decide
  have hdescent : baseEnd_6931274 < baseStart_6931274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931318 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_6931318 : Nat := 118140960795 + 6931318 * 2 ^ 59
def prefixEnd_6931318 : Nat := 4983230072969 + 3 ^ 40 * 6931318 * 2
def baseEnd_6931318 : Nat := 1186365901053539140049485

theorem tailTrace_6931318 : CollatzResearch.WordTrace tailWord_6931318 prefixEnd_6931318 1186365901053539140049485 := by
  unfold tailWord_6931318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800371018939133482148663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168537290868684090476252405 15800371018939133482148663)
  ·
    refine ⟨23700556528408700223222995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15800371018939133482148663 23700556528408700223222995)
    ·
      refine ⟨35550834792613050334834493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23700556528408700223222995 35550834792613050334834493)
      ·
        refine ⟨13331563047229893875562935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35550834792613050334834493 13331563047229893875562935)
        ·
          refine ⟨19997344570844840813344403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13331563047229893875562935 19997344570844840813344403)
          ·
            refine ⟨29996016856267261220016605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19997344570844840813344403 29996016856267261220016605)
            ·
              refine ⟨11248506321100222957506227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29996016856267261220016605 11248506321100222957506227)
              ·
                refine ⟨16872759481650334436259341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11248506321100222957506227 16872759481650334436259341)
                ·
                  refine ⟨6327284805618875413597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16872759481650334436259341 6327284805618875413597253)
                  ·
                    refine ⟨1186365901053539140049485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6327284805618875413597253 1186365901053539140049485)
                    ·
                      rfl

theorem cell23_6931318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_6931318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931318 prefixEnd_6931318 := by exact prefixLift 6931318
  have htrace : WordTrace (prefixWord ++ tailWord_6931318) baseStart_6931318 baseEnd_6931318 := by
    simpa [prefixWord, tailWord_6931318, baseEnd_6931318] using wordTrace_append hprefix tailTrace_6931318
  have hstable : (prefixWord ++ tailWord_6931318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931318).length < 2 ^ (prefixWord ++ tailWord_6931318).sum := by decide
  have hdescent : baseEnd_6931318 < baseStart_6931318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931418 : List Nat := [3, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3]
def baseStart_6931418 : Nat := 118140960795 + 6931418 * 2 ^ 59
def prefixEnd_6931418 : Nat := 4983230072969 + 3 ^ 40 * 6931418 * 2
def baseEnd_6931418 : Nat := 3559149051226067028897995

theorem tailTrace_6931418 : CollatzResearch.WordTrace tailWord_6931418 prefixEnd_6931418 3559149051226067028897995 := by
  unfold tailWord_6931418
  simp only [CollatzResearch.WordTrace]
  refine ⟨63202395900665963198254727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168539722401775901862012605 63202395900665963198254727)
  ·
    refine ⟨94803593850998944797382091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63202395900665963198254727 94803593850998944797382091)
    ·
      refine ⟨142205390776498417196073137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94803593850998944797382091 142205390776498417196073137)
      ·
        refine ⟨106654043082373812897054853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142205390776498417196073137 106654043082373812897054853)
        ·
          refine ⟨19997633077945089918197785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106654043082373812897054853 19997633077945089918197785)
          ·
            refine ⟨14998224808458817438648339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19997633077945089918197785 14998224808458817438648339)
            ·
              refine ⟨22497337212688226157972509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14998224808458817438648339 22497337212688226157972509)
              ·
                refine ⟨8436501454758084809239691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22497337212688226157972509 8436501454758084809239691)
                ·
                  refine ⟨12654752182137127213859537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8436501454758084809239691 12654752182137127213859537)
                  ·
                    refine ⟨9491064136602845410394653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12654752182137127213859537 9491064136602845410394653)
                    ·
                      refine ⟨3559149051226067028897995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9491064136602845410394653 3559149051226067028897995)
                      ·
                        rfl

theorem cell23_6931418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_6931418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931418 prefixEnd_6931418 := by exact prefixLift 6931418
  have htrace : WordTrace (prefixWord ++ tailWord_6931418) baseStart_6931418 baseEnd_6931418 := by
    simpa [prefixWord, tailWord_6931418, baseEnd_6931418] using wordTrace_append hprefix tailTrace_6931418
  have hstable : (prefixWord ++ tailWord_6931418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931418).length < 2 ^ (prefixWord ++ tailWord_6931418).sum := by decide
  have hdescent : baseEnd_6931418 < baseStart_6931418 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931442 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_6931442 : Nat := 118140960795 + 6931442 * 2 ^ 59
def prefixEnd_6931442 : Nat := 4983230072969 + 3 ^ 40 * 6931442 * 2
def baseEnd_6931442 : Nat := 1186387124920591644999295

theorem tailTrace_6931442 : CollatzResearch.WordTrace tailWord_6931442 prefixEnd_6931442 1186387124920591644999295 := by
  unfold tailWord_6931442
  simp only [CollatzResearch.WordTrace]
  refine ⟨63202614738644226222973145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168540305969717936594595053 63202614738644226222973145)
  ·
    refine ⟨47401961053983169667229859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63202614738644226222973145 47401961053983169667229859)
    ·
      refine ⟨71102941580974754500844789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47401961053983169667229859 71102941580974754500844789)
      ·
        refine ⟨6665900773216383234454199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71102941580974754500844789 6665900773216383234454199)
        ·
          refine ⟨9998851159824574851681299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6665900773216383234454199 9998851159824574851681299)
          ·
            refine ⟨14998276739736862277521949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9998851159824574851681299 14998276739736862277521949)
            ·
              refine ⟨5624353777401323354070731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14998276739736862277521949 5624353777401323354070731)
              ·
                refine ⟨8436530666101985031106097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5624353777401323354070731 8436530666101985031106097)
                ·
                  refine ⟨6327397999576488773329573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436530666101985031106097 6327397999576488773329573)
                  ·
                    refine ⟨1186387124920591644999295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6327397999576488773329573 1186387124920591644999295)
                    ·
                      rfl

theorem cell23_6931442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_6931442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931442 prefixEnd_6931442 := by exact prefixLift 6931442
  have htrace : WordTrace (prefixWord ++ tailWord_6931442) baseStart_6931442 baseEnd_6931442 := by
    simpa [prefixWord, tailWord_6931442, baseEnd_6931442] using wordTrace_append hprefix tailTrace_6931442
  have hstable : (prefixWord ++ tailWord_6931442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931442).length < 2 ^ (prefixWord ++ tailWord_6931442).sum := by decide
  have hdescent : baseEnd_6931442 < baseStart_6931442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931505 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 2, 2, 2]
def baseStart_6931505 : Nat := 118140960795 + 6931505 * 2 ^ 59
def prefixEnd_6931505 : Nat := 4983230072969 + 3 ^ 40 * 6931505 * 2
def baseEnd_6931505 : Nat := 3559193724043008188510095

theorem tailTrace_6931505 : CollatzResearch.WordTrace tailWord_6931505 prefixEnd_6931505 3559193724043008188510095 := by
  unfold tailWord_6931505
  simp only [CollatzResearch.WordTrace]
  refine ⟨252812756753348666651435969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168541837835565777767623979 252812756753348666651435969)
  ·
    refine ⟨189609567565011499988576977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252812756753348666651435969 189609567565011499988576977)
    ·
      refine ⟨142207175673758624991432733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189609567565011499988576977 142207175673758624991432733)
      ·
        refine ⟨53327690877659484371787275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142207175673758624991432733 53327690877659484371787275)
        ·
          refine ⟨79991536316489226557680913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53327690877659484371787275 79991536316489226557680913)
          ·
            refine ⟨59993652237366919918260685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79991536316489226557680913 59993652237366919918260685)
            ·
              refine ⟨22497619589012594969347757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59993652237366919918260685 22497619589012594969347757)
              ·
                refine ⟨8436607345879723113505409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22497619589012594969347757 8436607345879723113505409)
                ·
                  refine ⟨6327455509409792335129057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8436607345879723113505409 6327455509409792335129057)
                  ·
                    refine ⟨4745591632057344251346793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6327455509409792335129057 4745591632057344251346793)
                    ·
                      refine ⟨3559193724043008188510095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745591632057344251346793 3559193724043008188510095)
                      ·
                        rfl

theorem cell23_6931505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2, 2].length) (baseStart_6931505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931505 prefixEnd_6931505 := by exact prefixLift 6931505
  have htrace : WordTrace (prefixWord ++ tailWord_6931505) baseStart_6931505 baseEnd_6931505 := by
    simpa [prefixWord, tailWord_6931505, baseEnd_6931505] using wordTrace_append hprefix tailTrace_6931505
  have hstable : (prefixWord ++ tailWord_6931505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931505).length < 2 ^ (prefixWord ++ tailWord_6931505).sum := by decide
  have hdescent : baseEnd_6931505 < baseStart_6931505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931508 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_6931508 : Nat := 118140960795 + 6931508 * 2 ^ 59
def prefixEnd_6931508 : Nat := 4983230072969 + 3 ^ 40 * 6931508 * 2
def baseEnd_6931508 : Nat := 3559195264484971676772581

theorem tailTrace_6931508 : CollatzResearch.WordTrace tailWord_6931508 prefixEnd_6931508 3559195264484971676772581 := by
  unfold tailWord_6931508
  simp only [CollatzResearch.WordTrace]
  refine ⟨126406433086168899081897589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168541910781558532109196785 126406433086168899081897589)
  ·
    refine ⟨11850603101828334288927899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126406433086168899081897589 11850603101828334288927899)
    ·
      refine ⟨17775904652742501433391849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11850603101828334288927899 17775904652742501433391849)
      ·
        refine ⟨13331928489556876075043887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17775904652742501433391849 13331928489556876075043887)
        ·
          refine ⟨19997892734335314112565831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13331928489556876075043887 19997892734335314112565831)
          ·
            refine ⟨29996839101502971168848747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19997892734335314112565831 29996839101502971168848747)
            ·
              refine ⟨44995258652254456753273121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29996839101502971168848747 44995258652254456753273121)
              ·
                refine ⟨33746443989190842564954841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44995258652254456753273121 33746443989190842564954841)
                ·
                  refine ⟨25309832991893131923716131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33746443989190842564954841 25309832991893131923716131)
                  ·
                    refine ⟨37964749487839697885574197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25309832991893131923716131 37964749487839697885574197)
                    ·
                      refine ⟨3559195264484971676772581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37964749487839697885574197 3559195264484971676772581)
                      ·
                        rfl

theorem cell23_6931508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_6931508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931508 prefixEnd_6931508 := by exact prefixLift 6931508
  have htrace : WordTrace (prefixWord ++ tailWord_6931508) baseStart_6931508 baseEnd_6931508 := by
    simpa [prefixWord, tailWord_6931508, baseEnd_6931508] using wordTrace_append hprefix tailTrace_6931508
  have hstable : (prefixWord ++ tailWord_6931508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931508).length < 2 ^ (prefixWord ++ tailWord_6931508).sum := by decide
  have hdescent : baseEnd_6931508 < baseStart_6931508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931531 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 7, 2]
def baseStart_6931531 : Nat := 118140960795 + 6931531 * 2 ^ 59
def prefixEnd_6931531 : Nat := 4983230072969 + 3 ^ 40 * 6931531 * 2
def baseEnd_6931531 : Nat := 3559207074540025086784975

theorem tailTrace_6931531 : CollatzResearch.WordTrace tailWord_6931531 prefixEnd_6931531 3559207074540025086784975 := by
  unfold tailWord_6931531
  simp only [CollatzResearch.WordTrace]
  refine ⟨252813705051254473091882447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168542470034169648727921631 252813705051254473091882447)
  ·
    refine ⟨379220557576881709637823671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252813705051254473091882447 379220557576881709637823671)
    ·
      refine ⟨568830836365322564456735507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379220557576881709637823671 568830836365322564456735507)
      ·
        refine ⟨853246254547983846685103261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568830836365322564456735507 853246254547983846685103261)
        ·
          refine ⟨319967345455493942506913723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 853246254547983846685103261 319967345455493942506913723)
          ·
            refine ⟨479951018183240913760370585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319967345455493942506913723 479951018183240913760370585)
            ·
              refine ⟨359963263637430685320277939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 479951018183240913760370585 359963263637430685320277939)
              ·
                refine ⟨539944895456146027980416909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359963263637430685320277939 539944895456146027980416909)
                ·
                  refine ⟨202479335796054760492656341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539944895456146027980416909 202479335796054760492656341)
                  ·
                    refine ⟨4745609432720033449046633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202479335796054760492656341 4745609432720033449046633)
                    ·
                      refine ⟨3559207074540025086784975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745609432720033449046633 3559207074540025086784975)
                      ·
                        rfl

theorem cell23_6931531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 7, 2].length) (baseStart_6931531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931531 prefixEnd_6931531 := by exact prefixLift 6931531
  have htrace : WordTrace (prefixWord ++ tailWord_6931531) baseStart_6931531 baseEnd_6931531 := by
    simpa [prefixWord, tailWord_6931531, baseEnd_6931531] using wordTrace_append hprefix tailTrace_6931531
  have hstable : (prefixWord ++ tailWord_6931531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931531).length < 2 ^ (prefixWord ++ tailWord_6931531).sum := by decide
  have hdescent : baseEnd_6931531 < baseStart_6931531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931541 : List Nat := [1, 3, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_6931541 : Nat := 118140960795 + 6931541 * 2 ^ 59
def prefixEnd_6931541 : Nat := 4983230072969 + 3 ^ 40 * 6931541 * 2
def baseEnd_6931541 : Nat := 1186404069782190015886643

theorem tailTrace_6931541 : CollatzResearch.WordTrace tailWord_6931541 prefixEnd_6931541 1186404069782190015886643 := by
  unfold tailWord_6931541
  simp only [CollatzResearch.WordTrace]
  refine ⟨252814069781218244799746477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168542713187478829866497651 252814069781218244799746477)
  ·
    refine ⟨94805276167956841799904929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252814069781218244799746477 94805276167956841799904929)
    ·
      refine ⟨71103957125967631349928697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94805276167956841799904929 71103957125967631349928697)
      ·
        refine ⟨53327967844475723512446523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71103957125967631349928697 53327967844475723512446523)
        ·
          refine ⟨79991951766713585268669785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53327967844475723512446523 79991951766713585268669785)
          ·
            refine ⟨59993963825035188951502339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79991951766713585268669785 59993963825035188951502339)
            ·
              refine ⟨89990945737552783427253509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59993963825035188951502339 89990945737552783427253509)
              ·
                refine ⟨16873302325791146892610033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89990945737552783427253509 16873302325791146892610033)
                ·
                  refine ⟨12654976744343360169457525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16873302325791146892610033 12654976744343360169457525)
                  ·
                    refine ⟨1186404069782190015886643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12654976744343360169457525 1186404069782190015886643)
                    ·
                      rfl

theorem cell23_6931541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_6931541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931541 prefixEnd_6931541 := by exact prefixLift 6931541
  have htrace : WordTrace (prefixWord ++ tailWord_6931541) baseStart_6931541 baseEnd_6931541 := by
    simpa [prefixWord, tailWord_6931541, baseEnd_6931541] using wordTrace_append hprefix tailTrace_6931541
  have hstable : (prefixWord ++ tailWord_6931541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931541).length < 2 ^ (prefixWord ++ tailWord_6931541).sum := by decide
  have hdescent : baseEnd_6931541 < baseStart_6931541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931548 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6931548 : Nat := 118140960795 + 6931548 * 2 ^ 59
def prefixEnd_6931548 : Nat := 4983230072969 + 3 ^ 40 * 6931548 * 2
def baseEnd_6931548 : Nat := 3559215803711151520272397

theorem tailTrace_6931548 : CollatzResearch.WordTrace tailWord_6931548 prefixEnd_6931548 3559215803711151520272397 := by
  unfold tailWord_6931548
  simp only [CollatzResearch.WordTrace]
  refine ⟨126407162546096442497625649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168542883394795256663500865 126407162546096442497625649)
  ·
    refine ⟨94805371909572331873219237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126407162546096442497625649 94805371909572331873219237)
    ·
      refine ⟨17776007233044812226228607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94805371909572331873219237 17776007233044812226228607)
      ·
        refine ⟨26664010849567218339342911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17776007233044812226228607 26664010849567218339342911)
        ·
          refine ⟨39996016274350827509014367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26664010849567218339342911 39996016274350827509014367)
          ·
            refine ⟨59994024411526241263521551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39996016274350827509014367 59994024411526241263521551)
            ·
              refine ⟨89991036617289361895282327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59994024411526241263521551 89991036617289361895282327)
              ·
                refine ⟨134986554925934042842923491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89991036617289361895282327 134986554925934042842923491)
                ·
                  refine ⟨202479832388901064264385237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134986554925934042842923491 202479832388901064264385237)
                  ·
                    refine ⟨4745621071614868693696529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202479832388901064264385237 4745621071614868693696529)
                    ·
                      refine ⟨3559215803711151520272397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745621071614868693696529 3559215803711151520272397)
                      ·
                        rfl

theorem cell23_6931548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6931548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931548 prefixEnd_6931548 := by exact prefixLift 6931548
  have htrace : WordTrace (prefixWord ++ tailWord_6931548) baseStart_6931548 baseEnd_6931548 := by
    simpa [prefixWord, tailWord_6931548, baseEnd_6931548] using wordTrace_append hprefix tailTrace_6931548
  have hstable : (prefixWord ++ tailWord_6931548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931548).length < 2 ^ (prefixWord ++ tailWord_6931548).sum := by decide
  have hdescent : baseEnd_6931548 < baseStart_6931548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931628 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_6931628 : Nat := 118140960795 + 6931628 * 2 ^ 59
def prefixEnd_6931628 : Nat := 4983230072969 + 3 ^ 40 * 6931628 * 2
def baseEnd_6931628 : Nat := 3559256882163511207272029

theorem tailTrace_6931628 : CollatzResearch.WordTrace tailWord_6931628 prefixEnd_6931628 3559256882163511207272029 := by
  unfold tailWord_6931628
  simp only [CollatzResearch.WordTrace]
  refine ⟨126408621465951529329081769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168544828621268705772109025 126408621465951529329081769)
  ·
    refine ⟨94806466099463646996811327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126408621465951529329081769 94806466099463646996811327)
    ·
      refine ⟨142209699149195470495216991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94806466099463646996811327 142209699149195470495216991)
      ·
        refine ⟨213314548723793205742825487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142209699149195470495216991 213314548723793205742825487)
        ·
          refine ⟨319971823085689808614238231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213314548723793205742825487 319971823085689808614238231)
          ·
            refine ⟨479957734628534712921357347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 319971823085689808614238231 479957734628534712921357347)
            ·
              refine ⟨719936601942802069382036021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 479957734628534712921357347 719936601942802069382036021)
              ·
                refine ⟨67494056432137694004565877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 719936601942802069382036021 67494056432137694004565877)
                ·
                  refine ⟨6327567790512908812928051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67494056432137694004565877 6327567790512908812928051)
                  ·
                    refine ⟨9491351685769363219392077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6327567790512908812928051 9491351685769363219392077)
                    ·
                      refine ⟨3559256882163511207272029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9491351685769363219392077 3559256882163511207272029)
                      ·
                        rfl

theorem cell23_6931628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_6931628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931628 prefixEnd_6931628 := by exact prefixLift 6931628
  have htrace : WordTrace (prefixWord ++ tailWord_6931628) baseStart_6931628 baseEnd_6931628 := by
    simpa [prefixWord, tailWord_6931628, baseEnd_6931628] using wordTrace_append hprefix tailTrace_6931628
  have hstable : (prefixWord ++ tailWord_6931628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931628).length < 2 ^ (prefixWord ++ tailWord_6931628).sum := by decide
  have hdescent : baseEnd_6931628 < baseStart_6931628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931631 : List Nat := [1, 1, 2, 1, 2, 3, 2, 3, 3, 5]
def baseStart_6931631 : Nat := 118140960795 + 6931631 * 2 ^ 59
def prefixEnd_6931631 : Nat := 4983230072969 + 3 ^ 40 * 6931631 * 2
def baseEnd_6931631 : Nat := 1186419474201824898511505

theorem tailTrace_6931631 : CollatzResearch.WordTrace tailWord_6931631 prefixEnd_6931631 1186419474201824898511505 := by
  unfold tailWord_6931631
  simp only [CollatzResearch.WordTrace]
  refine ⟨252817352350892190170522747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168544901567261460113681831 252817352350892190170522747)
  ·
    refine ⟨379226028526338285255784121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252817352350892190170522747 379226028526338285255784121)
    ·
      refine ⟨284419521394753713941838091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379226028526338285255784121 284419521394753713941838091)
      ·
        refine ⟨426629282092130570912757137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284419521394753713941838091 426629282092130570912757137)
        ·
          refine ⟨319971961569097928184567853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 426629282092130570912757137 319971961569097928184567853)
          ·
            refine ⟨119989485588411723069212945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 319971961569097928184567853 119989485588411723069212945)
            ·
              refine ⟨89992114191308792301909709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119989485588411723069212945 89992114191308792301909709)
              ·
                refine ⟨33747042821740797113216141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89992114191308792301909709 33747042821740797113216141)
                ·
                  refine ⟨12655141058152798917456053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33747042821740797113216141 12655141058152798917456053)
                  ·
                    refine ⟨1186419474201824898511505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12655141058152798917456053 1186419474201824898511505)
                    ·
                      rfl

theorem cell23_6931631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_6931631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931631 prefixEnd_6931631 := by exact prefixLift 6931631
  have htrace : WordTrace (prefixWord ++ tailWord_6931631) baseStart_6931631 baseEnd_6931631 := by
    simpa [prefixWord, tailWord_6931631, baseEnd_6931631] using wordTrace_append hprefix tailTrace_6931631
  have hstable : (prefixWord ++ tailWord_6931631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931631).length < 2 ^ (prefixWord ++ tailWord_6931631).sum := by decide
  have hdescent : baseEnd_6931631 < baseStart_6931631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931685 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 4]
def baseStart_6931685 : Nat := 118140960795 + 6931685 * 2 ^ 59
def prefixEnd_6931685 : Nat := 4983230072969 + 3 ^ 40 * 6931685 * 2
def baseEnd_6931685 : Nat := 3559286150560817484259267

theorem tailTrace_6931685 : CollatzResearch.WordTrace tailWord_6931685 prefixEnd_6931685 3559286150560817484259267 := by
  unfold tailWord_6931685
  simp only [CollatzResearch.WordTrace]
  refine ⟨252819321892696557392988509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168546214595131038261992339 252819321892696557392988509)
  ·
    refine ⟨94807245709761209022370691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 252819321892696557392988509 94807245709761209022370691)
    ·
      refine ⟨142210868564641813533556037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94807245709761209022370691 142210868564641813533556037)
      ·
        refine ⟨26664537855870340037541757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142210868564641813533556037 26664537855870340037541757)
        ·
          refine ⟨9999201695951377514078159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26664537855870340037541757 9999201695951377514078159)
          ·
            refine ⟨14998802543927066271117239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9999201695951377514078159 14998802543927066271117239)
            ·
              refine ⟨22498203815890599406675859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14998802543927066271117239 22498203815890599406675859)
              ·
                refine ⟨33747305723835899110013789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22498203815890599406675859 33747305723835899110013789)
                ·
                  refine ⟨12655239646438462166255171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33747305723835899110013789 12655239646438462166255171)
                  ·
                    refine ⟨18982859469657693249382757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12655239646438462166255171 18982859469657693249382757)
                    ·
                      refine ⟨3559286150560817484259267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18982859469657693249382757 3559286150560817484259267)
                      ·
                        rfl

theorem cell23_6931685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_6931685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931685 prefixEnd_6931685 := by exact prefixLift 6931685
  have htrace : WordTrace (prefixWord ++ tailWord_6931685) baseStart_6931685 baseEnd_6931685 := by
    simpa [prefixWord, tailWord_6931685, baseEnd_6931685] using wordTrace_append hprefix tailTrace_6931685
  have hstable : (prefixWord ++ tailWord_6931685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931685).length < 2 ^ (prefixWord ++ tailWord_6931685).sum := by decide
  have hdescent : baseEnd_6931685 < baseStart_6931685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931691 : List Nat := [1, 1, 1, 1, 2, 6, 2, 9]
def baseStart_6931691 : Nat := 118140960795 + 6931691 * 2 ^ 59
def prefixEnd_6931691 : Nat := 4983230072969 + 3 ^ 40 * 6931691 * 2
def baseEnd_6931691 : Nat := 131825527090546091140157

theorem tailTrace_6931691 : CollatzResearch.WordTrace tailWord_6931691 prefixEnd_6931691 131825527090546091140157 := by
  unfold tailWord_6931691
  simp only [CollatzResearch.WordTrace]
  refine ⟨252819540730674820417706927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168546360487116546945137951 252819540730674820417706927)
  ·
    refine ⟨379229311096012230626560391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252819540730674820417706927 379229311096012230626560391)
    ·
      refine ⟨568843966644018345939840587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379229311096012230626560391 568843966644018345939840587)
      ·
        refine ⟨853265949966027518909760881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568843966644018345939840587 853265949966027518909760881)
        ·
          refine ⟨639949462474520639182320661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 853265949966027518909760881 639949462474520639182320661)
          ·
            refine ⟨29997631053493154961671281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 639949462474520639182320661 29997631053493154961671281)
            ·
              refine ⟨22498223290119866221253461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29997631053493154961671281 22498223290119866221253461)
              ·
                refine ⟨131825527090546091140157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22498223290119866221253461 131825527090546091140157)
                ·
                  rfl

theorem cell23_6931691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 9].length) (baseStart_6931691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931691 prefixEnd_6931691 := by exact prefixLift 6931691
  have htrace : WordTrace (prefixWord ++ tailWord_6931691) baseStart_6931691 baseEnd_6931691 := by
    simpa [prefixWord, tailWord_6931691, baseEnd_6931691] using wordTrace_append hprefix tailTrace_6931691
  have hstable : (prefixWord ++ tailWord_6931691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931691).length < 2 ^ (prefixWord ++ tailWord_6931691).sum := by decide
  have hdescent : baseEnd_6931691 < baseStart_6931691 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931708 : List Nat := [2, 2, 2, 1, 6, 10]
def baseStart_6931708 : Nat := 118140960795 + 6931708 * 2 ^ 59
def prefixEnd_6931708 : Nat := 4983230072969 + 3 ^ 40 * 6931708 * 2
def baseEnd_6931708 : Nat := 14647316710353378165727

theorem tailTrace_6931708 : CollatzResearch.WordTrace tailWord_6931708 prefixEnd_6931708 14647316710353378165727 := by
  unfold tailWord_6931708
  simp only [CollatzResearch.WordTrace]
  refine ⟨126410080385806616160537889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168546773847742154880717185 126410080385806616160537889)
  ·
    refine ⟨94807560289354962120403417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126410080385806616160537889 94807560289354962120403417)
    ·
      refine ⟨71105670217016221590302563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94807560289354962120403417 71105670217016221590302563)
      ·
        refine ⟨106658505325524332385453845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71105670217016221590302563 106658505325524332385453845)
        ·
          refine ⟨4999617437133953080568149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106658505325524332385453845 4999617437133953080568149)
          ·
            refine ⟨14647316710353378165727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4999617437133953080568149 14647316710353378165727)
            ·
              rfl

theorem cell23_6931708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 10].length) (baseStart_6931708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931708 prefixEnd_6931708 := by exact prefixLift 6931708
  have htrace : WordTrace (prefixWord ++ tailWord_6931708) baseStart_6931708 baseEnd_6931708 := by
    simpa [prefixWord, tailWord_6931708, baseEnd_6931708] using wordTrace_append hprefix tailTrace_6931708
  have hstable : (prefixWord ++ tailWord_6931708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931708).length < 2 ^ (prefixWord ++ tailWord_6931708).sum := by decide
  have hdescent : baseEnd_6931708 < baseStart_6931708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931721 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_6931721 : Nat := 118140960795 + 6931721 * 2 ^ 59
def prefixEnd_6931721 : Nat := 4983230072969 + 3 ^ 40 * 6931721 * 2
def baseEnd_6931721 : Nat := 1186434878621459781136367

theorem tailTrace_6931721 : CollatzResearch.WordTrace tailWord_6931721 prefixEnd_6931721 1186434878621459781136367 := by
  unfold tailWord_6931721
  simp only [CollatzResearch.WordTrace]
  refine ⟨252820634920566135541299017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168547089947044090360866011 252820634920566135541299017)
  ·
    refine ⟨189615476190424601655974263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 252820634920566135541299017 189615476190424601655974263)
    ·
      refine ⟨284423214285636902483961395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189615476190424601655974263 284423214285636902483961395)
      ·
        refine ⟨426634821428455353725942093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284423214285636902483961395 426634821428455353725942093)
        ·
          refine ⟨159988058035670757647228285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 426634821428455353725942093 159988058035670757647228285)
          ·
            refine ⟨59995521763376534117710607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 159988058035670757647228285 59995521763376534117710607)
            ·
              refine ⟨89993282645064801176565911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59995521763376534117710607 89993282645064801176565911)
              ·
                refine ⟨134989923967597201764848867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89993282645064801176565911 134989923967597201764848867)
                ·
                  refine ⟨202484885951395802647273301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134989923967597201764848867 202484885951395802647273301)
                  ·
                    refine ⟨1186434878621459781136367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 202484885951395802647273301 1186434878621459781136367)
                    ·
                      rfl

theorem cell23_6931721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_6931721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931721 prefixEnd_6931721 := by exact prefixLift 6931721
  have htrace : WordTrace (prefixWord ++ tailWord_6931721) baseStart_6931721 baseEnd_6931721 := by
    simpa [prefixWord, tailWord_6931721, baseEnd_6931721] using wordTrace_append hprefix tailTrace_6931721
  have hstable : (prefixWord ++ tailWord_6931721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931721).length < 2 ^ (prefixWord ++ tailWord_6931721).sum := by decide
  have hdescent : baseEnd_6931721 < baseStart_6931721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931731 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_6931731 : Nat := 118140960795 + 6931731 * 2 ^ 59
def prefixEnd_6931731 : Nat := 4983230072969 + 3 ^ 40 * 6931731 * 2
def baseEnd_6931731 : Nat := 3559309770670924304284055

theorem tailTrace_6931731 : CollatzResearch.WordTrace tailWord_6931731 prefixEnd_6931731 3559309770670924304284055 := by
  unfold tailWord_6931731
  simp only [CollatzResearch.WordTrace]
  refine ⟨252820999650529907249163047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168547333100353271499442031 252820999650529907249163047)
  ·
    refine ⟨379231499475794860873744571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252820999650529907249163047 379231499475794860873744571)
    ·
      refine ⟨568847249213692291310616857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379231499475794860873744571 568847249213692291310616857)
      ·
        refine ⟨426635436910269218482962643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 568847249213692291310616857 426635436910269218482962643)
        ·
          refine ⟨639953155365403827724443965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 426635436910269218482962643 639953155365403827724443965)
          ·
            refine ⟨239982433262026435396666487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 639953155365403827724443965 239982433262026435396666487)
            ·
              refine ⟨359973649893039653094999731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 239982433262026435396666487 359973649893039653094999731)
              ·
                refine ⟨539960474839559479642499597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 359973649893039653094999731 539960474839559479642499597)
                ·
                  refine ⟨202485178064834804865937349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 539960474839559479642499597 202485178064834804865937349)
                  ·
                    refine ⟨37965970887156525912363253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 202485178064834804865937349 37965970887156525912363253)
                    ·
                      refine ⟨3559309770670924304284055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37965970887156525912363253 3559309770670924304284055)
                      ·
                        rfl

theorem cell23_6931731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_6931731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931731 prefixEnd_6931731 := by exact prefixLift 6931731
  have htrace : WordTrace (prefixWord ++ tailWord_6931731) baseStart_6931731 baseEnd_6931731 := by
    simpa [prefixWord, tailWord_6931731, baseEnd_6931731] using wordTrace_append hprefix tailTrace_6931731
  have hstable : (prefixWord ++ tailWord_6931731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931731).length < 2 ^ (prefixWord ++ tailWord_6931731).sum := by decide
  have hdescent : baseEnd_6931731 < baseStart_6931731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931735 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_6931735 : Nat := 118140960795 + 6931735 * 2 ^ 59
def prefixEnd_6931735 : Nat := 4983230072969 + 3 ^ 40 * 6931735 * 2
def baseEnd_6931735 : Nat := 3559311824593542288634037

theorem tailTrace_6931735 : CollatzResearch.WordTrace tailWord_6931735 prefixEnd_6931735 3559311824593542288634037 := by
  unfold tailWord_6931735
  simp only [CollatzResearch.WordTrace]
  refine ⟨252821145542515415932308659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168547430361676943954872439 252821145542515415932308659)
  ·
    refine ⟨379231718313773123898462989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252821145542515415932308659 379231718313773123898462989)
    ·
      refine ⟨142211894367664921461923621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379231718313773123898462989 142211894367664921461923621)
      ·
        refine ⟨26664730193937172774110679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142211894367664921461923621 26664730193937172774110679)
        ·
          refine ⟨39997095290905759161166019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26664730193937172774110679 39997095290905759161166019)
          ·
            refine ⟨59995642936358638741749029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39997095290905759161166019 59995642936358638741749029)
            ·
              refine ⟨11249183050567244764077943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59995642936358638741749029 11249183050567244764077943)
              ·
                refine ⟨16873774575850867146116915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11249183050567244764077943 16873774575850867146116915)
                ·
                  refine ⟨25310661863776300719175373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16873774575850867146116915 25310661863776300719175373)
                  ·
                    refine ⟨9491498198916112769690765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25310661863776300719175373 9491498198916112769690765)
                    ·
                      refine ⟨3559311824593542288634037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9491498198916112769690765 3559311824593542288634037)
                      ·
                        rfl

theorem cell23_6931735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_6931735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931735 prefixEnd_6931735 := by exact prefixLift 6931735
  have htrace : WordTrace (prefixWord ++ tailWord_6931735) baseStart_6931735 baseEnd_6931735 := by
    simpa [prefixWord, tailWord_6931735, baseEnd_6931735] using wordTrace_append hprefix tailTrace_6931735
  have hstable : (prefixWord ++ tailWord_6931735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931735).length < 2 ^ (prefixWord ++ tailWord_6931735).sum := by decide
  have hdescent : baseEnd_6931735 < baseStart_6931735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931748 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 2, 2, 5]
def baseStart_6931748 : Nat := 118140960795 + 6931748 * 2 ^ 59
def prefixEnd_6931748 : Nat := 4983230072969 + 3 ^ 40 * 6931748 * 2
def baseEnd_6931748 : Nat := 3559318499842050737771477

theorem tailTrace_6931748 : CollatzResearch.WordTrace tailWord_6931748 prefixEnd_6931748 3559318499842050737771477 := by
  unfold tailWord_6931748
  simp only [CollatzResearch.WordTrace]
  refine ⟨126410809845734159576265949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168547746460978879435021265 126410809845734159576265949)
  ·
    refine ⟨47404053692150309841099731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126410809845734159576265949 47404053692150309841099731)
    ·
      refine ⟨71106080538225464761649597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47404053692150309841099731 71106080538225464761649597)
      ·
        refine ⟨26664780201834549285618599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71106080538225464761649597 26664780201834549285618599)
        ·
          refine ⟨39997170302751823928427899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26664780201834549285618599 39997170302751823928427899)
          ·
            refine ⟨59995755454127735892641849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39997170302751823928427899 59995755454127735892641849)
            ·
              refine ⟨44996816590595801919481387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59995755454127735892641849 44996816590595801919481387)
              ·
                refine ⟨67495224885893702879222081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44996816590595801919481387 67495224885893702879222081)
                ·
                  refine ⟨50621418664420277159416561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67495224885893702879222081 50621418664420277159416561)
                  ·
                    refine ⟨37966063998315207869562421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50621418664420277159416561 37966063998315207869562421)
                    ·
                      refine ⟨3559318499842050737771477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37966063998315207869562421 3559318499842050737771477)
                      ·
                        rfl

theorem cell23_6931748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_6931748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931748 prefixEnd_6931748 := by exact prefixLift 6931748
  have htrace : WordTrace (prefixWord ++ tailWord_6931748) baseStart_6931748 baseEnd_6931748 := by
    simpa [prefixWord, tailWord_6931748, baseEnd_6931748] using wordTrace_append hprefix tailTrace_6931748
  have hstable : (prefixWord ++ tailWord_6931748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931748).length < 2 ^ (prefixWord ++ tailWord_6931748).sum := by decide
  have hdescent : baseEnd_6931748 < baseStart_6931748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6931835 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 5, 2]
def baseStart_6931835 : Nat := 118140960795 + 6931835 * 2 ^ 59
def prefixEnd_6931835 : Nat := 4983230072969 + 3 ^ 40 * 6931835 * 2
def baseEnd_6931835 : Nat := 3559363172658991897383577

theorem tailTrace_6931835 : CollatzResearch.WordTrace tailWord_6931835 prefixEnd_6931835 3559363172658991897383577 := by
  unfold tailWord_6931835
  simp only [CollatzResearch.WordTrace]
  refine ⟨252824792842153133010948959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168549861894768755340632639 252824792842153133010948959)
  ·
    refine ⟨379237189263229699516423439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 252824792842153133010948959 379237189263229699516423439)
    ·
      refine ⟨568855783894844549274635159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379237189263229699516423439 568855783894844549274635159)
      ·
        refine ⟨853283675842266823911952739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 568855783894844549274635159 853283675842266823911952739)
        ·
          refine ⟨1279925513763400235867929109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 853283675842266823911952739 1279925513763400235867929109)
          ·
            refine ⟨59996508457659386056309177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1279925513763400235867929109 59996508457659386056309177)
            ·
              refine ⟨44997381343244539542231883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59996508457659386056309177 44997381343244539542231883)
              ·
                refine ⟨67496072014866809313347825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44997381343244539542231883 67496072014866809313347825)
                ·
                  refine ⟨50622054011150106985010869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67496072014866809313347825 50622054011150106985010869)
                  ·
                    refine ⟨4745817563545322529844769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50622054011150106985010869 4745817563545322529844769)
                    ·
                      refine ⟨3559363172658991897383577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4745817563545322529844769 3559363172658991897383577)
                      ·
                        rfl

theorem cell23_6931835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5, 2].length) (baseStart_6931835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6931835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6931835 prefixEnd_6931835 := by exact prefixLift 6931835
  have htrace : WordTrace (prefixWord ++ tailWord_6931835) baseStart_6931835 baseEnd_6931835 := by
    simpa [prefixWord, tailWord_6931835, baseEnd_6931835] using wordTrace_append hprefix tailTrace_6931835
  have hstable : (prefixWord ++ tailWord_6931835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6931835).length < 2 ^ (prefixWord ++ tailWord_6931835).sum := by decide
  have hdescent : baseEnd_6931835 < baseStart_6931835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6931835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
