import V185TrunkScan22Chunk362

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3237221 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_3237221 : Nat := 118140960795 + 3237221 * 2 ^ 59
def prefixEnd_3237221 : Nat := 4983230072969 + 3 ^ 40 * 3237221 * 2
def baseEnd_3237221 : Nat := 1108166905219056061099865

theorem tailTrace_3237221 : CollatzResearch.WordTrace tailWord_3237221 prefixEnd_3237221 1108166905219056061099865 := by
  unfold tailWord_3237221
  simp only [CollatzResearch.WordTrace]
  refine ⟨118071149805108665175415517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78714099870072443450277011 118071149805108665175415517)
  ·
    refine ⟨44276681176915749440780819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118071149805108665175415517 44276681176915749440780819)
    ·
      refine ⟨66415021765373624161171229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44276681176915749440780819 66415021765373624161171229)
      ·
        refine ⟨24905633162015109060439211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66415021765373624161171229 24905633162015109060439211)
        ·
          refine ⟨37358449743022663590658817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24905633162015109060439211 37358449743022663590658817)
          ·
            refine ⟨28018837307266997692994113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37358449743022663590658817 28018837307266997692994113)
            ·
              refine ⟨21014127980450248269745585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28018837307266997692994113 21014127980450248269745585)
              ·
                refine ⟨15760595985337686202309189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21014127980450248269745585 15760595985337686202309189)
                ·
                  refine ⟨2955111747250816162932973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15760595985337686202309189 2955111747250816162932973)
                  ·
                    refine ⟨1108166905219056061099865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955111747250816162932973 1108166905219056061099865)
                    ·
                      rfl

theorem cell22_3237221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_3237221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237221 prefixEnd_3237221 := by exact prefixLift 3237221
  have htrace : WordTrace (prefixWord ++ tailWord_3237221) baseStart_3237221 baseEnd_3237221 := by
    simpa [prefixWord, tailWord_3237221, baseEnd_3237221] using wordTrace_append hprefix tailTrace_3237221
  have hstable : (prefixWord ++ tailWord_3237221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237221).length < 2 ^ (prefixWord ++ tailWord_3237221).sum := by decide
  have hdescent : baseEnd_3237221 < baseStart_3237221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237234 : List Nat := [3, 2, 1, 2, 1, 2, 11]
def baseStart_3237234 : Nat := 118140960795 + 3237234 * 2 ^ 59
def prefixEnd_3237234 : Nat := 4983230072969 + 3 ^ 40 * 3237234 * 2
def baseEnd_3237234 : Nat := 41043383532767717056475

theorem tailTrace_3237234 : CollatzResearch.WordTrace tailWord_3237234 prefixEnd_3237234 41043383532767717056475 := by
  unfold tailWord_3237234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29517905988515392098909689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78714415969374378930425837 29517905988515392098909689)
  ·
    refine ⟨22138429491386544074182267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29517905988515392098909689 22138429491386544074182267)
    ·
      refine ⟨33207644237079816111273401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22138429491386544074182267 33207644237079816111273401)
      ·
        refine ⟨24905733177809862083455051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33207644237079816111273401 24905733177809862083455051)
        ·
          refine ⟨37358599766714793125182577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24905733177809862083455051 37358599766714793125182577)
          ·
            refine ⟨28018949825036094843886933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37358599766714793125182577 28018949825036094843886933)
            ·
              refine ⟨41043383532767717056475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28018949825036094843886933 41043383532767717056475)
              ·
                rfl

theorem cell22_3237234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 11].length) (baseStart_3237234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237234 prefixEnd_3237234 := by exact prefixLift 3237234
  have htrace : WordTrace (prefixWord ++ tailWord_3237234) baseStart_3237234 baseEnd_3237234 := by
    simpa [prefixWord, tailWord_3237234, baseEnd_3237234] using wordTrace_append hprefix tailTrace_3237234
  have hstable : (prefixWord ++ tailWord_3237234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237234).length < 2 ^ (prefixWord ++ tailWord_3237234).sum := by decide
  have hdescent : baseEnd_3237234 < baseStart_3237234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237255 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 2, 3]
def baseStart_3237255 : Nat := 118140960795 + 3237255 * 2 ^ 59
def prefixEnd_3237255 : Nat := 4983230072969 + 3 ^ 40 * 3237255 * 2
def baseEnd_3237255 : Nat := 1108178544113891305749761

theorem tailTrace_3237255 : CollatzResearch.WordTrace tailWord_3237255 prefixEnd_3237255 1108178544113891305749761 := by
  unfold tailWord_3237255
  simp only [CollatzResearch.WordTrace]
  refine ⟨118072389886985488982153219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78714926591323659321435479 118072389886985488982153219)
  ·
    refine ⟨177108584830478233473229829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118072389886985488982153219 177108584830478233473229829)
    ·
      refine ⟨33207859655714668776230593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177108584830478233473229829 33207859655714668776230593)
      ·
        refine ⟨24905894741786001582172945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33207859655714668776230593 24905894741786001582172945)
        ·
          refine ⟨18679421056339501186629709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24905894741786001582172945 18679421056339501186629709)
          ·
            refine ⟨7004782896127312944986141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18679421056339501186629709 7004782896127312944986141)
            ·
              refine ⟨2626793586047742354369803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7004782896127312944986141 2626793586047742354369803)
              ·
                refine ⟨3940190379071613531554705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626793586047742354369803 3940190379071613531554705)
                ·
                  refine ⟨2955142784303710148666029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940190379071613531554705 2955142784303710148666029)
                  ·
                    refine ⟨1108178544113891305749761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955142784303710148666029 1108178544113891305749761)
                    ·
                      rfl

theorem cell22_3237255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_3237255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237255 prefixEnd_3237255 := by exact prefixLift 3237255
  have htrace : WordTrace (prefixWord ++ tailWord_3237255) baseStart_3237255 baseEnd_3237255 := by
    simpa [prefixWord, tailWord_3237255, baseEnd_3237255] using wordTrace_append hprefix tailTrace_3237255
  have hstable : (prefixWord ++ tailWord_3237255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237255).length < 2 ^ (prefixWord ++ tailWord_3237255).sum := by decide
  have hdescent : baseEnd_3237255 < baseStart_3237255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237268 : List Nat := [2, 4, 2, 1, 2, 1, 4, 6]
def baseStart_3237268 : Nat := 118140960795 + 3237268 * 2 ^ 59
def prefixEnd_3237268 : Nat := 4983230072969 + 3 ^ 40 * 3237268 * 2
def baseEnd_3237268 : Nat := 123131443808840400574969

theorem tailTrace_3237268 : CollatzResearch.WordTrace tailWord_3237268 prefixEnd_3237268 123131443808840400574969 := by
  unfold tailWord_3237268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59036432017969196101188229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78715242690625594801584305 59036432017969196101188229)
  ·
    refine ⟨11069331003369224268972793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59036432017969196101188229 11069331003369224268972793)
    ·
      refine ⟨8301998252526918201729595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11069331003369224268972793 8301998252526918201729595)
      ·
        refine ⟨12452997378790377302594393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8301998252526918201729595 12452997378790377302594393)
        ·
          refine ⟨9339748034092782976945795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12452997378790377302594393 9339748034092782976945795)
          ·
            refine ⟨14009622051139174465418693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9339748034092782976945795 14009622051139174465418693)
            ·
              refine ⟨2626804134588595212266005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14009622051139174465418693 2626804134588595212266005)
              ·
                refine ⟨123131443808840400574969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2626804134588595212266005 123131443808840400574969)
                ·
                  rfl

theorem cell22_3237268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 6].length) (baseStart_3237268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237268 prefixEnd_3237268 := by exact prefixLift 3237268
  have htrace : WordTrace (prefixWord ++ tailWord_3237268) baseStart_3237268 baseEnd_3237268 := by
    simpa [prefixWord, tailWord_3237268, baseEnd_3237268] using wordTrace_append hprefix tailTrace_3237268
  have hstable : (prefixWord ++ tailWord_3237268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237268).length < 2 ^ (prefixWord ++ tailWord_3237268).sum := by decide
  have hdescent : baseEnd_3237268 < baseStart_3237268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237373 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_3237373 : Nat := 118140960795 + 3237373 * 2 ^ 59
def prefixEnd_3237373 : Nat := 4983230072969 + 3 ^ 40 * 3237373 * 2
def baseEnd_3237373 : Nat := 1108218937925378331299399

theorem tailTrace_3237373 : CollatzResearch.WordTrace tailWord_3237373 prefixEnd_3237373 1108218937925378331299399 := by
  unfold tailWord_3237373
  simp only [CollatzResearch.WordTrace]
  refine ⟨118076693700557995134948773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78717795800371996756632515 118076693700557995134948773)
  ·
    refine ⟨22139380068854624087802895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118076693700557995134948773 22139380068854624087802895)
    ·
      refine ⟨33209070103281936131704343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22139380068854624087802895 33209070103281936131704343)
      ·
        refine ⟨49813605154922904197556515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33209070103281936131704343 49813605154922904197556515)
        ·
          refine ⟨74720407732384356296334773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49813605154922904197556515 74720407732384356296334773)
          ·
            refine ⟨7005038224911033402781385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74720407732384356296334773 7005038224911033402781385)
            ·
              refine ⟨5253778668683275052086039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7005038224911033402781385 5253778668683275052086039)
              ·
                refine ⟨7880668003024912578129059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5253778668683275052086039 7880668003024912578129059)
                ·
                  refine ⟨11821002004537368867193589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7880668003024912578129059 11821002004537368867193589)
                  ·
                    refine ⟨1108218937925378331299399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11821002004537368867193589 1108218937925378331299399)
                    ·
                      rfl

theorem cell22_3237373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_3237373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237373 prefixEnd_3237373 := by exact prefixLift 3237373
  have htrace : WordTrace (prefixWord ++ tailWord_3237373) baseStart_3237373 baseEnd_3237373 := by
    simpa [prefixWord, tailWord_3237373, baseEnd_3237373] using wordTrace_append hprefix tailTrace_3237373
  have hstable : (prefixWord ++ tailWord_3237373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237373).length < 2 ^ (prefixWord ++ tailWord_3237373).sum := by decide
  have hdescent : baseEnd_3237373 < baseStart_3237373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237388 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 1, 6]
def baseStart_3237388 : Nat := 118140960795 + 3237388 * 2 ^ 59
def prefixEnd_3237388 : Nat := 4983230072969 + 3 ^ 40 * 3237388 * 2
def baseEnd_3237388 : Nat := 1108224072731923292174353

theorem tailTrace_3237388 : CollatzResearch.WordTrace tailWord_3237388 prefixEnd_3237388 1108224072731923292174353 := by
  unfold tailWord_3237388
  simp only [CollatzResearch.WordTrace]
  refine ⟨59038620397751826348372409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78718160530335768464496545 59038620397751826348372409)
  ·
    refine ⟨44278965298313869761279307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59038620397751826348372409 44278965298313869761279307)
    ·
      refine ⟨66418447947470804641918961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44278965298313869761279307 66418447947470804641918961)
      ·
        refine ⟨49813835960603103481439221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66418447947470804641918961 49813835960603103481439221)
        ·
          refine ⟨4670047121306540951384927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49813835960603103481439221 4670047121306540951384927)
          ·
            refine ⟨7005070681959811427077391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670047121306540951384927 7005070681959811427077391)
            ·
              refine ⟨10507606022939717140616087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005070681959811427077391 10507606022939717140616087)
              ·
                refine ⟨15761409034409575710924131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10507606022939717140616087 15761409034409575710924131)
                ·
                  refine ⟨23642113551614363566386197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15761409034409575710924131 23642113551614363566386197)
                  ·
                    refine ⟨1108224072731923292174353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23642113551614363566386197 1108224072731923292174353)
                    ·
                      rfl

theorem cell22_3237388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_3237388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237388 prefixEnd_3237388 := by exact prefixLift 3237388
  have htrace : WordTrace (prefixWord ++ tailWord_3237388) baseStart_3237388 baseEnd_3237388 := by
    simpa [prefixWord, tailWord_3237388, baseEnd_3237388] using wordTrace_append hprefix tailTrace_3237388
  have hstable : (prefixWord ++ tailWord_3237388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237388).length < 2 ^ (prefixWord ++ tailWord_3237388).sum := by decide
  have hdescent : baseEnd_3237388 < baseStart_3237388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237437 : List Nat := [1, 4, 1, 3, 4, 1, 2, 6]
def baseStart_3237437 : Nat := 118140960795 + 3237437 * 2 ^ 59
def prefixEnd_3237437 : Nat := 4983230072969 + 3 ^ 40 * 3237437 * 2
def baseEnd_3237437 : Nat := 123137871825922610855467

theorem tailTrace_3237437 : CollatzResearch.WordTrace tailWord_3237437 prefixEnd_3237437 123137871825922610855467 := by
  unfold tailWord_3237437
  simp only [CollatzResearch.WordTrace]
  refine ⟨118079027972326134065278565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78719351981550756043519043 118079027972326134065278565)
  ·
    refine ⟨22139817744811150137239731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118079027972326134065278565 22139817744811150137239731)
    ·
      refine ⟨33209726617216725205859597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22139817744811150137239731 33209726617216725205859597)
      ·
        refine ⟨12453647481456271952197349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33209726617216725205859597 12453647481456271952197349)
        ·
          refine ⟨2335058902773050991037003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12453647481456271952197349 2335058902773050991037003)
          ·
            refine ⟨3502588354159576486555505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335058902773050991037003 3502588354159576486555505)
            ·
              refine ⟨2626941265619682364916629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502588354159576486555505 2626941265619682364916629)
              ·
                refine ⟨123137871825922610855467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2626941265619682364916629 123137871825922610855467)
                ·
                  rfl

theorem cell22_3237437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 6].length) (baseStart_3237437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237437 prefixEnd_3237437 := by exact prefixLift 3237437
  have htrace : WordTrace (prefixWord ++ tailWord_3237437) baseStart_3237437 baseEnd_3237437 := by
    simpa [prefixWord, tailWord_3237437, baseEnd_3237437] using wordTrace_append hprefix tailTrace_3237437
  have hstable : (prefixWord ++ tailWord_3237437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237437).length < 2 ^ (prefixWord ++ tailWord_3237437).sum := by decide
  have hdescent : baseEnd_3237437 < baseStart_3237437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237452 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 1, 3]
def baseStart_3237452 : Nat := 118140960795 + 3237452 * 2 ^ 59
def prefixEnd_3237452 : Nat := 4983230072969 + 3 ^ 40 * 3237452 * 2
def baseEnd_3237452 : Nat := 1108245981239848458574157

theorem tailTrace_3237452 : CollatzResearch.WordTrace tailWord_3237452 prefixEnd_3237452 1108245981239848458574157 := by
  unfold tailWord_3237452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59039787533635895813537305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78719716711514527751383073 59039787533635895813537305)
  ·
    refine ⟨44279840650226921860152979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59039787533635895813537305 44279840650226921860152979)
    ·
      refine ⟨66419760975340382790229469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44279840650226921860152979 66419760975340382790229469)
      ·
        refine ⟨24907410365752643546336051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66419760975340382790229469 24907410365752643546336051)
        ·
          refine ⟨37361115548628965319504077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24907410365752643546336051 37361115548628965319504077)
          ·
            refine ⟨14010418330735861994814029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37361115548628965319504077 14010418330735861994814029)
            ·
              refine ⟨5253906874025948248055261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14010418330735861994814029 5253906874025948248055261)
              ·
                refine ⟨1970215077759730593020723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5253906874025948248055261 1970215077759730593020723)
                ·
                  refine ⟨2955322616639595889531085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970215077759730593020723 2955322616639595889531085)
                  ·
                    refine ⟨1108245981239848458574157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955322616639595889531085 1108245981239848458574157)
                    ·
                      rfl

theorem cell22_3237452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_3237452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237452 prefixEnd_3237452 := by exact prefixLift 3237452
  have htrace : WordTrace (prefixWord ++ tailWord_3237452) baseStart_3237452 baseEnd_3237452 := by
    simpa [prefixWord, tailWord_3237452, baseEnd_3237452] using wordTrace_append hprefix tailTrace_3237452
  have hstable : (prefixWord ++ tailWord_3237452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237452).length < 2 ^ (prefixWord ++ tailWord_3237452).sum := by decide
  have hdescent : baseEnd_3237452 < baseStart_3237452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237482 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_3237482 : Nat := 118140960795 + 3237482 * 2 ^ 59
def prefixEnd_3237482 : Nat := 4983230072969 + 3 ^ 40 * 3237482 * 2
def baseEnd_3237482 : Nat := 369418750284312793441355

theorem tailTrace_3237482 : CollatzResearch.WordTrace tailWord_3237482 prefixEnd_3237482 369418750284312793441355 := by
  unfold tailWord_3237482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29520167314290776687666675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78720446171442071167111133 29520167314290776687666675)
  ·
    refine ⟨44280250971436165031500013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29520167314290776687666675 44280250971436165031500013)
    ·
      refine ⟨16605094114288561886812505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44280250971436165031500013 16605094114288561886812505)
      ·
        refine ⟨12453820585716421415109379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16605094114288561886812505 12453820585716421415109379)
        ·
          refine ⟨18680730878574632122664069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12453820585716421415109379 18680730878574632122664069)
          ·
            refine ⟨3502637039732743522999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18680730878574632122664069 3502637039732743522999513)
            ·
              refine ⟨2626977779799557642249635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3502637039732743522999513 2626977779799557642249635)
              ·
                refine ⟨3940466669699336463374453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2626977779799557642249635 3940466669699336463374453)
                ·
                  refine ⟨369418750284312793441355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3940466669699336463374453 369418750284312793441355)
                  ·
                    rfl

theorem cell22_3237482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_3237482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237482 prefixEnd_3237482 := by exact prefixLift 3237482
  have htrace : WordTrace (prefixWord ++ tailWord_3237482) baseStart_3237482 baseEnd_3237482 := by
    simpa [prefixWord, tailWord_3237482, baseEnd_3237482] using wordTrace_append hprefix tailTrace_3237482
  have hstable : (prefixWord ++ tailWord_3237482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237482).length < 2 ^ (prefixWord ++ tailWord_3237482).sum := by decide
  have hdescent : baseEnd_3237482 < baseStart_3237482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237527 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 4]
def baseStart_3237527 : Nat := 118140960795 + 3237527 * 2 ^ 59
def prefixEnd_3237527 : Nat := 4983230072969 + 3 ^ 40 * 3237527 * 2
def baseEnd_3237527 : Nat := 369423885090857754316309

theorem tailTrace_3237527 : CollatzResearch.WordTrace tailWord_3237527 prefixEnd_3237527 369423885090857754316309 := by
  unfold tailWord_3237527
  simp only [CollatzResearch.WordTrace]
  refine ⟨118082310542000079436054835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78721540361333386290703223 118082310542000079436054835)
  ·
    refine ⟨177123465813000119154082253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118082310542000079436054835 177123465813000119154082253)
    ·
      refine ⟨66421299679875044682780845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177123465813000119154082253 66421299679875044682780845)
      ·
        refine ⟨24907987379953141756042817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66421299679875044682780845 24907987379953141756042817)
        ·
          refine ⟨18680990534964856317032113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24907987379953141756042817 18680990534964856317032113)
          ·
            refine ⟨14010742901223642237774085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18680990534964856317032113 14010742901223642237774085)
            ·
              refine ⟨2627014293979432919582641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14010742901223642237774085 2627014293979432919582641)
              ·
                refine ⟨1970260720484574689686981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627014293979432919582641 1970260720484574689686981)
                ·
                  refine ⟨369423885090857754316309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970260720484574689686981 369423885090857754316309)
                  ·
                    rfl

theorem cell22_3237527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 4].length) (baseStart_3237527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237527 prefixEnd_3237527 := by exact prefixLift 3237527
  have htrace : WordTrace (prefixWord ++ tailWord_3237527) baseStart_3237527 baseEnd_3237527 := by
    simpa [prefixWord, tailWord_3237527, baseEnd_3237527] using wordTrace_append hprefix tailTrace_3237527
  have hstable : (prefixWord ++ tailWord_3237527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237527).length < 2 ^ (prefixWord ++ tailWord_3237527).sum := by decide
  have hdescent : baseEnd_3237527 < baseStart_3237527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237544 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 6]
def baseStart_3237544 : Nat := 118140960795 + 3237544 * 2 ^ 59
def prefixEnd_3237544 : Nat := 4983230072969 + 3 ^ 40 * 3237544 * 2
def baseEnd_3237544 : Nat := 369425824906663628424625

theorem tailTrace_3237544 : CollatzResearch.WordTrace tailWord_3237544 prefixEnd_3237544 369425824906663628424625 := by
  unfold tailWord_3237544
  simp only [CollatzResearch.WordTrace]
  refine ⟨59041465291469245669711843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78721953721958994226282457 59041465291469245669711843)
  ·
    refine ⟨88562197937203868504567765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59041465291469245669711843 88562197937203868504567765)
    ·
      refine ⟨2075676514153215668075807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 88562197937203868504567765 2075676514153215668075807)
      ·
        refine ⟨3113514771229823502113711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075676514153215668075807 3113514771229823502113711)
        ·
          refine ⟨4670272156844735253170567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113514771229823502113711 4670272156844735253170567)
          ·
            refine ⟨7005408235267102879755851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670272156844735253170567 7005408235267102879755851)
            ·
              refine ⟨10508112352900654319633777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7005408235267102879755851 10508112352900654319633777)
              ·
                refine ⟨7881084264675490739725333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10508112352900654319633777 7881084264675490739725333)
                ·
                  refine ⟨369425824906663628424625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7881084264675490739725333 369425824906663628424625)
                  ·
                    rfl

theorem cell22_3237544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 6].length) (baseStart_3237544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237544 prefixEnd_3237544 := by exact prefixLift 3237544
  have htrace : WordTrace (prefixWord ++ tailWord_3237544) baseStart_3237544 baseEnd_3237544 := by
    simpa [prefixWord, tailWord_3237544, baseEnd_3237544] using wordTrace_append hprefix tailTrace_3237544
  have hstable : (prefixWord ++ tailWord_3237544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237544).length < 2 ^ (prefixWord ++ tailWord_3237544).sum := by decide
  have hdescent : baseEnd_3237544 < baseStart_3237544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237660 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 1, 5]
def baseStart_3237660 : Nat := 118140960795 + 3237660 * 2 ^ 59
def prefixEnd_3237660 : Nat := 4983230072969 + 3 ^ 40 * 3237660 * 2
def baseEnd_3237660 : Nat := 1108317183890605249373519

theorem tailTrace_3237660 : CollatzResearch.WordTrace tailWord_3237660 prefixEnd_3237660 1108317183890605249373519 := by
  unfold tailWord_3237660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59043580725259121575323217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78724774300345495433764289 59043580725259121575323217)
  ·
    refine ⟨44282685543944341181492413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59043580725259121575323217 44282685543944341181492413)
    ·
      refine ⟨16606007078979127943059655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44282685543944341181492413 16606007078979127943059655)
      ·
        refine ⟨24909010618468691914589483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16606007078979127943059655 24909010618468691914589483)
        ·
          refine ⟨37363515927703037871884225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24909010618468691914589483 37363515927703037871884225)
          ·
            refine ⟨28022636945777278403913169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37363515927703037871884225 28022636945777278403913169)
            ·
              refine ⟨21016977709332958802934877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28022636945777278403913169 21016977709332958802934877)
              ·
                refine ⟨7881366640999859551100579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21016977709332958802934877 7881366640999859551100579)
                ·
                  refine ⟨11822049961499789326650869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881366640999859551100579 11822049961499789326650869)
                  ·
                    refine ⟨1108317183890605249373519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11822049961499789326650869 1108317183890605249373519)
                    ·
                      rfl

theorem cell22_3237660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_3237660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237660 prefixEnd_3237660 := by exact prefixLift 3237660
  have htrace : WordTrace (prefixWord ++ tailWord_3237660) baseStart_3237660 baseEnd_3237660 := by
    simpa [prefixWord, tailWord_3237660, baseEnd_3237660] using wordTrace_append hprefix tailTrace_3237660
  have hstable : (prefixWord ++ tailWord_3237660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237660).length < 2 ^ (prefixWord ++ tailWord_3237660).sum := by decide
  have hdescent : baseEnd_3237660 < baseStart_3237660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237694 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_3237694 : Nat := 118140960795 + 3237694 * 2 ^ 59
def prefixEnd_3237694 : Nat := 4983230072969 + 3 ^ 40 * 3237694 * 2
def baseEnd_3237694 : Nat := 1108328822785440494023415

theorem tailTrace_3237694 : CollatzResearch.WordTrace tailWord_3237694 prefixEnd_3237694 1108328822785440494023415 := by
  unfold tailWord_3237694
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761050191549383369673017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78725601021596711304922757 14761050191549383369673017)
  ·
    refine ⟨11070787643662037527254763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14761050191549383369673017 11070787643662037527254763)
    ·
      refine ⟨16606181465493056290882145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11070787643662037527254763 16606181465493056290882145)
      ·
        refine ⟨12454636099119792218161609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16606181465493056290882145 12454636099119792218161609)
        ·
          refine ⟨9340977074339844163621207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12454636099119792218161609 9340977074339844163621207)
          ·
            refine ⟨14011465611509766245431811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9340977074339844163621207 14011465611509766245431811)
            ·
              refine ⟨21017198417264649368147717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14011465611509766245431811 21017198417264649368147717)
              ·
                refine ⟨3940724703237121756527697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21017198417264649368147717 3940724703237121756527697)
                ·
                  refine ⟨2955543527427841317395773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3940724703237121756527697 2955543527427841317395773)
                  ·
                    refine ⟨1108328822785440494023415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955543527427841317395773 1108328822785440494023415)
                    ·
                      rfl

theorem cell22_3237694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_3237694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237694 prefixEnd_3237694 := by exact prefixLift 3237694
  have htrace : WordTrace (prefixWord ++ tailWord_3237694) baseStart_3237694 baseEnd_3237694 := by
    simpa [prefixWord, tailWord_3237694, baseEnd_3237694] using wordTrace_append hprefix tailTrace_3237694
  have hstable : (prefixWord ++ tailWord_3237694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237694).length < 2 ^ (prefixWord ++ tailWord_3237694).sum := by decide
  have hdescent : baseEnd_3237694 < baseStart_3237694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237722 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_3237722 : Nat := 118140960795 + 3237722 * 2 ^ 59
def prefixEnd_3237722 : Nat := 4983230072969 + 3 ^ 40 * 3237722 * 2
def baseEnd_3237722 : Nat := 1108338407757657754323329

theorem tailTrace_3237722 : CollatzResearch.WordTrace tailWord_3237722 prefixEnd_3237722 1108338407757657754323329 := by
  unfold tailWord_3237722
  simp only [CollatzResearch.WordTrace]
  refine ⟨29522355694073406934850855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78726281850862418492935613 29522355694073406934850855)
  ·
    refine ⟨44283533541110110402276283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29522355694073406934850855 44283533541110110402276283)
    ·
      refine ⟨66425300311665165603414425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44283533541110110402276283 66425300311665165603414425)
      ·
        refine ⟨49818975233748874202560819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66425300311665165603414425 49818975233748874202560819)
        ·
          refine ⟨74728462850623311303841229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49818975233748874202560819 74728462850623311303841229)
          ·
            refine ⟨28023173568983741738940461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74728462850623311303841229 28023173568983741738940461)
            ·
              refine ⟨10508690088368903152102673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28023173568983741738940461 10508690088368903152102673)
              ·
                refine ⟨7881517566276677364077005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10508690088368903152102673 7881517566276677364077005)
                ·
                  refine ⟨2955569087353754011528877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7881517566276677364077005 2955569087353754011528877)
                  ·
                    refine ⟨1108338407757657754323329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955569087353754011528877 1108338407757657754323329)
                    ·
                      rfl

theorem cell22_3237722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_3237722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237722 prefixEnd_3237722 := by exact prefixLift 3237722
  have htrace : WordTrace (prefixWord ++ tailWord_3237722) baseStart_3237722 baseEnd_3237722 := by
    simpa [prefixWord, tailWord_3237722, baseEnd_3237722] using wordTrace_append hprefix tailTrace_3237722
  have hstable : (prefixWord ++ tailWord_3237722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237722).length < 2 ^ (prefixWord ++ tailWord_3237722).sum := by decide
  have hdescent : baseEnd_3237722 < baseStart_3237722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237724 : List Nat := [2, 2, 4, 2, 2, 1, 3, 6]
def baseStart_3237724 : Nat := 118140960795 + 3237724 * 2 ^ 59
def prefixEnd_3237724 : Nat := 4983230072969 + 3 ^ 40 * 3237724 * 2
def baseEnd_3237724 : Nat := 123148788044281157308147

theorem tailTrace_3237724 : CollatzResearch.WordTrace tailWord_3237724 prefixEnd_3237724 123148788044281157308147 := by
  unfold tailWord_3237724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59044747861143191040488113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78726330481524254720650817 59044747861143191040488113)
  ·
    refine ⟨44283560895857393280366085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59044747861143191040488113 44283560895857393280366085)
    ·
      refine ⟨8303167667973261240068641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44283560895857393280366085 8303167667973261240068641)
      ·
        refine ⟨6227375750979945930051481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8303167667973261240068641 6227375750979945930051481)
        ·
          refine ⟨4670531813234959447538611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6227375750979945930051481 4670531813234959447538611)
          ·
            refine ⟨7005797719852439171307917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670531813234959447538611 7005797719852439171307917)
            ·
              refine ⟨2627174144944664689240469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7005797719852439171307917 2627174144944664689240469)
              ·
                refine ⟨123148788044281157308147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2627174144944664689240469 123148788044281157308147)
                ·
                  rfl

theorem cell22_3237724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 6].length) (baseStart_3237724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237724 prefixEnd_3237724 := by exact prefixLift 3237724
  have htrace : WordTrace (prefixWord ++ tailWord_3237724) baseStart_3237724 baseEnd_3237724 := by
    simpa [prefixWord, tailWord_3237724, baseEnd_3237724] using wordTrace_append hprefix tailTrace_3237724
  have hstable : (prefixWord ++ tailWord_3237724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237724).length < 2 ^ (prefixWord ++ tailWord_3237724).sum := by decide
  have hdescent : baseEnd_3237724 < baseStart_3237724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237735 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 7]
def baseStart_3237735 : Nat := 118140960795 + 3237735 * 2 ^ 59
def prefixEnd_3237735 : Nat := 4983230072969 + 3 ^ 40 * 3237735 * 2
def baseEnd_3237735 : Nat := 369447619307776684582763

theorem tailTrace_3237735 : CollatzResearch.WordTrace tailWord_3237735 prefixEnd_3237735 369447619307776684582763 := by
  unfold tailWord_3237735
  simp only [CollatzResearch.WordTrace]
  refine ⟨118089896925246530959626659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78726597950164353973084439 118089896925246530959626659)
  ·
    refine ⟨177134845387869796439439989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118089896925246530959626659 177134845387869796439439989)
    ·
      refine ⟨16606391755112793416197499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177134845387869796439439989 16606391755112793416197499)
      ·
        refine ⟨24909587632669190124296249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16606391755112793416197499 24909587632669190124296249)
        ·
          refine ⟨18682190724501892593222187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24909587632669190124296249 18682190724501892593222187)
          ·
            refine ⟨28023286086752838889833281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682190724501892593222187 28023286086752838889833281)
            ·
              refine ⟨21017464565064629167374961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28023286086752838889833281 21017464565064629167374961)
              ·
                refine ⟨15763098423798471875531221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21017464565064629167374961 15763098423798471875531221)
                ·
                  refine ⟨369447619307776684582763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15763098423798471875531221 369447619307776684582763)
                  ·
                    rfl

theorem cell22_3237735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 7].length) (baseStart_3237735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237735 prefixEnd_3237735 := by exact prefixLift 3237735
  have htrace : WordTrace (prefixWord ++ tailWord_3237735) baseStart_3237735 baseEnd_3237735 := by
    simpa [prefixWord, tailWord_3237735, baseEnd_3237735] using wordTrace_append hprefix tailTrace_3237735
  have hstable : (prefixWord ++ tailWord_3237735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237735).length < 2 ^ (prefixWord ++ tailWord_3237735).sum := by decide
  have hdescent : baseEnd_3237735 < baseStart_3237735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237795 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 3, 5]
def baseStart_3237795 : Nat := 118140960795 + 3237795 * 2 ^ 59
def prefixEnd_3237795 : Nat := 4983230072969 + 3 ^ 40 * 3237795 * 2
def baseEnd_3237795 : Nat := 1108363397149509897248105

theorem tailTrace_3237795 : CollatzResearch.WordTrace tailWord_3237795 prefixEnd_3237795 1108363397149509897248105 := by
  unfold tailWord_3237795
  simp only [CollatzResearch.WordTrace]
  refine ⟨118092085305029161206810839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78728056870019440804540559 118092085305029161206810839)
  ·
    refine ⟨177138127957543741810216259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118092085305029161206810839 177138127957543741810216259)
    ·
      refine ⟨265707191936315612715324389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177138127957543741810216259 265707191936315612715324389)
      ·
        refine ⟨49820098488059177384123323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265707191936315612715324389 49820098488059177384123323)
        ·
          refine ⟨74730147732088766076184985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49820098488059177384123323 74730147732088766076184985)
          ·
            refine ⟨56047610799066574557138739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74730147732088766076184985 56047610799066574557138739)
            ·
              refine ⟨84071416198599861835708109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56047610799066574557138739 84071416198599861835708109)
              ·
                refine ⟨31526781074474948188390541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84071416198599861835708109 31526781074474948188390541)
                ·
                  refine ⟨11822542902928105570646453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31526781074474948188390541 11822542902928105570646453)
                  ·
                    refine ⟨1108363397149509897248105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11822542902928105570646453 1108363397149509897248105)
                    ·
                      rfl

theorem cell22_3237795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_3237795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237795 prefixEnd_3237795 := by exact prefixLift 3237795
  have htrace : WordTrace (prefixWord ++ tailWord_3237795) baseStart_3237795 baseEnd_3237795 := by
    simpa [prefixWord, tailWord_3237795, baseEnd_3237795] using wordTrace_append hprefix tailTrace_3237795
  have hstable : (prefixWord ++ tailWord_3237795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237795).length < 2 ^ (prefixWord ++ tailWord_3237795).sum := by decide
  have hdescent : baseEnd_3237795 < baseStart_3237795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237799 : List Nat := [1, 1, 6, 1, 2, 1, 2, 3, 1, 4]
def baseStart_3237799 : Nat := 118140960795 + 3237799 * 2 ^ 59
def prefixEnd_3237799 : Nat := 4983230072969 + 3 ^ 40 * 3237799 * 2
def baseEnd_3237799 : Nat := 1108364766431255220148093

theorem tailTrace_3237799 : CollatzResearch.WordTrace tailWord_3237799 prefixEnd_3237799 1108364766431255220148093 := by
  unfold tailWord_3237799
  simp only [CollatzResearch.WordTrace]
  refine ⟨118092231197014669889956451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78728154131343113259970967 118092231197014669889956451)
  ·
    refine ⟨177138346795522004834934677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118092231197014669889956451 177138346795522004834934677)
    ·
      refine ⟨8303360006040093976637563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177138346795522004834934677 8303360006040093976637563)
      ·
        refine ⟨12455040009060140964956345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303360006040093976637563 12455040009060140964956345)
        ·
          refine ⟨9341280006795105723717259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12455040009060140964956345 9341280006795105723717259)
          ·
            refine ⟨14011920010192658585575889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9341280006795105723717259 14011920010192658585575889)
            ·
              refine ⟨10508940007644493939181917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14011920010192658585575889 10508940007644493939181917)
              ·
                refine ⟨3940852502866685227193219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10508940007644493939181917 3940852502866685227193219)
                ·
                  refine ⟨5911278754300027840789829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3940852502866685227193219 5911278754300027840789829)
                  ·
                    refine ⟨1108364766431255220148093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5911278754300027840789829 1108364766431255220148093)
                    ·
                      rfl

theorem cell22_3237799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_3237799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237799 prefixEnd_3237799 := by exact prefixLift 3237799
  have htrace : WordTrace (prefixWord ++ tailWord_3237799) baseStart_3237799 baseEnd_3237799 := by
    simpa [prefixWord, tailWord_3237799, baseEnd_3237799] using wordTrace_append hprefix tailTrace_3237799
  have hstable : (prefixWord ++ tailWord_3237799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237799).length < 2 ^ (prefixWord ++ tailWord_3237799).sum := by decide
  have hdescent : baseEnd_3237799 < baseStart_3237799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237840 : List Nat := [2, 1, 1, 1, 1, 2, 4, 1, 2, 7]
def baseStart_3237840 : Nat := 118140960795 + 3237840 * 2 ^ 59
def prefixEnd_3237840 : Nat := 4983230072969 + 3 ^ 40 * 3237840 * 2
def baseEnd_3237840 : Nat := 1108378801569144779872967

theorem tailTrace_3237840 : CollatzResearch.WordTrace tailWord_3237840 prefixEnd_3237840 1108378801569144779872967 := by
  unfold tailWord_3237840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046863294933066946099487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78729151059910755928132649 59046863294933066946099487)
  ·
    refine ⟨88570294942399600419149231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59046863294933066946099487 88570294942399600419149231)
    ·
      refine ⟨132855442413599400628723847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88570294942399600419149231 132855442413599400628723847)
      ·
        refine ⟨199283163620399100943085771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132855442413599400628723847 199283163620399100943085771)
        ·
          refine ⟨298924745430598651414628657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199283163620399100943085771 298924745430598651414628657)
          ·
            refine ⟨224193559072948988560971493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298924745430598651414628657 224193559072948988560971493)
            ·
              refine ⟨42036292326177935355182155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224193559072948988560971493 42036292326177935355182155)
              ·
                refine ⟨63054438489266903032773233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42036292326177935355182155 63054438489266903032773233)
                ·
                  refine ⟨47290828866950177274579925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63054438489266903032773233 47290828866950177274579925)
                  ·
                    refine ⟨1108378801569144779872967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47290828866950177274579925 1108378801569144779872967)
                    ·
                      rfl

theorem cell22_3237840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_3237840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237840 prefixEnd_3237840 := by exact prefixLift 3237840
  have htrace : WordTrace (prefixWord ++ tailWord_3237840) baseStart_3237840 baseEnd_3237840 := by
    simpa [prefixWord, tailWord_3237840, baseEnd_3237840] using wordTrace_append hprefix tailTrace_3237840
  have hstable : (prefixWord ++ tailWord_3237840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237840).length < 2 ^ (prefixWord ++ tailWord_3237840).sum := by decide
  have hdescent : baseEnd_3237840 < baseStart_3237840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237844 : List Nat := [2, 4, 1, 2, 1, 1, 4, 1, 2, 4]
def baseStart_3237844 : Nat := 118140960795 + 3237844 * 2 ^ 59
def prefixEnd_3237844 : Nat := 4983230072969 + 3 ^ 40 * 3237844 * 2
def baseEnd_3237844 : Nat := 1108380170850890102772955

theorem tailTrace_3237844 : CollatzResearch.WordTrace tailWord_3237844 prefixEnd_3237844 1108380170850890102772955 := by
  unfold tailWord_3237844
  simp only [CollatzResearch.WordTrace]
  refine ⟨59046936240925821287672293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78729248321234428383563057 59046936240925821287672293)
  ·
    refine ⟨11071300545173591491438555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59046936240925821287672293 11071300545173591491438555)
    ·
      refine ⟨16606950817760387237157833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11071300545173591491438555 16606950817760387237157833)
      ·
        refine ⟨12455213113320290427868375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16606950817760387237157833 12455213113320290427868375)
        ·
          refine ⟨18682819669980435641802563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12455213113320290427868375 18682819669980435641802563)
          ·
            refine ⟨28024229504970653462703845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18682819669980435641802563 28024229504970653462703845)
            ·
              refine ⟨5254543032181997524256971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28024229504970653462703845 5254543032181997524256971)
              ·
                refine ⟨7881814548272996286385457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5254543032181997524256971 7881814548272996286385457)
                ·
                  refine ⟨5911360911204747214789093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7881814548272996286385457 5911360911204747214789093)
                  ·
                    refine ⟨1108380170850890102772955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5911360911204747214789093 1108380170850890102772955)
                    ·
                      rfl

theorem cell22_3237844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_3237844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237844 prefixEnd_3237844 := by exact prefixLift 3237844
  have htrace : WordTrace (prefixWord ++ tailWord_3237844) baseStart_3237844 baseEnd_3237844 := by
    simpa [prefixWord, tailWord_3237844, baseEnd_3237844] using wordTrace_append hprefix tailTrace_3237844
  have hstable : (prefixWord ++ tailWord_3237844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237844).length < 2 ^ (prefixWord ++ tailWord_3237844).sum := by decide
  have hdescent : baseEnd_3237844 < baseStart_3237844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237846 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_3237846 : Nat := 118140960795 + 3237846 * 2 ^ 59
def prefixEnd_3237846 : Nat := 4983230072969 + 3 ^ 40 * 3237846 * 2
def baseEnd_3237846 : Nat := 1108380855491762764222949

theorem tailTrace_3237846 : CollatzResearch.WordTrace tailWord_3237846 prefixEnd_3237846 1108380855491762764222949 := by
  unfold tailWord_3237846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380871589240274807307337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78729296951896264611278261 7380871589240274807307337)
  ·
    refine ⟨5535653691930206105480503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7380871589240274807307337 5535653691930206105480503)
    ·
      refine ⟨8303480537895309158220755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535653691930206105480503 8303480537895309158220755)
      ·
        refine ⟨12455220806842963737331133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303480537895309158220755 12455220806842963737331133)
        ·
          refine ⟨4670707802566111401499175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12455220806842963737331133 4670707802566111401499175)
          ·
            refine ⟨7006061703849167102248763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4670707802566111401499175 7006061703849167102248763)
            ·
              refine ⟨10509092555773750653373145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006061703849167102248763 10509092555773750653373145)
              ·
                refine ⟨7881819416830312990029859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10509092555773750653373145 7881819416830312990029859)
                ·
                  refine ⟨11822729125245469485044789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7881819416830312990029859 11822729125245469485044789)
                  ·
                    refine ⟨1108380855491762764222949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11822729125245469485044789 1108380855491762764222949)
                    ·
                      rfl

theorem cell22_3237846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_3237846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237846 prefixEnd_3237846 := by exact prefixLift 3237846
  have htrace : WordTrace (prefixWord ++ tailWord_3237846) baseStart_3237846 baseEnd_3237846 := by
    simpa [prefixWord, tailWord_3237846, baseEnd_3237846] using wordTrace_append hprefix tailTrace_3237846
  have hstable : (prefixWord ++ tailWord_3237846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237846).length < 2 ^ (prefixWord ++ tailWord_3237846).sum := by decide
  have hdescent : baseEnd_3237846 < baseStart_3237846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237902 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3237902 : Nat := 118140960795 + 3237902 * 2 ^ 59
def prefixEnd_3237902 : Nat := 4983230072969 + 3 ^ 40 * 3237902 * 2
def baseEnd_3237902 : Nat := 1108400025436197284822777

theorem tailTrace_3237902 : CollatzResearch.WordTrace tailWord_3237902 prefixEnd_3237902 1108400025436197284822777 := by
  unfold tailWord_3237902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761998489455189810119495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78730658610427678987303973 14761998489455189810119495)
  ·
    refine ⟨22142997734182784715179243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14761998489455189810119495 22142997734182784715179243)
    ·
      refine ⟨33214496601274177072768865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22142997734182784715179243 33214496601274177072768865)
      ·
        refine ⟨24910872450955632804576649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33214496601274177072768865 24910872450955632804576649)
        ·
          refine ⟨18683154338216724603432487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24910872450955632804576649 18683154338216724603432487)
          ·
            refine ⟨28024731507325086905148731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18683154338216724603432487 28024731507325086905148731)
            ·
              refine ⟨42037097260987630357723097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28024731507325086905148731 42037097260987630357723097)
              ·
                refine ⟨31527822945740722768292323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42037097260987630357723097 31527822945740722768292323)
                ·
                  refine ⟨47291734418611084152438485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31527822945740722768292323 47291734418611084152438485)
                  ·
                    refine ⟨1108400025436197284822777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47291734418611084152438485 1108400025436197284822777)
                    ·
                      rfl

theorem cell22_3237902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3237902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237902 prefixEnd_3237902 := by exact prefixLift 3237902
  have htrace : WordTrace (prefixWord ++ tailWord_3237902) baseStart_3237902 baseEnd_3237902 := by
    simpa [prefixWord, tailWord_3237902, baseEnd_3237902] using wordTrace_append hprefix tailTrace_3237902
  have hstable : (prefixWord ++ tailWord_3237902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237902).length < 2 ^ (prefixWord ++ tailWord_3237902).sum := by decide
  have hdescent : baseEnd_3237902 < baseStart_3237902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237921 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 5]
def baseStart_3237921 : Nat := 118140960795 + 3237921 * 2 ^ 59
def prefixEnd_3237921 : Nat := 4983230072969 + 3 ^ 40 * 3237921 * 2
def baseEnd_3237921 : Nat := 369468843174829189532573

theorem tailTrace_3237921 : CollatzResearch.WordTrace tailWord_3237921 prefixEnd_3237921 369468843174829189532573 := by
  unfold tailWord_3237921
  simp only [CollatzResearch.WordTrace]
  refine ⟨118096680902572684725897617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78731120601715123150598411 118096680902572684725897617)
  ·
    refine ⟨88572510676929513544423213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118096680902572684725897617 88572510676929513544423213)
    ·
      refine ⟨33214691503848567579158705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88572510676929513544423213 33214691503848567579158705)
      ·
        refine ⟨24911018627886425684369029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33214691503848567579158705 24911018627886425684369029)
        ·
          refine ⟨4670815992728704815819193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24911018627886425684369029 4670815992728704815819193)
          ·
            refine ⟨3503111994546528611864395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4670815992728704815819193 3503111994546528611864395)
            ·
              refine ⟨5254667991819792917796593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503111994546528611864395 5254667991819792917796593)
              ·
                refine ⟨3941000993864844688347445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5254667991819792917796593 3941000993864844688347445)
                ·
                  refine ⟨369468843174829189532573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3941000993864844688347445 369468843174829189532573)
                  ·
                    rfl

theorem cell22_3237921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_3237921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237921 prefixEnd_3237921 := by exact prefixLift 3237921
  have htrace : WordTrace (prefixWord ++ tailWord_3237921) baseStart_3237921 baseEnd_3237921 := by
    simpa [prefixWord, tailWord_3237921, baseEnd_3237921] using wordTrace_append hprefix tailTrace_3237921
  have hstable : (prefixWord ++ tailWord_3237921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237921).length < 2 ^ (prefixWord ++ tailWord_3237921).sum := by decide
  have hdescent : baseEnd_3237921 < baseStart_3237921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237964 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 4, 3]
def baseStart_3237964 : Nat := 118140960795 + 3237964 * 2 ^ 59
def prefixEnd_3237964 : Nat := 4983230072969 + 3 ^ 40 * 3237964 * 2
def baseEnd_3237964 : Nat := 1108421249303249789772587

theorem tailTrace_3237964 : CollatzResearch.WordTrace tailWord_3237964 prefixEnd_3237964 1108421249303249789772587 := by
  unfold tailWord_3237964
  simp only [CollatzResearch.WordTrace]
  refine ⟨59049124620708451534856473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78732166160944602046475297 59049124620708451534856473)
  ·
    refine ⟨44286843465531338651142355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59049124620708451534856473 44286843465531338651142355)
    ·
      refine ⟨66430265198297007976713533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44286843465531338651142355 66430265198297007976713533)
      ·
        refine ⟨24911349449361377991267575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66430265198297007976713533 24911349449361377991267575)
        ·
          refine ⟨37367024174042066986901363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24911349449361377991267575 37367024174042066986901363)
          ·
            refine ⟨56050536261063100480352045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37367024174042066986901363 56050536261063100480352045)
            ·
              refine ⟨21018951097898662680132017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56050536261063100480352045 21018951097898662680132017)
              ·
                refine ⟨15764213323423997010099013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21018951097898662680132017 15764213323423997010099013)
                ·
                  refine ⟨2955789998141999439393565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15764213323423997010099013 2955789998141999439393565)
                  ·
                    refine ⟨1108421249303249789772587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2955789998141999439393565 1108421249303249789772587)
                    ·
                      rfl

theorem cell22_3237964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_3237964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237964 prefixEnd_3237964 := by exact prefixLift 3237964
  have htrace : WordTrace (prefixWord ++ tailWord_3237964) baseStart_3237964 baseEnd_3237964 := by
    simpa [prefixWord, tailWord_3237964, baseEnd_3237964] using wordTrace_append hprefix tailTrace_3237964
  have hstable : (prefixWord ++ tailWord_3237964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237964).length < 2 ^ (prefixWord ++ tailWord_3237964).sum := by decide
  have hdescent : baseEnd_3237964 < baseStart_3237964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3237966 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 4]
def baseStart_3237966 : Nat := 118140960795 + 3237966 * 2 ^ 59
def prefixEnd_3237966 : Nat := 4983230072969 + 3 ^ 40 * 3237966 * 2
def baseEnd_3237966 : Nat := 369473977981374150407527

theorem tailTrace_3237966 : CollatzResearch.WordTrace tailWord_3237966 prefixEnd_3237966 369473977981374150407527 := by
  unfold tailWord_3237966
  simp only [CollatzResearch.WordTrace]
  refine ⟨14762290273426207176410719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78732214791606438274190501 14762290273426207176410719)
  ·
    refine ⟨22143435410139310764616079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14762290273426207176410719 22143435410139310764616079)
    ·
      refine ⟨33215153115208966146924119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22143435410139310764616079 33215153115208966146924119)
      ·
        refine ⟨49822729672813449220386179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33215153115208966146924119 49822729672813449220386179)
        ·
          refine ⟨74734094509220173830579269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49822729672813449220386179 74734094509220173830579269)
          ·
            refine ⟨14012642720478782593233613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74734094509220173830579269 14012642720478782593233613)
            ·
              refine ⟨5254741020179543472462605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14012642720478782593233613 5254741020179543472462605)
              ·
                refine ⟨1970527882567328802173477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5254741020179543472462605 1970527882567328802173477)
                ·
                  refine ⟨369473977981374150407527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1970527882567328802173477 369473977981374150407527)
                  ·
                    rfl

theorem cell22_3237966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_3237966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3237966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3237966 prefixEnd_3237966 := by exact prefixLift 3237966
  have htrace : WordTrace (prefixWord ++ tailWord_3237966) baseStart_3237966 baseEnd_3237966 := by
    simpa [prefixWord, tailWord_3237966, baseEnd_3237966] using wordTrace_append hprefix tailTrace_3237966
  have hstable : (prefixWord ++ tailWord_3237966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3237966).length < 2 ^ (prefixWord ++ tailWord_3237966).sum := by decide
  have hdescent : baseEnd_3237966 < baseStart_3237966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3237966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238146 : List Nat := [3, 4, 1, 1, 2, 1, 10]
def baseStart_3238146 : Nat := 118140960795 + 3238146 * 2 ^ 59
def prefixEnd_3238146 : Nat := 4983230072969 + 3 ^ 40 * 3238146 * 2
def baseEnd_3238146 : Nat := 41054946356394888211927

theorem tailTrace_3238146 : CollatzResearch.WordTrace tailWord_3238146 prefixEnd_3238146 41054946356394888211927 := by
  unfold tailWord_3238146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29526221831689387038209573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78736591551171698768558861 29526221831689387038209573)
  ·
    refine ⟨5536166593441760069664295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29526221831689387038209573 5536166593441760069664295)
    ·
      refine ⟨8304249890162640104496443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536166593441760069664295 8304249890162640104496443)
      ·
        refine ⟨12456374835243960156744665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8304249890162640104496443 12456374835243960156744665)
        ·
          refine ⟨9342281126432970117558499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12456374835243960156744665 9342281126432970117558499)
          ·
            refine ⟨14013421689649455176337749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9342281126432970117558499 14013421689649455176337749)
            ·
              refine ⟨41054946356394888211927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14013421689649455176337749 41054946356394888211927)
              ·
                rfl

theorem cell22_3238146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 10].length) (baseStart_3238146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238146 prefixEnd_3238146 := by exact prefixLift 3238146
  have htrace : WordTrace (prefixWord ++ tailWord_3238146) baseStart_3238146 baseEnd_3238146 := by
    simpa [prefixWord, tailWord_3238146, baseEnd_3238146] using wordTrace_append hprefix tailTrace_3238146
  have hstable : (prefixWord ++ tailWord_3238146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238146).length < 2 ^ (prefixWord ++ tailWord_3238146).sum := by decide
  have hdescent : baseEnd_3238146 < baseStart_3238146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238148 : List Nat := [2, 3, 2, 2, 3, 1, 1, 2, 2, 4]
def baseStart_3238148 : Nat := 118140960795 + 3238148 * 2 ^ 59
def prefixEnd_3238148 : Nat := 4983230072969 + 3 ^ 40 * 3238148 * 2
def baseEnd_3238148 : Nat := 1108484236263534643172023

theorem tailTrace_3238148 : CollatzResearch.WordTrace tailWord_3238148 prefixEnd_3238148 1108484236263534643172023 := by
  unfold tailWord_3238148
  simp only [CollatzResearch.WordTrace]
  refine ⟨59052480136375151247205549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78736640181833534996274065 59052480136375151247205549)
  ·
    refine ⟨22144680051140681717702081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59052480136375151247205549 22144680051140681717702081)
    ·
      refine ⟨16608510038355511288276561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22144680051140681717702081 16608510038355511288276561)
      ·
        refine ⟨12456382528766633466207421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16608510038355511288276561 12456382528766633466207421)
        ·
          refine ⟨4671143448287487549827783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12456382528766633466207421 4671143448287487549827783)
          ·
            refine ⟨7006715172431231324741675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4671143448287487549827783 7006715172431231324741675)
            ·
              refine ⟨10510072758646846987112513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7006715172431231324741675 10510072758646846987112513)
              ·
                refine ⟨7882554568985135240334385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10510072758646846987112513 7882554568985135240334385)
                ·
                  refine ⟨5911915926738851430250789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7882554568985135240334385 5911915926738851430250789)
                  ·
                    refine ⟨1108484236263534643172023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5911915926738851430250789 1108484236263534643172023)
                    ·
                      rfl

theorem cell22_3238148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_3238148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238148 prefixEnd_3238148 := by exact prefixLift 3238148
  have htrace : WordTrace (prefixWord ++ tailWord_3238148) baseStart_3238148 baseEnd_3238148 := by
    simpa [prefixWord, tailWord_3238148, baseEnd_3238148] using wordTrace_append hprefix tailTrace_3238148
  have hstable : (prefixWord ++ tailWord_3238148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238148).length < 2 ^ (prefixWord ++ tailWord_3238148).sum := by decide
  have hdescent : baseEnd_3238148 < baseStart_3238148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238251 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 6, 3]
def baseStart_3238251 : Nat := 118140960795 + 3238251 * 2 ^ 59
def prefixEnd_3238251 : Nat := 4983230072969 + 3 ^ 40 * 3238251 * 2
def baseEnd_3238251 : Nat := 1108519495268476707846707

theorem tailTrace_3238251 : CollatzResearch.WordTrace tailWord_3238251 prefixEnd_3238251 1108519495268476707846707 := by
  unfold tailWord_3238251
  simp only [CollatzResearch.WordTrace]
  refine ⟨118108716991377151085410607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78739144660918100723607071 118108716991377151085410607)
  ·
    refine ⟨177163075487065726628115911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118108716991377151085410607 177163075487065726628115911)
    ·
      refine ⟨265744613230598589942173867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177163075487065726628115911 265744613230598589942173867)
      ·
        refine ⟨398616919845897884913260801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265744613230598589942173867 398616919845897884913260801)
        ·
          refine ⟨298962689884423413684945601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398616919845897884913260801 298962689884423413684945601)
          ·
            refine ⟨224222017413317560263709201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 298962689884423413684945601 224222017413317560263709201)
            ·
              refine ⟨168166513059988170197781901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224222017413317560263709201 168166513059988170197781901)
              ·
                refine ⟨63062442397495563824168213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168166513059988170197781901 63062442397495563824168213)
                ·
                  refine ⟨2956051987382604554257885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63062442397495563824168213 2956051987382604554257885)
                  ·
                    refine ⟨1108519495268476707846707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956051987382604554257885 1108519495268476707846707)
                    ·
                      rfl

theorem cell22_3238251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 6, 3].length) (baseStart_3238251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238251 prefixEnd_3238251 := by exact prefixLift 3238251
  have htrace : WordTrace (prefixWord ++ tailWord_3238251) baseStart_3238251 baseEnd_3238251 := by
    simpa [prefixWord, tailWord_3238251, baseEnd_3238251] using wordTrace_append hprefix tailTrace_3238251
  have hstable : (prefixWord ++ tailWord_3238251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238251).length < 2 ^ (prefixWord ++ tailWord_3238251).sum := by decide
  have hdescent : baseEnd_3238251 < baseStart_3238251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238268 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 2, 3]
def baseStart_3238268 : Nat := 118140960795 + 3238268 * 2 ^ 59
def prefixEnd_3238268 : Nat := 4983230072969 + 3 ^ 40 * 3238268 * 2
def baseEnd_3238268 : Nat := 1108525314715894330171655

theorem tailTrace_3238268 : CollatzResearch.WordTrace tailWord_3238268 prefixEnd_3238268 1108525314715894330171655 := by
  unfold tailWord_3238268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59054668516157781494389729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78739558021543708659186305 59054668516157781494389729)
  ·
    refine ⟨44291001387118336120792297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59054668516157781494389729 44291001387118336120792297)
    ·
      refine ⟨33218251040338752090594223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44291001387118336120792297 33218251040338752090594223)
      ·
        refine ⟨49827376560508128135891335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33218251040338752090594223 49827376560508128135891335)
        ·
          refine ⟨74741064840762192203837003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49827376560508128135891335 74741064840762192203837003)
          ·
            refine ⟨112111597261143288305755505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74741064840762192203837003 112111597261143288305755505)
            ·
              refine ⟨84083697945857466229316629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112111597261143288305755505 84083697945857466229316629)
              ·
                refine ⟨3941423341212068729499217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84083697945857466229316629 3941423341212068729499217)
                ·
                  refine ⟨2956067505909051547124413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3941423341212068729499217 2956067505909051547124413)
                  ·
                    refine ⟨1108525314715894330171655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956067505909051547124413 1108525314715894330171655)
                    ·
                      rfl

theorem cell22_3238268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_3238268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238268 prefixEnd_3238268 := by exact prefixLift 3238268
  have htrace : WordTrace (prefixWord ++ tailWord_3238268) baseStart_3238268 baseEnd_3238268 := by
    simpa [prefixWord, tailWord_3238268, baseEnd_3238268] using wordTrace_append hprefix tailTrace_3238268
  have hstable : (prefixWord ++ tailWord_3238268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238268).length < 2 ^ (prefixWord ++ tailWord_3238268).sum := by decide
  have hdescent : baseEnd_3238268 < baseStart_3238268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238298 : List Nat := [3, 1, 1, 4, 1, 2, 4, 6]
def baseStart_3238298 : Nat := 118140960795 + 3238298 * 2 ^ 59
def prefixEnd_3238298 : Nat := 4983230072969 + 3 ^ 40 * 3238298 * 2
def baseEnd_3238298 : Nat := 123170620480998250213507

theorem tailTrace_3238298 : CollatzResearch.WordTrace tailWord_3238298 prefixEnd_3238298 123170620480998250213507 := by
  unfold tailWord_3238298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29527607805551719528092887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78740287481471252074914365 29527607805551719528092887)
  ·
    refine ⟨44291411708327579292139331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29527607805551719528092887 44291411708327579292139331)
    ·
      refine ⟨66437117562491368938208997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44291411708327579292139331 66437117562491368938208997)
      ·
        refine ⟨12456959542967131675914187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66437117562491368938208997 12456959542967131675914187)
        ·
          refine ⟨18685439314450697513871281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12456959542967131675914187 18685439314450697513871281)
          ·
            refine ⟨14014079485838023135403461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18685439314450697513871281 14014079485838023135403461)
            ·
              refine ⟨2627639903594629337888149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14014079485838023135403461 2627639903594629337888149)
              ·
                refine ⟨123170620480998250213507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2627639903594629337888149 123170620480998250213507)
                ·
                  rfl

theorem cell22_3238298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_3238298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238298 prefixEnd_3238298 := by exact prefixLift 3238298
  have htrace : WordTrace (prefixWord ++ tailWord_3238298) baseStart_3238298 baseEnd_3238298 := by
    simpa [prefixWord, tailWord_3238298, baseEnd_3238298] using wordTrace_append hprefix tailTrace_3238298
  have hstable : (prefixWord ++ tailWord_3238298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238298).length < 2 ^ (prefixWord ++ tailWord_3238298).sum := by decide
  have hdescent : baseEnd_3238298 < baseStart_3238298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238330 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_3238330 : Nat := 118140960795 + 3238330 * 2 ^ 59
def prefixEnd_3238330 : Nat := 4983230072969 + 3 ^ 40 * 3238330 * 2
def baseEnd_3238330 : Nat := 1108546538582946835121465

theorem tailTrace_3238330 : CollatzResearch.WordTrace tailWord_3238330 prefixEnd_3238330 1108546538582946835121465 := by
  unfold tailWord_3238330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29527899589522736894384111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78741065572060631718357629 29527899589522736894384111)
  ·
    refine ⟨44291849384284105341576167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29527899589522736894384111 44291849384284105341576167)
    ·
      refine ⟨66437774076426158012364251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44291849384284105341576167 66437774076426158012364251)
      ·
        refine ⟨99656661114639237018546377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66437774076426158012364251 99656661114639237018546377)
        ·
          refine ⟨74742495835979427763909783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99656661114639237018546377 74742495835979427763909783)
          ·
            refine ⟨112113743753969141645864675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74742495835979427763909783 112113743753969141645864675)
            ·
              refine ⟨168170615630953712468797013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112113743753969141645864675 168170615630953712468797013)
              ·
                refine ⟨1970749401925238817993715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 168170615630953712468797013 1970749401925238817993715)
                ·
                  refine ⟨2956124102887858226990573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970749401925238817993715 2956124102887858226990573)
                  ·
                    refine ⟨1108546538582946835121465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956124102887858226990573 1108546538582946835121465)
                    ·
                      rfl

theorem cell22_3238330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_3238330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238330 prefixEnd_3238330 := by exact prefixLift 3238330
  have htrace : WordTrace (prefixWord ++ tailWord_3238330) baseStart_3238330 baseEnd_3238330 := by
    simpa [prefixWord, tailWord_3238330, baseEnd_3238330] using wordTrace_append hprefix tailTrace_3238330
  have hstable : (prefixWord ++ tailWord_3238330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238330).length < 2 ^ (prefixWord ++ tailWord_3238330).sum := by decide
  have hdescent : baseEnd_3238330 < baseStart_3238330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238343 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 5]
def baseStart_3238343 : Nat := 118140960795 + 3238343 * 2 ^ 59
def prefixEnd_3238343 : Nat := 4983230072969 + 3 ^ 40 * 3238343 * 2
def baseEnd_3238343 : Nat := 369516996249539711515475

theorem tailTrace_3238343 : CollatzResearch.WordTrace tailWord_3238343 prefixEnd_3238343 369516996249539711515475 := by
  unfold tailWord_3238343
  simp only [CollatzResearch.WordTrace]
  refine ⟨118112072507043850797759683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78741381671362567198506455 118112072507043850797759683)
  ·
    refine ⟨177168108760565776196639525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118112072507043850797759683 177168108760565776196639525)
    ·
      refine ⟨33219020392606083036869911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177168108760565776196639525 33219020392606083036869911)
      ·
        refine ⟨49828530588909124555304867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33219020392606083036869911 49828530588909124555304867)
        ·
          refine ⟨74742795883363686832957301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49828530588909124555304867 74742795883363686832957301)
          ·
            refine ⟨7007137114065345640589747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74742795883363686832957301 7007137114065345640589747)
            ·
              refine ⟨10510705671098018460884621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007137114065345640589747 10510705671098018460884621)
              ·
                refine ⟨3941514626661756922831733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10510705671098018460884621 3941514626661756922831733)
                ·
                  refine ⟨369516996249539711515475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3941514626661756922831733 369516996249539711515475)
                  ·
                    rfl

theorem cell22_3238343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 5].length) (baseStart_3238343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238343 prefixEnd_3238343 := by exact prefixLift 3238343
  have htrace : WordTrace (prefixWord ++ tailWord_3238343) baseStart_3238343 baseEnd_3238343 := by
    simpa [prefixWord, tailWord_3238343, baseEnd_3238343] using wordTrace_append hprefix tailTrace_3238343
  have hstable : (prefixWord ++ tailWord_3238343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238343).length < 2 ^ (prefixWord ++ tailWord_3238343).sum := by decide
  have hdescent : baseEnd_3238343 < baseStart_3238343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238381 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_3238381 : Nat := 118140960795 + 3238381 * 2 ^ 59
def prefixEnd_3238381 : Nat := 4983230072969 + 3 ^ 40 * 3238381 * 2
def baseEnd_3238381 : Nat := 1108563996925199702096309

theorem tailTrace_3238381 : CollatzResearch.WordTrace tailWord_3238381 prefixEnd_3238381 1108563996925199702096309 := by
  unfold tailWord_3238381
  simp only [CollatzResearch.WordTrace]
  refine ⟨118113458480906183287642997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78742305653937455525095331 118113458480906183287642997)
  ·
    refine ⟨11073136732584954683216531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118113458480906183287642997 11073136732584954683216531)
    ·
      refine ⟨16609705098877432024824797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11073136732584954683216531 16609705098877432024824797)
      ·
        refine ⟨6228639412079037009309299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16609705098877432024824797 6228639412079037009309299)
        ·
          refine ⟨9342959118118555513963949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6228639412079037009309299 9342959118118555513963949)
          ·
            refine ⟨3503609669294458317736481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9342959118118555513963949 3503609669294458317736481)
            ·
              refine ⟨2627707251970843738302361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503609669294458317736481 2627707251970843738302361)
              ·
                refine ⟨1970780438978132803726771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627707251970843738302361 1970780438978132803726771)
                ·
                  refine ⟨2956170658467199205590157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970780438978132803726771 2956170658467199205590157)
                  ·
                    refine ⟨1108563996925199702096309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956170658467199205590157 1108563996925199702096309)
                    ·
                      rfl

theorem cell22_3238381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_3238381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238381 prefixEnd_3238381 := by exact prefixLift 3238381
  have htrace : WordTrace (prefixWord ++ tailWord_3238381) baseStart_3238381 baseEnd_3238381 := by
    simpa [prefixWord, tailWord_3238381, baseEnd_3238381] using wordTrace_append hprefix tailTrace_3238381
  have hstable : (prefixWord ++ tailWord_3238381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238381).length < 2 ^ (prefixWord ++ tailWord_3238381).sum := by decide
  have hdescent : baseEnd_3238381 < baseStart_3238381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238403 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 1, 5]
def baseStart_3238403 : Nat := 118140960795 + 3238403 * 2 ^ 59
def prefixEnd_3238403 : Nat := 4983230072969 + 3 ^ 40 * 3238403 * 2
def baseEnd_3238403 : Nat := 1108571527974798978046241

theorem tailTrace_3238403 : CollatzResearch.WordTrace tailWord_3238403 prefixEnd_3238403 1108571527974798978046241 := by
  unfold tailWord_3238403
  simp only [CollatzResearch.WordTrace]
  refine ⟨118114260886826481044943863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78742840591217654029962575 118114260886826481044943863)
  ·
    refine ⟨177171391330239721567415795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118114260886826481044943863 177171391330239721567415795)
    ·
      refine ⟨265757086995359582351123693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177171391330239721567415795 265757086995359582351123693)
      ·
        refine ⟨99658907623259843381671385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265757086995359582351123693 99658907623259843381671385)
        ·
          refine ⟨74744180717444882536253539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99658907623259843381671385 74744180717444882536253539)
          ·
            refine ⟨112116271076167323804380309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74744180717444882536253539 112116271076167323804380309)
            ·
              refine ⟨5255450206695343303330327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112116271076167323804380309 5255450206695343303330327)
              ·
                refine ⟨7883175310043014954995491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255450206695343303330327 7883175310043014954995491)
                ·
                  refine ⟨11824762965064522432493237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883175310043014954995491 11824762965064522432493237)
                  ·
                    refine ⟨1108571527974798978046241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11824762965064522432493237 1108571527974798978046241)
                    ·
                      rfl

theorem cell22_3238403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 1, 5].length) (baseStart_3238403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238403 prefixEnd_3238403 := by exact prefixLift 3238403
  have htrace : WordTrace (prefixWord ++ tailWord_3238403) baseStart_3238403 baseEnd_3238403 := by
    simpa [prefixWord, tailWord_3238403, baseEnd_3238403] using wordTrace_append hprefix tailTrace_3238403
  have hstable : (prefixWord ++ tailWord_3238403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238403).length < 2 ^ (prefixWord ++ tailWord_3238403).sum := by decide
  have hdescent : baseEnd_3238403 < baseStart_3238403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238478 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_3238478 : Nat := 118140960795 + 3238478 * 2 ^ 59
def prefixEnd_3238478 : Nat := 4983230072969 + 3 ^ 40 * 3238478 * 2
def baseEnd_3238478 : Nat := 369532400669174594140337

theorem tailTrace_3238478 : CollatzResearch.WordTrace tailWord_3238478 prefixEnd_3238478 369532400669174594140337 := by
  unfold tailWord_3238478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764624545194346106740511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78744664241036512569282725 14764624545194346106740511)
  ·
    refine ⟨22146936817791519160110767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14764624545194346106740511 22146936817791519160110767)
    ·
      refine ⟨33220405226687278740166151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22146936817791519160110767 33220405226687278740166151)
      ·
        refine ⟨49830607840030918110249227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33220405226687278740166151 49830607840030918110249227)
        ·
          refine ⟨74745911760046377165373841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49830607840030918110249227 74745911760046377165373841)
          ·
            refine ⟨56059433820034782874030381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74745911760046377165373841 56059433820034782874030381)
            ·
              refine ⟨21022287682513043577761393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56059433820034782874030381 21022287682513043577761393)
              ·
                refine ⟨15766715761884782683321045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21022287682513043577761393 15766715761884782683321045)
                ·
                  refine ⟨369532400669174594140337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15766715761884782683321045 369532400669174594140337)
                  ·
                    rfl

theorem cell22_3238478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_3238478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238478 prefixEnd_3238478 := by exact prefixLift 3238478
  have htrace : WordTrace (prefixWord ++ tailWord_3238478) baseStart_3238478 baseEnd_3238478 := by
    simpa [prefixWord, tailWord_3238478, baseEnd_3238478] using wordTrace_append hprefix tailTrace_3238478
  have hstable : (prefixWord ++ tailWord_3238478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238478).length < 2 ^ (prefixWord ++ tailWord_3238478).sum := by decide
  have hdescent : baseEnd_3238478 < baseStart_3238478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238499 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 1, 3]
def baseStart_3238499 : Nat := 118140960795 + 3238499 * 2 ^ 59
def prefixEnd_3238499 : Nat := 4983230072969 + 3 ^ 40 * 3238499 * 2
def baseEnd_3238499 : Nat := 1108604390736686727645947

theorem tailTrace_3238499 : CollatzResearch.WordTrace tailWord_3238499 prefixEnd_3238499 1108604390736686727645947 := by
  unfold tailWord_3238499
  simp only [CollatzResearch.WordTrace]
  refine ⟨118117762294478689440438551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78745174862985792960292367 118117762294478689440438551)
  ·
    refine ⟨177176643441718034160657827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118117762294478689440438551 177176643441718034160657827)
    ·
      refine ⟨265764965162577051240986741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177176643441718034160657827 265764965162577051240986741)
      ·
        refine ⟨24915465483991598553842507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265764965162577051240986741 24915465483991598553842507)
        ·
          refine ⟨37373198225987397830763761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24915465483991598553842507 37373198225987397830763761)
          ·
            refine ⟨28029898669490548373072821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37373198225987397830763761 28029898669490548373072821)
            ·
              refine ⟨2627803000264738909975577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28029898669490548373072821 2627803000264738909975577)
              ·
                refine ⟨1970852250198554182481683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2627803000264738909975577 1970852250198554182481683)
                ·
                  refine ⟨2956278375297831273722525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970852250198554182481683 2956278375297831273722525)
                  ·
                    refine ⟨1108604390736686727645947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956278375297831273722525 1108604390736686727645947)
                    ·
                      rfl

theorem cell22_3238499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 1, 3].length) (baseStart_3238499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238499 prefixEnd_3238499 := by exact prefixLift 3238499
  have htrace : WordTrace (prefixWord ++ tailWord_3238499) baseStart_3238499 baseEnd_3238499 := by
    simpa [prefixWord, tailWord_3238499, baseEnd_3238499] using wordTrace_append hprefix tailTrace_3238499
  have hstable : (prefixWord ++ tailWord_3238499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238499).length < 2 ^ (prefixWord ++ tailWord_3238499).sum := by decide
  have hdescent : baseEnd_3238499 < baseStart_3238499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238593 : List Nat := [1, 2, 6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3238593 : Nat := 118140960795 + 3238593 * 2 ^ 59
def prefixEnd_3238593 : Nat := 4983230072969 + 3 ^ 40 * 3238593 * 2
def baseEnd_3238593 : Nat := 1108636568857701815795659

theorem tailTrace_3238593 : CollatzResearch.WordTrace tailWord_3238593 prefixEnd_3238593 1108636568857701815795659 := by
  unfold tailWord_3238593
  simp only [CollatzResearch.WordTrace]
  refine ⟨118121190756138143494360433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78747460504092095662906955 118121190756138143494360433)
  ·
    refine ⟨88590893067103607620770325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118121190756138143494360433 88590893067103607620770325)
    ·
      refine ⟨4152698112520481607223609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 88590893067103607620770325 4152698112520481607223609)
      ·
        refine ⟨3114523584390361205417707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4152698112520481607223609 3114523584390361205417707)
        ·
          refine ⟨4671785376585541808126561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114523584390361205417707 4671785376585541808126561)
          ·
            refine ⟨3503839032439156356094921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671785376585541808126561 3503839032439156356094921)
            ·
              refine ⟨2627879274329367267071191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503839032439156356094921 2627879274329367267071191)
              ·
                refine ⟨3941818911494050900606787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627879274329367267071191 3941818911494050900606787)
                ·
                  refine ⟨5912728367241076350910181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3941818911494050900606787 5912728367241076350910181)
                  ·
                    refine ⟨1108636568857701815795659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5912728367241076350910181 1108636568857701815795659)
                    ·
                      rfl

theorem cell22_3238593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3238593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238593 prefixEnd_3238593 := by exact prefixLift 3238593
  have htrace : WordTrace (prefixWord ++ tailWord_3238593) baseStart_3238593 baseEnd_3238593 := by
    simpa [prefixWord, tailWord_3238593, baseEnd_3238593] using wordTrace_append hprefix tailTrace_3238593
  have hstable : (prefixWord ++ tailWord_3238593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238593).length < 2 ^ (prefixWord ++ tailWord_3238593).sum := by decide
  have hdescent : baseEnd_3238593 < baseStart_3238593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238617 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_3238617 : Nat := 118140960795 + 3238617 * 2 ^ 59
def prefixEnd_3238617 : Nat := 4983230072969 + 3 ^ 40 * 3238617 * 2
def baseEnd_3238617 : Nat := 1108644784548173753195585

theorem tailTrace_3238617 : CollatzResearch.WordTrace tailWord_3238617 prefixEnd_3238617 1108644784548173753195585 := by
  unfold tailWord_3238617
  simp only [CollatzResearch.WordTrace]
  refine ⟨118122066108051195593234105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78748044072034130395489403 118122066108051195593234105)
  ·
    refine ⟨88591549581038396694925579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118122066108051195593234105 88591549581038396694925579)
    ·
      refine ⟨132887324371557595042388369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88591549581038396694925579 132887324371557595042388369)
      ·
        refine ⟨99665493278668196281791277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132887324371557595042388369 99665493278668196281791277)
        ·
          refine ⟨37374559979500573605671729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99665493278668196281791277 37374559979500573605671729)
          ·
            refine ⟨28030919984625430204253797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37374559979500573605671729 28030919984625430204253797)
            ·
              refine ⟨5255797497117268163297587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28030919984625430204253797 5255797497117268163297587)
              ·
                refine ⟨7883696245675902244946381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5255797497117268163297587 7883696245675902244946381)
                ·
                  refine ⟨2956386092128463341854893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7883696245675902244946381 2956386092128463341854893)
                  ·
                    refine ⟨1108644784548173753195585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956386092128463341854893 1108644784548173753195585)
                    ·
                      rfl

theorem cell22_3238617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_3238617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238617 prefixEnd_3238617 := by exact prefixLift 3238617
  have htrace : WordTrace (prefixWord ++ tailWord_3238617) baseStart_3238617 baseEnd_3238617 := by
    simpa [prefixWord, tailWord_3238617, baseEnd_3238617] using wordTrace_append hprefix tailTrace_3238617
  have hstable : (prefixWord ++ tailWord_3238617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238617).length < 2 ^ (prefixWord ++ tailWord_3238617).sum := by decide
  have hdescent : baseEnd_3238617 < baseStart_3238617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238707 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 1, 5]
def baseStart_3238707 : Nat := 118140960795 + 3238707 * 2 ^ 59
def prefixEnd_3238707 : Nat := 4983230072969 + 3 ^ 40 * 3238707 * 2
def baseEnd_3238707 : Nat := 1108675593387443518445309

theorem tailTrace_3238707 : CollatzResearch.WordTrace tailWord_3238707 prefixEnd_3238707 1108675593387443518445309 := by
  unfold tailWord_3238707
  simp only [CollatzResearch.WordTrace]
  refine ⟨118125348677725140964010375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78750232451816760642673583 118125348677725140964010375)
  ·
    refine ⟨177188023016587711446015563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118125348677725140964010375 177188023016587711446015563)
    ·
      refine ⟨265782034524881567169023345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177188023016587711446015563 265782034524881567169023345)
      ·
        refine ⟨199336525893661175376767509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265782034524881567169023345 199336525893661175376767509)
        ·
          refine ⟨9343899651265367595785977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 199336525893661175376767509 9343899651265367595785977)
          ·
            refine ⟨7007924738449025696839483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9343899651265367595785977 7007924738449025696839483)
            ·
              refine ⟨10511887107673538545259225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7007924738449025696839483 10511887107673538545259225)
              ·
                refine ⟨7883915330755153908944419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10511887107673538545259225 7883915330755153908944419)
                ·
                  refine ⟨11825872996132730863416629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7883915330755153908944419 11825872996132730863416629)
                  ·
                    refine ⟨1108675593387443518445309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11825872996132730863416629 1108675593387443518445309)
                    ·
                      rfl

theorem cell22_3238707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 5].length) (baseStart_3238707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238707 prefixEnd_3238707 := by exact prefixLift 3238707
  have htrace : WordTrace (prefixWord ++ tailWord_3238707) baseStart_3238707 baseEnd_3238707 := by
    simpa [prefixWord, tailWord_3238707, baseEnd_3238707] using wordTrace_append hprefix tailTrace_3238707
  have hstable : (prefixWord ++ tailWord_3238707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238707).length < 2 ^ (prefixWord ++ tailWord_3238707).sum := by decide
  have hdescent : baseEnd_3238707 < baseStart_3238707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238872 : List Nat := [2, 1, 2, 2, 2, 3, 2, 8]
def baseStart_3238872 : Nat := 118140960795 + 3238872 * 2 ^ 59
def prefixEnd_3238872 : Nat := 4983230072969 + 3 ^ 40 * 3238872 * 2
def baseEnd_3238872 : Nat := 123192452917715343118867

theorem tailTrace_3238872 : CollatzResearch.WordTrace tailWord_3238872 prefixEnd_3238872 123192452917715343118867 := by
  unfold tailWord_3238872
  simp only [CollatzResearch.WordTrace]
  refine ⟨59065683361063687071883435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78754244481418249429177913 59065683361063687071883435)
  ·
    refine ⟨88598525041595530607825153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59065683361063687071883435 88598525041595530607825153)
    ·
      refine ⟨66448893781196647955868865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88598525041595530607825153 66448893781196647955868865)
      ·
        refine ⟨49836670335897485966901649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66448893781196647955868865 49836670335897485966901649)
        ·
          refine ⟨37377502751923114475176237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49836670335897485966901649 37377502751923114475176237)
          ·
            refine ⟨14016563531971167928191089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37377502751923114475176237 14016563531971167928191089)
            ·
              refine ⟨10512422648978375946143317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14016563531971167928191089 10512422648978375946143317)
              ·
                refine ⟨123192452917715343118867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10512422648978375946143317 123192452917715343118867)
                ·
                  rfl

theorem cell22_3238872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 8].length) (baseStart_3238872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238872 prefixEnd_3238872 := by exact prefixLift 3238872
  have htrace : WordTrace (prefixWord ++ tailWord_3238872) baseStart_3238872 baseEnd_3238872 := by
    simpa [prefixWord, tailWord_3238872, baseEnd_3238872] using wordTrace_append hprefix tailTrace_3238872
  have hstable : (prefixWord ++ tailWord_3238872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238872).length < 2 ^ (prefixWord ++ tailWord_3238872).sum := by decide
  have hdescent : baseEnd_3238872 < baseStart_3238872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238874 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_3238874 : Nat := 118140960795 + 3238874 * 2 ^ 59
def prefixEnd_3238874 : Nat := 4983230072969 + 3 ^ 40 * 3238874 * 2
def baseEnd_3238874 : Nat := 1108732760900310749519797

theorem tailTrace_3238874 : CollatzResearch.WordTrace tailWord_3238874 prefixEnd_3238874 1108732760900310749519797 := by
  unfold tailWord_3238874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29532859917030032121334919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78754293112080085656893117 29532859917030032121334919)
  ·
    refine ⟨44299289875545048182002379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29532859917030032121334919 44299289875545048182002379)
    ·
      refine ⟨66448934813317572273003569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44299289875545048182002379 66448934813317572273003569)
      ·
        refine ⟨49836701109988179204752677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66448934813317572273003569 49836701109988179204752677)
        ·
          refine ⟨9344381458122783600891127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49836701109988179204752677 9344381458122783600891127)
          ·
            refine ⟨14016572187184175401336691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9344381458122783600891127 14016572187184175401336691)
            ·
              refine ⟨21024858280776263102005037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14016572187184175401336691 21024858280776263102005037)
              ·
                refine ⟨7884321855291098663251889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21024858280776263102005037 7884321855291098663251889)
                ·
                  refine ⟨5913241391468323997438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7884321855291098663251889 5913241391468323997438917)
                  ·
                    refine ⟨1108732760900310749519797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913241391468323997438917 1108732760900310749519797)
                    ·
                      rfl

theorem cell22_3238874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_3238874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238874 prefixEnd_3238874 := by exact prefixLift 3238874
  have htrace : WordTrace (prefixWord ++ tailWord_3238874) baseStart_3238874 baseEnd_3238874 := by
    simpa [prefixWord, tailWord_3238874, baseEnd_3238874] using wordTrace_append hprefix tailTrace_3238874
  have hstable : (prefixWord ++ tailWord_3238874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238874).length < 2 ^ (prefixWord ++ tailWord_3238874).sum := by decide
  have hdescent : baseEnd_3238874 < baseStart_3238874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238904 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 3, 3]
def baseStart_3238904 : Nat := 118140960795 + 3238904 * 2 ^ 59
def prefixEnd_3238904 : Nat := 4983230072969 + 3 ^ 40 * 3238904 * 2
def baseEnd_3238904 : Nat := 1108743030513400671269705

theorem tailTrace_3238904 : CollatzResearch.WordTrace tailWord_3238904 prefixEnd_3238904 1108743030513400671269705 := by
  unfold tailWord_3238904
  simp only [CollatzResearch.WordTrace]
  refine ⟨59066266929005721804465883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78755022572007629072621177 59066266929005721804465883)
  ·
    refine ⟨88599400393508582706698825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59066266929005721804465883 88599400393508582706698825)
    ·
      refine ⟨66449550295131437030024119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88599400393508582706698825 66449550295131437030024119)
      ·
        refine ⟨99674325442697155545036179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66449550295131437030024119 99674325442697155545036179)
        ·
          refine ⟨149511488164045733317554269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99674325442697155545036179 149511488164045733317554269)
          ·
            refine ⟨56066808061517149994082851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149511488164045733317554269 56066808061517149994082851)
            ·
              refine ⟨84100212092275724991124277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56066808061517149994082851 84100212092275724991124277)
              ·
                refine ⟨7884394883650849217917901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84100212092275724991124277 7884394883650849217917901)
                ·
                  refine ⟨2956648081369068456719213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7884394883650849217917901 2956648081369068456719213)
                  ·
                    refine ⟨1108743030513400671269705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956648081369068456719213 1108743030513400671269705)
                    ·
                      rfl

theorem cell22_3238904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 3, 3].length) (baseStart_3238904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238904 prefixEnd_3238904 := by exact prefixLift 3238904
  have htrace : WordTrace (prefixWord ++ tailWord_3238904) baseStart_3238904 baseEnd_3238904 := by
    simpa [prefixWord, tailWord_3238904, baseEnd_3238904] using wordTrace_append hprefix tailTrace_3238904
  have hstable : (prefixWord ++ tailWord_3238904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238904).length < 2 ^ (prefixWord ++ tailWord_3238904).sum := by decide
  have hdescent : baseEnd_3238904 < baseStart_3238904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238938 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_3238938 : Nat := 118140960795 + 3238938 * 2 ^ 59
def prefixEnd_3238938 : Nat := 4983230072969 + 3 ^ 40 * 3238938 * 2
def baseEnd_3238938 : Nat := 1108754669408235915919601

theorem tailTrace_3238938 : CollatzResearch.WordTrace tailWord_3238938 prefixEnd_3238938 1108754669408235915919601 := by
  unfold tailWord_3238938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29533443484972066853917367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78755849293258844943779645 29533443484972066853917367)
  ·
    refine ⟨44300165227458100280876051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29533443484972066853917367 44300165227458100280876051)
    ·
      refine ⟨66450247841187150421314077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44300165227458100280876051 66450247841187150421314077)
      ·
        refine ⟨24918842940445181407992779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66450247841187150421314077 24918842940445181407992779)
        ·
          refine ⟨37378264410667772111989169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24918842940445181407992779 37378264410667772111989169)
          ·
            refine ⟨28033698308000829083991877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37378264410667772111989169 28033698308000829083991877)
            ·
              refine ⟨5256318432750155453248477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28033698308000829083991877 5256318432750155453248477)
              ·
                refine ⟨1971119412281308294968179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5256318432750155453248477 1971119412281308294968179)
                ·
                  refine ⟨2956679118421962442452269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971119412281308294968179 2956679118421962442452269)
                  ·
                    refine ⟨1108754669408235915919601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956679118421962442452269 1108754669408235915919601)
                    ·
                      rfl

theorem cell22_3238938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_3238938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238938 prefixEnd_3238938 := by exact prefixLift 3238938
  have htrace : WordTrace (prefixWord ++ tailWord_3238938) baseStart_3238938 baseEnd_3238938 := by
    simpa [prefixWord, tailWord_3238938, baseEnd_3238938] using wordTrace_append hprefix tailTrace_3238938
  have hstable : (prefixWord ++ tailWord_3238938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238938).length < 2 ^ (prefixWord ++ tailWord_3238938).sum := by decide
  have hdescent : baseEnd_3238938 < baseStart_3238938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238951 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 7]
def baseStart_3238951 : Nat := 118140960795 + 3238951 * 2 ^ 59
def prefixEnd_3238951 : Nat := 4983230072969 + 3 ^ 40 * 3238951 * 2
def baseEnd_3238951 : Nat := 369586373191302738448187

theorem tailTrace_3238951 : CollatzResearch.WordTrace tailWord_3238951 prefixEnd_3238951 369586373191302738448187 := by
  unfold tailWord_3238951
  simp only [CollatzResearch.WordTrace]
  refine ⟨118134248088841170635892707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78756165392560780423928471 118134248088841170635892707)
  ·
    refine ⟨177201372133261755953839061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118134248088841170635892707 177201372133261755953839061)
    ·
      refine ⟨4153157159373322405168103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 177201372133261755953839061 4153157159373322405168103)
      ·
        refine ⟨6229735739059983607752155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153157159373322405168103 6229735739059983607752155)
        ·
          refine ⟨9344603608589975411628233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229735739059983607752155 9344603608589975411628233)
          ·
            refine ⟨7008452706442481558721175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9344603608589975411628233 7008452706442481558721175)
            ·
              refine ⟨10512679059663722338081763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7008452706442481558721175 10512679059663722338081763)
              ·
                refine ⟨15769018589495583507122645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10512679059663722338081763 15769018589495583507122645)
                ·
                  refine ⟨369586373191302738448187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15769018589495583507122645 369586373191302738448187)
                  ·
                    rfl

theorem cell22_3238951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 7].length) (baseStart_3238951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238951 prefixEnd_3238951 := by exact prefixLift 3238951
  have htrace : WordTrace (prefixWord ++ tailWord_3238951) baseStart_3238951 baseEnd_3238951 := by
    simpa [prefixWord, tailWord_3238951, baseEnd_3238951] using wordTrace_append hprefix tailTrace_3238951
  have hstable : (prefixWord ++ tailWord_3238951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238951).length < 2 ^ (prefixWord ++ tailWord_3238951).sum := by decide
  have hdescent : baseEnd_3238951 < baseStart_3238951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3238966 : List Nat := [5, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_3238966 : Nat := 118140960795 + 3238966 * 2 ^ 59
def prefixEnd_3238966 : Nat := 4983230072969 + 3 ^ 40 * 3238966 * 2
def baseEnd_3238966 : Nat := 1108764254380453176219515

theorem tailTrace_3238966 : CollatzResearch.WordTrace tailWord_3238966 prefixEnd_3238966 1108764254380453176219515 := by
  unfold tailWord_3238966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383424698986676762355547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78756530122524552131792501 7383424698986676762355547)
  ·
    refine ⟨11075137048480015143533321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7383424698986676762355547 11075137048480015143533321)
    ·
      refine ⟨8306352786360011357649991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11075137048480015143533321 8306352786360011357649991)
      ·
        refine ⟨12459529179540017036474987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8306352786360011357649991 12459529179540017036474987)
        ·
          refine ⟨18689293769310025554712481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12459529179540017036474987 18689293769310025554712481)
          ·
            refine ⟨14016970326982519166034361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18689293769310025554712481 14016970326982519166034361)
            ·
              refine ⟨10512727745236889374525771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14016970326982519166034361 10512727745236889374525771)
              ·
                refine ⟨15769091617855334061788657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10512727745236889374525771 15769091617855334061788657)
                ·
                  refine ⟨11826818713391500546341493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15769091617855334061788657 11826818713391500546341493)
                  ·
                    refine ⟨1108764254380453176219515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11826818713391500546341493 1108764254380453176219515)
                    ·
                      rfl

theorem cell22_3238966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_3238966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3238966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3238966 prefixEnd_3238966 := by exact prefixLift 3238966
  have htrace : WordTrace (prefixWord ++ tailWord_3238966) baseStart_3238966 baseEnd_3238966 := by
    simpa [prefixWord, tailWord_3238966, baseEnd_3238966] using wordTrace_append hprefix tailTrace_3238966
  have hstable : (prefixWord ++ tailWord_3238966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3238966).length < 2 ^ (prefixWord ++ tailWord_3238966).sum := by decide
  have hdescent : baseEnd_3238966 < baseStart_3238966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3238966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239009 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_3239009 : Nat := 118140960795 + 3239009 * 2 ^ 59
def prefixEnd_3239009 : Nat := 4983230072969 + 3 ^ 40 * 3239009 * 2
def baseEnd_3239009 : Nat := 1108778974159215397394383

theorem tailTrace_3239009 : CollatzResearch.WordTrace tailWord_3239009 prefixEnd_3239009 1108778974159215397394383 := by
  unfold tailWord_3239009
  simp only [CollatzResearch.WordTrace]
  refine ⟨118136363522631046541504081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78757575681754031027669387 118136363522631046541504081)
  ·
    refine ⟨88602272641973284906128061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118136363522631046541504081 88602272641973284906128061)
    ·
      refine ⟨33225852240739981839798023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88602272641973284906128061 33225852240739981839798023)
      ·
        refine ⟨49838778361109972759697035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33225852240739981839798023 49838778361109972759697035)
        ·
          refine ⟨74758167541664959139545553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49838778361109972759697035 74758167541664959139545553)
          ·
            refine ⟨56068625656248719354659165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74758167541664959139545553 56068625656248719354659165)
            ·
              refine ⟨21025734621093269757997187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56068625656248719354659165 21025734621093269757997187)
              ·
                refine ⟨31538601931639904636995781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21025734621093269757997187 31538601931639904636995781)
                ·
                  refine ⟨5913487862182482119436709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31538601931639904636995781 5913487862182482119436709)
                  ·
                    refine ⟨1108778974159215397394383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913487862182482119436709 1108778974159215397394383)
                    ·
                      rfl

theorem cell22_3239009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_3239009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239009 prefixEnd_3239009 := by exact prefixLift 3239009
  have htrace : WordTrace (prefixWord ++ tailWord_3239009) baseStart_3239009 baseEnd_3239009 := by
    simpa [prefixWord, tailWord_3239009, baseEnd_3239009] using wordTrace_append hprefix tailTrace_3239009
  have hstable : (prefixWord ++ tailWord_3239009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239009).length < 2 ^ (prefixWord ++ tailWord_3239009).sum := by decide
  have hdescent : baseEnd_3239009 < baseStart_3239009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239011 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 2, 3]
def baseStart_3239011 : Nat := 118140960795 + 3239011 * 2 ^ 59
def prefixEnd_3239011 : Nat := 4983230072969 + 3 ^ 40 * 3239011 * 2
def baseEnd_3239011 : Nat := 1108779658800088058844377

theorem tailTrace_3239011 : CollatzResearch.WordTrace tailWord_3239011 prefixEnd_3239011 1108779658800088058844377 := by
  unfold tailWord_3239011
  simp only [CollatzResearch.WordTrace]
  refine ⟨118136436468623800883076887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78757624312415867255384591 118136436468623800883076887)
  ·
    refine ⟨177204654702935701324615331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118136436468623800883076887 177204654702935701324615331)
    ·
      refine ⟨265806982054403551986922997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177204654702935701324615331 265806982054403551986922997)
      ·
        refine ⟨24919404567600332998774031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265806982054403551986922997 24919404567600332998774031)
        ·
          refine ⟨37379106851400499498161047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24919404567600332998774031 37379106851400499498161047)
          ·
            refine ⟨56068660277100749247241571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37379106851400499498161047 56068660277100749247241571)
            ·
              refine ⟨84102990415651123870862357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56068660277100749247241571 84102990415651123870862357)
              ·
                refine ⟨3942327675733646431446673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84102990415651123870862357 3942327675733646431446673)
                ·
                  refine ⟨2956745756800234823585005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942327675733646431446673 2956745756800234823585005)
                  ·
                    refine ⟨1108779658800088058844377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956745756800234823585005 1108779658800088058844377)
                    ·
                      rfl

theorem cell22_3239011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 2, 3].length) (baseStart_3239011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239011 prefixEnd_3239011 := by exact prefixLift 3239011
  have htrace : WordTrace (prefixWord ++ tailWord_3239011) baseStart_3239011 baseEnd_3239011 := by
    simpa [prefixWord, tailWord_3239011, baseEnd_3239011] using wordTrace_append hprefix tailTrace_3239011
  have hstable : (prefixWord ++ tailWord_3239011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239011).length < 2 ^ (prefixWord ++ tailWord_3239011).sum := by decide
  have hdescent : baseEnd_3239011 < baseStart_3239011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239013 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 4]
def baseStart_3239013 : Nat := 118140960795 + 3239013 * 2 ^ 59
def prefixEnd_3239013 : Nat := 4983230072969 + 3 ^ 40 * 3239013 * 2
def baseEnd_3239013 : Nat := 369593447813653573431457

theorem tailTrace_3239013 : CollatzResearch.WordTrace tailWord_3239013 prefixEnd_3239013 369593447813653573431457 := by
  unfold tailWord_3239013
  simp only [CollatzResearch.WordTrace]
  refine ⟨118136509414616555224649693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78757672943077703483099795 118136509414616555224649693)
  ·
    refine ⟨44301191030481208209243635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118136509414616555224649693 44301191030481208209243635)
    ·
      refine ⟨66451786545721812313865453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44301191030481208209243635 66451786545721812313865453)
      ·
        refine ⟨24919419954645679617699545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66451786545721812313865453 24919419954645679617699545)
        ·
          refine ⟨18689564965984259713274659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24919419954645679617699545 18689564965984259713274659)
          ·
            refine ⟨28034347448976389569911989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18689564965984259713274659 28034347448976389569911989)
            ·
              refine ⟨2628220073341536522179249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28034347448976389569911989 2628220073341536522179249)
              ·
                refine ⟨1971165055006152391634437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628220073341536522179249 1971165055006152391634437)
                ·
                  refine ⟨369593447813653573431457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971165055006152391634437 369593447813653573431457)
                  ·
                    rfl

theorem cell22_3239013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_3239013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239013 prefixEnd_3239013 := by exact prefixLift 3239013
  have htrace : WordTrace (prefixWord ++ tailWord_3239013) baseStart_3239013 baseEnd_3239013 := by
    simpa [prefixWord, tailWord_3239013, baseEnd_3239013] using wordTrace_append hprefix tailTrace_3239013
  have hstable : (prefixWord ++ tailWord_3239013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239013).length < 2 ^ (prefixWord ++ tailWord_3239013).sum := by decide
  have hdescent : baseEnd_3239013 < baseStart_3239013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239024 : List Nat := [2, 1, 1, 1, 5, 1, 4, 7]
def baseStart_3239024 : Nat := 118140960795 + 3239024 * 2 ^ 59
def prefixEnd_3239024 : Nat := 4983230072969 + 3 ^ 40 * 3239024 * 2
def baseEnd_3239024 : Nat := 123198234329528928696593

theorem tailTrace_3239024 : CollatzResearch.WordTrace tailWord_3239024 prefixEnd_3239024 123198234329528928696593 := by
  unfold tailWord_3239024
  simp only [CollatzResearch.WordTrace]
  refine ⟨59068455308788352051650063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78757940411717802735533417 59068455308788352051650063)
  ·
    refine ⟨88602682963182528077475095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59068455308788352051650063 88602682963182528077475095)
    ·
      refine ⟨132904024444773792116212643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88602682963182528077475095 132904024444773792116212643)
      ·
        refine ⟨199356036667160688174318965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132904024444773792116212643 199356036667160688174318965)
        ·
          refine ⟨18689628437546314516342403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199356036667160688174318965 18689628437546314516342403)
          ·
            refine ⟨28034442656319471774513605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18689628437546314516342403 28034442656319471774513605)
            ·
              refine ⟨5256457998059900957721301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28034442656319471774513605 5256457998059900957721301)
              ·
                refine ⟨123198234329528928696593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5256457998059900957721301 123198234329528928696593)
                ·
                  rfl

theorem cell22_3239024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 7].length) (baseStart_3239024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239024 prefixEnd_3239024 := by exact prefixLift 3239024
  have htrace : WordTrace (prefixWord ++ tailWord_3239024) baseStart_3239024 baseEnd_3239024 := by
    simpa [prefixWord, tailWord_3239024, baseEnd_3239024] using wordTrace_append hprefix tailTrace_3239024
  have hstable : (prefixWord ++ tailWord_3239024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239024).length < 2 ^ (prefixWord ++ tailWord_3239024).sum := by decide
  have hdescent : baseEnd_3239024 < baseStart_3239024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239094 : List Nat := [5, 1, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_3239094 : Nat := 118140960795 + 3239094 * 2 ^ 59
def prefixEnd_3239094 : Nat := 4983230072969 + 3 ^ 40 * 3239094 * 2
def baseEnd_3239094 : Nat := 1108808071396303509019123

theorem tailTrace_3239094 : CollatzResearch.WordTrace tailWord_3239094 prefixEnd_3239094 1108808071396303509019123 := by
  unfold tailWord_3239094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383716482957694128646771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78759642484882070705565557 7383716482957694128646771)
  ·
    refine ⟨11075574724436541192970157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7383716482957694128646771 11075574724436541192970157)
    ·
      refine ⟨4153340521663702947363809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11075574724436541192970157 4153340521663702947363809)
      ·
        refine ⟨3115005391247777210522857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4153340521663702947363809 3115005391247777210522857)
        ·
          refine ⟨2336254043435832907892143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3115005391247777210522857 2336254043435832907892143)
          ·
            refine ⟨3504381065153749361838215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336254043435832907892143 3504381065153749361838215)
            ·
              refine ⟨5256571597730624042757323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504381065153749361838215 5256571597730624042757323)
              ·
                refine ⟨7884857396595936064135985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5256571597730624042757323 7884857396595936064135985)
                ·
                  refine ⟨5913643047446952048101989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7884857396595936064135985 5913643047446952048101989)
                  ·
                    refine ⟨1108808071396303509019123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913643047446952048101989 1108808071396303509019123)
                    ·
                      rfl

theorem cell22_3239094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_3239094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239094 prefixEnd_3239094 := by exact prefixLift 3239094
  have htrace : WordTrace (prefixWord ++ tailWord_3239094) baseStart_3239094 baseEnd_3239094 := by
    simpa [prefixWord, tailWord_3239094, baseEnd_3239094] using wordTrace_append hprefix tailTrace_3239094
  have hstable : (prefixWord ++ tailWord_3239094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239094).length < 2 ^ (prefixWord ++ tailWord_3239094).sum := by decide
  have hdescent : baseEnd_3239094 < baseStart_3239094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239159 : List Nat := [1, 1, 3, 1, 1, 1, 2, 12]
def baseStart_3239159 : Nat := 118140960795 + 3239159 * 2 ^ 59
def prefixEnd_3239159 : Nat := 4983230072969 + 3 ^ 40 * 3239159 * 2
def baseEnd_3239159 : Nat := 123203369136073889571547

theorem tailTrace_3239159 : CollatzResearch.WordTrace tailWord_3239159 prefixEnd_3239159 123203369136073889571547 := by
  unfold tailWord_3239159
  simp only [CollatzResearch.WordTrace]
  refine ⟨118141834472087622159464531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78761222981391748106309687 118141834472087622159464531)
  ·
    refine ⟨177212751708131433239196797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118141834472087622159464531 177212751708131433239196797)
    ·
      refine ⟨66454781890549287464698799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177212751708131433239196797 66454781890549287464698799)
      ·
        refine ⟨99682172835823931197048199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66454781890549287464698799 99682172835823931197048199)
        ·
          refine ⟨149523259253735896795572299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99682172835823931197048199 149523259253735896795572299)
          ·
            refine ⟨224284888880603845193358449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149523259253735896795572299 224284888880603845193358449)
            ·
              refine ⟨168213666660452883895018837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224284888880603845193358449 168213666660452883895018837)
              ·
                refine ⟨123203369136073889571547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 168213666660452883895018837 123203369136073889571547)
                ·
                  rfl

theorem cell22_3239159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 12].length) (baseStart_3239159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239159 prefixEnd_3239159 := by exact prefixLift 3239159
  have htrace : WordTrace (prefixWord ++ tailWord_3239159) baseStart_3239159 baseEnd_3239159 := by
    simpa [prefixWord, tailWord_3239159, baseEnd_3239159] using wordTrace_append hprefix tailTrace_3239159
  have hstable : (prefixWord ++ tailWord_3239159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239159).length < 2 ^ (prefixWord ++ tailWord_3239159).sum := by decide
  have hdescent : baseEnd_3239159 < baseStart_3239159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239161 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 2, 4]
def baseStart_3239161 : Nat := 118140960795 + 3239161 * 2 ^ 59
def prefixEnd_3239161 : Nat := 4983230072969 + 3 ^ 40 * 3239161 * 2
def baseEnd_3239161 : Nat := 1108831006865537667593917

theorem tailTrace_3239161 : CollatzResearch.WordTrace tailWord_3239161 prefixEnd_3239161 1108831006865537667593917 := by
  unfold tailWord_3239161
  simp only [CollatzResearch.WordTrace]
  refine ⟨118141907418080376501037337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78761271612053584334024891 118141907418080376501037337)
  ·
    refine ⟨88606430563560282375778003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118141907418080376501037337 88606430563560282375778003)
    ·
      refine ⟨132909645845340423563667005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88606430563560282375778003 132909645845340423563667005)
      ·
        refine ⟨49841117192002658836375127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132909645845340423563667005 49841117192002658836375127)
        ·
          refine ⟨74761675788003988254562691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49841117192002658836375127 74761675788003988254562691)
          ·
            refine ⟨112142513682005982381844037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74761675788003988254562691 112142513682005982381844037)
            ·
              refine ⟨21026721315376121696595757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112142513682005982381844037 21026721315376121696595757)
              ·
                refine ⟨7885020493266045636223409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21026721315376121696595757 7885020493266045636223409)
                ·
                  refine ⟨5913765369949534227167557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7885020493266045636223409 5913765369949534227167557)
                  ·
                    refine ⟨1108831006865537667593917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913765369949534227167557 1108831006865537667593917)
                    ·
                      rfl

theorem cell22_3239161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 2, 4].length) (baseStart_3239161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239161 prefixEnd_3239161 := by exact prefixLift 3239161
  have htrace : WordTrace (prefixWord ++ tailWord_3239161) baseStart_3239161 baseEnd_3239161 := by
    simpa [prefixWord, tailWord_3239161, baseEnd_3239161] using wordTrace_append hprefix tailTrace_3239161
  have hstable : (prefixWord ++ tailWord_3239161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239161).length < 2 ^ (prefixWord ++ tailWord_3239161).sum := by decide
  have hdescent : baseEnd_3239161 < baseStart_3239161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239197 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_3239197 : Nat := 118140960795 + 3239197 * 2 ^ 59
def prefixEnd_3239197 : Nat := 4983230072969 + 3 ^ 40 * 3239197 * 2
def baseEnd_3239197 : Nat := 1108843330401245573693807

theorem tailTrace_3239197 : CollatzResearch.WordTrace tailWord_3239197 prefixEnd_3239197 1108843330401245573693807 := by
  unfold tailWord_3239197
  simp only [CollatzResearch.WordTrace]
  refine ⟨118143220445949954649347845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78762146963966636432898563 118143220445949954649347845)
  ·
    refine ⟨22151853833615616496752721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118143220445949954649347845 22151853833615616496752721)
    ·
      refine ⟨16613890375211712372564541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22151853833615616496752721 16613890375211712372564541)
      ·
        refine ⟨6230208890704392139711703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16613890375211712372564541 6230208890704392139711703)
        ·
          refine ⟨9345313336056588209567555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6230208890704392139711703 9345313336056588209567555)
          ·
            refine ⟨14017970004084882314351333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9345313336056588209567555 14017970004084882314351333)
            ·
              refine ⟨2628369375765915433940875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14017970004084882314351333 2628369375765915433940875)
              ·
                refine ⟨3942554063648873150911313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2628369375765915433940875 3942554063648873150911313)
                ·
                  refine ⟨2956915547736654863183485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3942554063648873150911313 2956915547736654863183485)
                  ·
                    refine ⟨1108843330401245573693807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2956915547736654863183485 1108843330401245573693807)
                    ·
                      rfl

theorem cell22_3239197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_3239197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239197 prefixEnd_3239197 := by exact prefixLift 3239197
  have htrace : WordTrace (prefixWord ++ tailWord_3239197) baseStart_3239197 baseEnd_3239197 := by
    simpa [prefixWord, tailWord_3239197, baseEnd_3239197] using wordTrace_append hprefix tailTrace_3239197
  have hstable : (prefixWord ++ tailWord_3239197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239197).length < 2 ^ (prefixWord ++ tailWord_3239197).sum := by decide
  have hdescent : baseEnd_3239197 < baseStart_3239197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239251 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 5, 4]
def baseStart_3239251 : Nat := 118140960795 + 3239251 * 2 ^ 59
def prefixEnd_3239251 : Nat := 4983230072969 + 3 ^ 40 * 3239251 * 2
def baseEnd_3239251 : Nat := 1108861815704807432843641

theorem tailTrace_3239251 : CollatzResearch.WordTrace tailWord_3239251 prefixEnd_3239251 1108861815704807432843641 := by
  unfold tailWord_3239251
  simp only [CollatzResearch.WordTrace]
  refine ⟨118145189987754321871813607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78763459991836214581209071 118145189987754321871813607)
  ·
    refine ⟨177217784981631482807720411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118145189987754321871813607 177217784981631482807720411)
    ·
      refine ⟨265826677472447224211580617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177217784981631482807720411 265826677472447224211580617)
      ·
        refine ⟨199370008104335418158685463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265826677472447224211580617 199370008104335418158685463)
        ·
          refine ⟨299055012156503127238028195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199370008104335418158685463 299055012156503127238028195)
          ·
            refine ⟨448582518234754690857042293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299055012156503127238028195 448582518234754690857042293)
            ·
              refine ⟨42054611084508252267847715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 448582518234754690857042293 42054611084508252267847715)
              ·
                refine ⟨63081916626762378401771573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42054611084508252267847715 63081916626762378401771573)
                ·
                  refine ⟨5913929683758972975166085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63081916626762378401771573 5913929683758972975166085)
                  ·
                    refine ⟨1108861815704807432843641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913929683758972975166085 1108861815704807432843641)
                    ·
                      rfl

theorem cell22_3239251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 4].length) (baseStart_3239251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239251 prefixEnd_3239251 := by exact prefixLift 3239251
  have htrace : WordTrace (prefixWord ++ tailWord_3239251) baseStart_3239251 baseEnd_3239251 := by
    simpa [prefixWord, tailWord_3239251, baseEnd_3239251] using wordTrace_append hprefix tailTrace_3239251
  have hstable : (prefixWord ++ tailWord_3239251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239251).length < 2 ^ (prefixWord ++ tailWord_3239251).sum := by decide
  have hdescent : baseEnd_3239251 < baseStart_3239251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239253 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3239253 : Nat := 118140960795 + 3239253 * 2 ^ 59
def prefixEnd_3239253 : Nat := 4983230072969 + 3 ^ 40 * 3239253 * 2
def baseEnd_3239253 : Nat := 1108862500345680094293635

theorem tailTrace_3239253 : CollatzResearch.WordTrace tailWord_3239253 prefixEnd_3239253 1108862500345680094293635 := by
  unfold tailWord_3239253
  simp only [CollatzResearch.WordTrace]
  refine ⟨118145262933747076213386413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78763508622498050808924275 118145262933747076213386413)
  ·
    refine ⟨44304473600155153580019905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118145262933747076213386413 44304473600155153580019905)
    ·
      refine ⟨33228355200116365185014929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44304473600155153580019905 33228355200116365185014929)
      ·
        refine ⟨24921266400087273888761197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33228355200116365185014929 24921266400087273888761197)
        ·
          refine ⟨9345474900032727708285449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24921266400087273888761197 9345474900032727708285449)
          ·
            refine ⟨7009106175024545781214087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9345474900032727708285449 7009106175024545781214087)
            ·
              refine ⟨10513659262536818671821131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009106175024545781214087 10513659262536818671821131)
              ·
                refine ⟨15770488893805228007731697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10513659262536818671821131 15770488893805228007731697)
                ·
                  refine ⟨11827866670353921005798773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15770488893805228007731697 11827866670353921005798773)
                  ·
                    refine ⟨1108862500345680094293635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11827866670353921005798773 1108862500345680094293635)
                    ·
                      rfl

theorem cell22_3239253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3239253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239253 prefixEnd_3239253 := by exact prefixLift 3239253
  have htrace : WordTrace (prefixWord ++ tailWord_3239253) baseStart_3239253 baseEnd_3239253 := by
    simpa [prefixWord, tailWord_3239253, baseEnd_3239253] using wordTrace_append hprefix tailTrace_3239253
  have hstable : (prefixWord ++ tailWord_3239253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239253).length < 2 ^ (prefixWord ++ tailWord_3239253).sum := by decide
  have hdescent : baseEnd_3239253 < baseStart_3239253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239268 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 3, 4]
def baseStart_3239268 : Nat := 118140960795 + 3239268 * 2 ^ 59
def prefixEnd_3239268 : Nat := 4983230072969 + 3 ^ 40 * 3239268 * 2
def baseEnd_3239268 : Nat := 1108867635152225055168589

theorem tailTrace_3239268 : CollatzResearch.WordTrace tailWord_3239268 prefixEnd_3239268 1108867635152225055168589 := by
  unfold tailWord_3239268
  simp only [CollatzResearch.WordTrace]
  refine ⟨59072905014346366887591229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78763873352461822516788305 59072905014346366887591229)
  ·
    refine ⟨22152339380379887582846711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59072905014346366887591229 22152339380379887582846711)
    ·
      refine ⟨33228509070569831374270067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22152339380379887582846711 33228509070569831374270067)
      ·
        refine ⟨49842763605854747061405101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33228509070569831374270067 49842763605854747061405101)
        ·
          refine ⟨18691036352195530148026913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49842763605854747061405101 18691036352195530148026913)
          ·
            refine ⟨14018277264146647611020185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18691036352195530148026913 14018277264146647611020185)
            ·
              refine ⟨10513707948109985708265139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14018277264146647611020185 10513707948109985708265139)
              ·
                refine ⟨15770561922164978562397709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10513707948109985708265139 15770561922164978562397709)
                ·
                  refine ⟨5913960720811866960899141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15770561922164978562397709 5913960720811866960899141)
                  ·
                    refine ⟨1108867635152225055168589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5913960720811866960899141 1108867635152225055168589)
                    ·
                      rfl

theorem cell22_3239268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_3239268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239268 prefixEnd_3239268 := by exact prefixLift 3239268
  have htrace : WordTrace (prefixWord ++ tailWord_3239268) baseStart_3239268 baseEnd_3239268 := by
    simpa [prefixWord, tailWord_3239268, baseEnd_3239268] using wordTrace_append hprefix tailTrace_3239268
  have hstable : (prefixWord ++ tailWord_3239268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239268).length < 2 ^ (prefixWord ++ tailWord_3239268).sum := by decide
  have hdescent : baseEnd_3239268 < baseStart_3239268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239300 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 4]
def baseStart_3239300 : Nat := 118140960795 + 3239300 * 2 ^ 59
def prefixEnd_3239300 : Nat := 4983230072969 + 3 ^ 40 * 3239300 * 2
def baseEnd_3239300 : Nat := 369626196468729212789497

theorem tailTrace_3239300 : CollatzResearch.WordTrace tailWord_3239300 prefixEnd_3239300 369626196468729212789497 := by
  unfold tailWord_3239300
  simp only [CollatzResearch.WordTrace]
  refine ⟨59073488582288401620173677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78764651443051202160231569 59073488582288401620173677)
  ·
    refine ⟨22152558218358150607565129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59073488582288401620173677 22152558218358150607565129)
    ·
      refine ⟨16614418663768612955673847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22152558218358150607565129 16614418663768612955673847)
      ·
        refine ⟨24921627995652919433510771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614418663768612955673847 24921627995652919433510771)
        ·
          refine ⟨37382441993479379150266157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24921627995652919433510771 37382441993479379150266157)
          ·
            refine ⟨14018415747554767181349809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37382441993479379150266157 14018415747554767181349809)
            ·
              refine ⟨10513811810666075386012357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14018415747554767181349809 10513811810666075386012357)
              ·
                refine ⟨1971339714499889134877317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10513811810666075386012357 1971339714499889134877317)
                ·
                  refine ⟨369626196468729212789497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971339714499889134877317 369626196468729212789497)
                  ·
                    rfl

theorem cell22_3239300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 4].length) (baseStart_3239300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239300 prefixEnd_3239300 := by exact prefixLift 3239300
  have htrace : WordTrace (prefixWord ++ tailWord_3239300) baseStart_3239300 baseEnd_3239300 := by
    simpa [prefixWord, tailWord_3239300, baseEnd_3239300] using wordTrace_append hprefix tailTrace_3239300
  have hstable : (prefixWord ++ tailWord_3239300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239300).length < 2 ^ (prefixWord ++ tailWord_3239300).sum := by decide
  have hdescent : baseEnd_3239300 < baseStart_3239300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239343 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 5, 3]
def baseStart_3239343 : Nat := 118140960795 + 3239343 * 2 ^ 59
def prefixEnd_3239343 : Nat := 4983230072969 + 3 ^ 40 * 3239343 * 2
def baseEnd_3239343 : Nat := 1108893309184949859543359

theorem tailTrace_3239343 : CollatzResearch.WordTrace tailWord_3239343 prefixEnd_3239343 1108893309184949859543359 := by
  unfold tailWord_3239343
  simp only [CollatzResearch.WordTrace]
  refine ⟨118148545503421021584162683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78765697002280681056108455 118148545503421021584162683)
  ·
    refine ⟨177222818255131532376244025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118148545503421021584162683 177222818255131532376244025)
    ·
      refine ⟨132917113691348649282183019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177222818255131532376244025 132917113691348649282183019)
      ·
        refine ⟨199375670537022973923274529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132917113691348649282183019 199375670537022973923274529)
        ·
          refine ⟨149531752902767230442455897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199375670537022973923274529 149531752902767230442455897)
          ·
            refine ⟨112148814677075422831841923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149531752902767230442455897 112148814677075422831841923)
            ·
              refine ⟨168223222015613134247762885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112148814677075422831841923 168223222015613134247762885)
              ·
                refine ⟨31541854127927462671455541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 168223222015613134247762885 31541854127927462671455541)
                ·
                  refine ⟨2957048824493199625448957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31541854127927462671455541 2957048824493199625448957)
                  ·
                    refine ⟨1108893309184949859543359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957048824493199625448957 1108893309184949859543359)
                    ·
                      rfl

theorem cell22_3239343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_3239343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239343 prefixEnd_3239343 := by exact prefixLift 3239343
  have htrace : WordTrace (prefixWord ++ tailWord_3239343) baseStart_3239343 baseEnd_3239343 := by
    simpa [prefixWord, tailWord_3239343, baseEnd_3239343] using wordTrace_append hprefix tailTrace_3239343
  have hstable : (prefixWord ++ tailWord_3239343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239343).length < 2 ^ (prefixWord ++ tailWord_3239343).sum := by decide
  have hdescent : baseEnd_3239343 < baseStart_3239343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239358 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_3239358 : Nat := 118140960795 + 3239358 * 2 ^ 59
def prefixEnd_3239358 : Nat := 4983230072969 + 3 ^ 40 * 3239358 * 2
def baseEnd_3239358 : Nat := 1108898443991494820418313

theorem tailTrace_3239358 : CollatzResearch.WordTrace tailWord_3239358 prefixEnd_3239358 1108898443991494820418313 := by
  unfold tailWord_3239358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768636574795834893244841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78766061732244452763972485 14768636574795834893244841)
  ·
    refine ⟨11076477431096876169933631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14768636574795834893244841 11076477431096876169933631)
    ·
      refine ⟨16614716146645314254900447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11076477431096876169933631 16614716146645314254900447)
      ·
        refine ⟨24922074219967971382350671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16614716146645314254900447 24922074219967971382350671)
        ·
          refine ⟨37383111329951957073526007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24922074219967971382350671 37383111329951957073526007)
          ·
            refine ⟨56074666994927935610289011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37383111329951957073526007 56074666994927935610289011)
            ·
              refine ⟨84112000492391903415433517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56074666994927935610289011 84112000492391903415433517)
              ·
                refine ⟨31542000184646963780787569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84112000492391903415433517 31542000184646963780787569)
                ·
                  refine ⟨23656500138485222835590677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31542000184646963780787569 23656500138485222835590677)
                  ·
                    refine ⟨1108898443991494820418313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23656500138485222835590677 1108898443991494820418313)
                    ·
                      rfl

theorem cell22_3239358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_3239358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239358 prefixEnd_3239358 := by exact prefixLift 3239358
  have htrace : WordTrace (prefixWord ++ tailWord_3239358) baseStart_3239358 baseEnd_3239358 := by
    simpa [prefixWord, tailWord_3239358, baseEnd_3239358] using wordTrace_append hprefix tailTrace_3239358
  have hstable : (prefixWord ++ tailWord_3239358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239358).length < 2 ^ (prefixWord ++ tailWord_3239358).sum := by decide
  have hdescent : baseEnd_3239358 < baseStart_3239358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239360 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 3, 3]
def baseStart_3239360 : Nat := 118140960795 + 3239360 * 2 ^ 59
def prefixEnd_3239360 : Nat := 4983230072969 + 3 ^ 40 * 3239360 * 2
def baseEnd_3239360 : Nat := 1108899128632367481868307

theorem tailTrace_3239360 : CollatzResearch.WordTrace tailWord_3239360 prefixEnd_3239360 1108899128632367481868307 := by
  unfold tailWord_3239360
  simp only [CollatzResearch.WordTrace]
  refine ⟨59074582772179716743765767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78766110362906288991687689 59074582772179716743765767)
  ·
    refine ⟨88611874158269575115648651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59074582772179716743765767 88611874158269575115648651)
    ·
      refine ⟨132917811237404362673472977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88611874158269575115648651 132917811237404362673472977)
      ·
        refine ⟨99688358428053272005104733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132917811237404362673472977 99688358428053272005104733)
        ·
          refine ⟨37383134410519977001914275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99688358428053272005104733 37383134410519977001914275)
          ·
            refine ⟨56074701615779965502871413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37383134410519977001914275 56074701615779965502871413)
            ·
              refine ⟨5257003276479371765894195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56074701615779965502871413 5257003276479371765894195)
              ·
                refine ⟨7885504914719057648841293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257003276479371765894195 7885504914719057648841293)
                ·
                  refine ⟨2957064343019646618315485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7885504914719057648841293 2957064343019646618315485)
                  ·
                    refine ⟨1108899128632367481868307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957064343019646618315485 1108899128632367481868307)
                    ·
                      rfl

theorem cell22_3239360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 3, 3].length) (baseStart_3239360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239360 prefixEnd_3239360 := by exact prefixLift 3239360
  have htrace : WordTrace (prefixWord ++ tailWord_3239360) baseStart_3239360 baseEnd_3239360 := by
    simpa [prefixWord, tailWord_3239360, baseEnd_3239360] using wordTrace_append hprefix tailTrace_3239360
  have hstable : (prefixWord ++ tailWord_3239360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239360).length < 2 ^ (prefixWord ++ tailWord_3239360).sum := by decide
  have hdescent : baseEnd_3239360 < baseStart_3239360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239418 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 6]
def baseStart_3239418 : Nat := 118140960795 + 3239418 * 2 ^ 59
def prefixEnd_3239418 : Nat := 4983230072969 + 3 ^ 40 * 3239418 * 2
def baseEnd_3239418 : Nat := 369639661072558221306043

theorem tailTrace_3239418 : CollatzResearch.WordTrace tailWord_3239418 prefixEnd_3239418 369639661072558221306043 := by
  unfold tailWord_3239418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29537820244537327348285727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78767520652099539595428605 29537820244537327348285727)
  ·
    refine ⟨44306730366805991022428591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29537820244537327348285727 44306730366805991022428591)
    ·
      refine ⟨66460095550208986533642887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44306730366805991022428591 66460095550208986533642887)
      ·
        refine ⟨99690143325313479800464331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66460095550208986533642887 99690143325313479800464331)
        ·
          refine ⟨149535214987970219700696497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99690143325313479800464331 149535214987970219700696497)
          ·
            refine ⟨112151411240977664775522373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149535214987970219700696497 112151411240977664775522373)
            ·
              refine ⟨21028389607683312145410445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112151411240977664775522373 21028389607683312145410445)
              ·
                refine ⟨7885646102881242054528917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21028389607683312145410445 7885646102881242054528917)
                ·
                  refine ⟨369639661072558221306043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7885646102881242054528917 369639661072558221306043)
                  ·
                    rfl

theorem cell22_3239418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_3239418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239418 prefixEnd_3239418 := by exact prefixLift 3239418
  have htrace : WordTrace (prefixWord ++ tailWord_3239418) baseStart_3239418 baseEnd_3239418 := by
    simpa [prefixWord, tailWord_3239418, baseEnd_3239418] using wordTrace_append hprefix tailTrace_3239418
  have hstable : (prefixWord ++ tailWord_3239418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239418).length < 2 ^ (prefixWord ++ tailWord_3239418).sum := by decide
  have hdescent : baseEnd_3239418 < baseStart_3239418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239435 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 6]
def baseStart_3239435 : Nat := 118140960795 + 3239435 * 2 ^ 59
def prefixEnd_3239435 : Nat := 4983230072969 + 3 ^ 40 * 3239435 * 2
def baseEnd_3239435 : Nat := 369641600888364095414359

theorem tailTrace_3239435 : CollatzResearch.WordTrace tailWord_3239435 prefixEnd_3239435 369641600888364095414359 := by
  unfold tailWord_3239435
  simp only [CollatzResearch.WordTrace]
  refine ⟨118151901019087721296511759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78767934012725147531007839 118151901019087721296511759)
  ·
    refine ⟨177227851528631581944767639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118151901019087721296511759 177227851528631581944767639)
    ·
      refine ⟨265841777292947372917151459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177227851528631581944767639 265841777292947372917151459)
      ·
        refine ⟨398762665939421059375727189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265841777292947372917151459 398762665939421059375727189)
        ·
          refine ⟨4672999991477590539559303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 398762665939421059375727189 4672999991477590539559303)
          ·
            refine ⟨7009499987216385809338955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672999991477590539559303 7009499987216385809338955)
            ·
              refine ⟨10514249980824578714008433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009499987216385809338955 10514249980824578714008433)
              ·
                refine ⟨7885687485618434035506325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10514249980824578714008433 7885687485618434035506325)
                ·
                  refine ⟨369641600888364095414359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7885687485618434035506325 369641600888364095414359)
                  ·
                    rfl

theorem cell22_3239435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 6].length) (baseStart_3239435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239435 prefixEnd_3239435 := by exact prefixLift 3239435
  have htrace : WordTrace (prefixWord ++ tailWord_3239435) baseStart_3239435 baseEnd_3239435 := by
    simpa [prefixWord, tailWord_3239435, baseEnd_3239435] using wordTrace_append hprefix tailTrace_3239435
  have hstable : (prefixWord ++ tailWord_3239435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239435).length < 2 ^ (prefixWord ++ tailWord_3239435).sum := by decide
  have hdescent : baseEnd_3239435 < baseStart_3239435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239450 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_3239450 : Nat := 118140960795 + 3239450 * 2 ^ 59
def prefixEnd_3239450 : Nat := 4983230072969 + 3 ^ 40 * 3239450 * 2
def baseEnd_3239450 : Nat := 1108929937471637247118031

theorem tailTrace_3239450 : CollatzResearch.WordTrace tailWord_3239450 prefixEnd_3239450 1108929937471637247118031 := by
  unfold tailWord_3239450
  simp only [CollatzResearch.WordTrace]
  refine ⟨29538112028508344714576951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78768298742688919238871869 29538112028508344714576951)
  ·
    refine ⟨44307168042762517071865427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29538112028508344714576951 44307168042762517071865427)
    ·
      refine ⟨66460752064143775607798141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44307168042762517071865427 66460752064143775607798141)
      ·
        refine ⟨24922782024053915852924303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66460752064143775607798141 24922782024053915852924303)
        ·
          refine ⟨37384173036080873779386455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24922782024053915852924303 37384173036080873779386455)
          ·
            refine ⟨56076259554121310669079683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37384173036080873779386455 56076259554121310669079683)
            ·
              refine ⟨84114389331181966003619525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56076259554121310669079683 84114389331181966003619525)
              ·
                refine ⟨15771447999596618625678661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84114389331181966003619525 15771447999596618625678661)
                ·
                  refine ⟨2957146499924365992314749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15771447999596618625678661 2957146499924365992314749)
                  ·
                    refine ⟨1108929937471637247118031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957146499924365992314749 1108929937471637247118031)
                    ·
                      rfl

theorem cell22_3239450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_3239450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239450 prefixEnd_3239450 := by exact prefixLift 3239450
  have htrace : WordTrace (prefixWord ++ tailWord_3239450) baseStart_3239450 baseEnd_3239450 := by
    simpa [prefixWord, tailWord_3239450, baseEnd_3239450] using wordTrace_append hprefix tailTrace_3239450
  have hstable : (prefixWord ++ tailWord_3239450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239450).length < 2 ^ (prefixWord ++ tailWord_3239450).sum := by decide
  have hdescent : baseEnd_3239450 < baseStart_3239450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239452 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 4]
def baseStart_3239452 : Nat := 118140960795 + 3239452 * 2 ^ 59
def prefixEnd_3239452 : Nat := 4983230072969 + 3 ^ 40 * 3239452 * 2
def baseEnd_3239452 : Nat := 369643540704169969522675

theorem tailTrace_3239452 : CollatzResearch.WordTrace tailWord_3239452 prefixEnd_3239452 369643540704169969522675 := by
  unfold tailWord_3239452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59076260530013066599940305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78768347373350755466587073 59076260530013066599940305)
  ·
    refine ⟨44307195397509799949955229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59076260530013066599940305 44307195397509799949955229)
    ·
      refine ⟨16615198274066174981233211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44307195397509799949955229 16615198274066174981233211)
      ·
        refine ⟨24922797411099262471849817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16615198274066174981233211 24922797411099262471849817)
        ·
          refine ⟨18692098058324446853887363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24922797411099262471849817 18692098058324446853887363)
          ·
            refine ⟨28038147087486670280831045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18692098058324446853887363 28038147087486670280831045)
            ·
              refine ⟨5257152578903750677655821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28038147087486670280831045 5257152578903750677655821)
              ·
                refine ⟨1971432217088906504120933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5257152578903750677655821 1971432217088906504120933)
                ·
                  refine ⟨369643540704169969522675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971432217088906504120933 369643540704169969522675)
                  ·
                    rfl

theorem cell22_3239452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 4].length) (baseStart_3239452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239452 prefixEnd_3239452 := by exact prefixLift 3239452
  have htrace : WordTrace (prefixWord ++ tailWord_3239452) baseStart_3239452 baseEnd_3239452 := by
    simpa [prefixWord, tailWord_3239452, baseEnd_3239452] using wordTrace_append hprefix tailTrace_3239452
  have hstable : (prefixWord ++ tailWord_3239452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239452).length < 2 ^ (prefixWord ++ tailWord_3239452).sum := by decide
  have hdescent : baseEnd_3239452 < baseStart_3239452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239484 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 1, 5]
def baseStart_3239484 : Nat := 118140960795 + 3239484 * 2 ^ 59
def prefixEnd_3239484 : Nat := 4983230072969 + 3 ^ 40 * 3239484 * 2
def baseEnd_3239484 : Nat := 1108941576366472491767927

theorem tailTrace_3239484 : CollatzResearch.WordTrace tailWord_3239484 prefixEnd_3239484 1108941576366472491767927 := by
  unfold tailWord_3239484
  simp only [CollatzResearch.WordTrace]
  refine ⟨59076844097955101332522753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78769125463940135110030337 59076844097955101332522753)
  ·
    refine ⟨44307633073466325999392065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59076844097955101332522753 44307633073466325999392065)
    ·
      refine ⟨33230724805099744499544049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44307633073466325999392065 33230724805099744499544049)
      ·
        refine ⟨24923043603824808374658037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33230724805099744499544049 24923043603824808374658037)
        ·
          refine ⟨2336535337858575785124191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24923043603824808374658037 2336535337858575785124191)
          ·
            refine ⟨3504803006787863677686287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336535337858575785124191 3504803006787863677686287)
            ·
              refine ⟨5257204510181795516529431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504803006787863677686287 5257204510181795516529431)
              ·
                refine ⟨7885806765272693274794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257204510181795516529431 7885806765272693274794147)
                ·
                  refine ⟨11828710147909039912191221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7885806765272693274794147 11828710147909039912191221)
                  ·
                    refine ⟨1108941576366472491767927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11828710147909039912191221 1108941576366472491767927)
                    ·
                      rfl

theorem cell22_3239484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_3239484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239484 prefixEnd_3239484 := by exact prefixLift 3239484
  have htrace : WordTrace (prefixWord ++ tailWord_3239484) baseStart_3239484 baseEnd_3239484 := by
    simpa [prefixWord, tailWord_3239484, baseEnd_3239484] using wordTrace_append hprefix tailTrace_3239484
  have hstable : (prefixWord ++ tailWord_3239484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239484).length < 2 ^ (prefixWord ++ tailWord_3239484).sum := by decide
  have hdescent : baseEnd_3239484 < baseStart_3239484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239525 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 7]
def baseStart_3239525 : Nat := 118140960795 + 3239525 * 2 ^ 59
def prefixEnd_3239525 : Nat := 4983230072969 + 3 ^ 40 * 3239525 * 2
def baseEnd_3239525 : Nat := 369651870501454017164267

theorem tailTrace_3239525 : CollatzResearch.WordTrace tailWord_3239525 prefixEnd_3239525 369651870501454017164267 := by
  unfold tailWord_3239525
  simp only [CollatzResearch.WordTrace]
  refine ⟨118155183588761666667288029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78770122392507777778192019 118155183588761666667288029)
  ·
    refine ⟨44308193845785625000233011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118155183588761666667288029 44308193845785625000233011)
    ·
      refine ⟨66462290768678437500349517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44308193845785625000233011 66462290768678437500349517)
      ·
        refine ⟨24923359038254414062631069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66462290768678437500349517 24923359038254414062631069)
        ·
          refine ⟨9346259639345405273486651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24923359038254414062631069 9346259639345405273486651)
          ·
            refine ⟨14019389459018107910229977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346259639345405273486651 14019389459018107910229977)
            ·
              refine ⟨10514542094263580932672483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14019389459018107910229977 10514542094263580932672483)
              ·
                refine ⟨15771813141395371399008725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10514542094263580932672483 15771813141395371399008725)
                ·
                  refine ⟨369651870501454017164267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15771813141395371399008725 369651870501454017164267)
                  ·
                    rfl

theorem cell22_3239525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_3239525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239525 prefixEnd_3239525 := by exact prefixLift 3239525
  have htrace : WordTrace (prefixWord ++ tailWord_3239525) baseStart_3239525 baseEnd_3239525 := by
    simpa [prefixWord, tailWord_3239525, baseEnd_3239525] using wordTrace_append hprefix tailTrace_3239525
  have hstable : (prefixWord ++ tailWord_3239525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239525).length < 2 ^ (prefixWord ++ tailWord_3239525).sum := by decide
  have hdescent : baseEnd_3239525 < baseStart_3239525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239580 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3239580 : Nat := 118140960795 + 3239580 * 2 ^ 59
def prefixEnd_3239580 : Nat := 4983230072969 + 3 ^ 40 * 3239580 * 2
def baseEnd_3239580 : Nat := 1108974439128360241367633

theorem tailTrace_3239580 : CollatzResearch.WordTrace tailWord_3239580 prefixEnd_3239580 1108974439128360241367633 := by
  unfold tailWord_3239580
  simp only [CollatzResearch.WordTrace]
  refine ⟨59078594801781205530270097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78771459735708274040360129 59078594801781205530270097)
  ·
    refine ⟨44308946101335904147702573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59078594801781205530270097 44308946101335904147702573)
    ·
      refine ⟨16615854788000964055388465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44308946101335904147702573 16615854788000964055388465)
      ·
        refine ⟨12461891091000723041541349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16615854788000964055388465 12461891091000723041541349)
        ·
          refine ⟨2336604579562635570289003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12461891091000723041541349 2336604579562635570289003)
          ·
            refine ⟨3504906869343953355433505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336604579562635570289003 3504906869343953355433505)
            ·
              refine ⟨2628680152007965016575129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3504906869343953355433505 2628680152007965016575129)
              ·
                refine ⟨1971510114005973762431347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2628680152007965016575129 1971510114005973762431347)
                ·
                  refine ⟨2957265171008960643647021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971510114005973762431347 2957265171008960643647021)
                  ·
                    refine ⟨1108974439128360241367633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957265171008960643647021 1108974439128360241367633)
                    ·
                      rfl

theorem cell22_3239580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3239580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239580 prefixEnd_3239580 := by exact prefixLift 3239580
  have htrace : WordTrace (prefixWord ++ tailWord_3239580) baseStart_3239580 baseEnd_3239580 := by
    simpa [prefixWord, tailWord_3239580, baseEnd_3239580] using wordTrace_append hprefix tailTrace_3239580
  have hstable : (prefixWord ++ tailWord_3239580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239580).length < 2 ^ (prefixWord ++ tailWord_3239580).sum := by decide
  have hdescent : baseEnd_3239580 < baseStart_3239580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239587 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 4]
def baseStart_3239587 : Nat := 118140960795 + 3239587 * 2 ^ 59
def prefixEnd_3239587 : Nat := 4983230072969 + 3 ^ 40 * 3239587 * 2
def baseEnd_3239587 : Nat := 369658945123804852147537

theorem tailTrace_3239587 : CollatzResearch.WordTrace tailWord_3239587 prefixEnd_3239587 369658945123804852147537 := by
  unfold tailWord_3239587
  simp only [CollatzResearch.WordTrace]
  refine ⟨118157444914537051256045015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78771629943024700837363343 118157444914537051256045015)
  ·
    refine ⟨177236167371805576884067523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118157444914537051256045015 177236167371805576884067523)
    ·
      refine ⟨265854251057708365326101285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177236167371805576884067523 265854251057708365326101285)
      ·
        refine ⟨49847672073320318498643991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 265854251057708365326101285 49847672073320318498643991)
        ·
          refine ⟨74771508109980477747965987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49847672073320318498643991 74771508109980477747965987)
          ·
            refine ⟨112157262164970716621948981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74771508109980477747965987 112157262164970716621948981)
            ·
              refine ⟨10514743327966004683307717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112157262164970716621948981 10514743327966004683307717)
              ·
                refine ⟨1971514373993625878120197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10514743327966004683307717 1971514373993625878120197)
                ·
                  refine ⟨369658945123804852147537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971514373993625878120197 369658945123804852147537)
                  ·
                    rfl

theorem cell22_3239587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 4].length) (baseStart_3239587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239587 prefixEnd_3239587 := by exact prefixLift 3239587
  have htrace : WordTrace (prefixWord ++ tailWord_3239587) baseStart_3239587 baseEnd_3239587 := by
    simpa [prefixWord, tailWord_3239587, baseEnd_3239587] using wordTrace_append hprefix tailTrace_3239587
  have hstable : (prefixWord ++ tailWord_3239587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239587).length < 2 ^ (prefixWord ++ tailWord_3239587).sum := by decide
  have hdescent : baseEnd_3239587 < baseStart_3239587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239600 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 4, 4]
def baseStart_3239600 : Nat := 118140960795 + 3239600 * 2 ^ 59
def prefixEnd_3239600 : Nat := 4983230072969 + 3 ^ 40 * 3239600 * 2
def baseEnd_3239600 : Nat := 1108981285537086855867571

theorem tailTrace_3239600 : CollatzResearch.WordTrace tailWord_3239600 prefixEnd_3239600 1108981285537086855867571 := by
  unfold tailWord_3239600
  simp only [CollatzResearch.WordTrace]
  refine ⟨59078959531744977238134127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78771946042326636317512169 59078959531744977238134127)
  ·
    refine ⟨88618439297617465857201191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59078959531744977238134127 88618439297617465857201191)
    ·
      refine ⟨132927658946426198785801787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88618439297617465857201191 132927658946426198785801787)
      ·
        refine ⟨199391488419639298178702681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132927658946426198785801787 199391488419639298178702681)
        ·
          refine ⟨149543616314729473634027011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199391488419639298178702681 149543616314729473634027011)
          ·
            refine ⟨224315424472094210451040517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149543616314729473634027011 224315424472094210451040517)
            ·
              refine ⟨42059142088517664459570097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224315424472094210451040517 42059142088517664459570097)
              ·
                refine ⟨31544356566388248344677573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42059142088517664459570097 31544356566388248344677573)
                ·
                  refine ⟨5914566856197796564627045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31544356566388248344677573 5914566856197796564627045)
                  ·
                    refine ⟨1108981285537086855867571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5914566856197796564627045 1108981285537086855867571)
                    ·
                      rfl

theorem cell22_3239600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_3239600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239600 prefixEnd_3239600 := by exact prefixLift 3239600
  have htrace : WordTrace (prefixWord ++ tailWord_3239600) baseStart_3239600 baseEnd_3239600 := by
    simpa [prefixWord, tailWord_3239600, baseEnd_3239600] using wordTrace_append hprefix tailTrace_3239600
  have hstable : (prefixWord ++ tailWord_3239600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239600).length < 2 ^ (prefixWord ++ tailWord_3239600).sum := by decide
  have hdescent : baseEnd_3239600 < baseStart_3239600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239636 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3239636 : Nat := 118140960795 + 3239636 * 2 ^ 59
def prefixEnd_3239636 : Nat := 4983230072969 + 3 ^ 40 * 3239636 * 2
def baseEnd_3239636 : Nat := 1108993609072794761967461

theorem tailTrace_3239636 : CollatzResearch.WordTrace tailWord_3239636 prefixEnd_3239636 1108993609072794761967461 := by
  unfold tailWord_3239636
  simp only [CollatzResearch.WordTrace]
  refine ⟨59079616045679766312289381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78772821394239688416385841 59079616045679766312289381)
  ·
    refine ⟨11077428008564956183554259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59079616045679766312289381 11077428008564956183554259)
    ·
      refine ⟨16616142012847434275331389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11077428008564956183554259 16616142012847434275331389)
      ·
        refine ⟨6231053254817787853249271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16616142012847434275331389 6231053254817787853249271)
        ·
          refine ⟨9346579882226681779873907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231053254817787853249271 9346579882226681779873907)
          ·
            refine ⟨14019869823340022669810861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9346579882226681779873907 14019869823340022669810861)
            ·
              refine ⟨5257451183752508501179073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14019869823340022669810861 5257451183752508501179073)
              ·
                refine ⟨3943088387814381375884305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257451183752508501179073 3943088387814381375884305)
                ·
                  refine ⟨2957316290860786031913229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3943088387814381375884305 2957316290860786031913229)
                  ·
                    refine ⟨1108993609072794761967461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957316290860786031913229 1108993609072794761967461)
                    ·
                      rfl

theorem cell22_3239636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3239636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239636 prefixEnd_3239636 := by exact prefixLift 3239636
  have htrace : WordTrace (prefixWord ++ tailWord_3239636) baseStart_3239636 baseEnd_3239636 := by
    simpa [prefixWord, tailWord_3239636, baseEnd_3239636] using wordTrace_append hprefix tailTrace_3239636
  have hstable : (prefixWord ++ tailWord_3239636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239636).length < 2 ^ (prefixWord ++ tailWord_3239636).sum := by decide
  have hdescent : baseEnd_3239636 < baseStart_3239636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239675 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 4, 5]
def baseStart_3239675 : Nat := 118140960795 + 3239675 * 2 ^ 59
def prefixEnd_3239675 : Nat := 4983230072969 + 3 ^ 40 * 3239675 * 2
def baseEnd_3239675 : Nat := 1109006959569811660242341

theorem tailTrace_3239675 : CollatzResearch.WordTrace tailWord_3239675 prefixEnd_3239675 1109006959569811660242341 := by
  unfold tailWord_3239675
  simp only [CollatzResearch.WordTrace]
  refine ⟨118160654538218242285248479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78773769692145494856832319 118160654538218242285248479)
  ·
    refine ⟨177240981807327363427872719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118160654538218242285248479 177240981807327363427872719)
    ·
      refine ⟨265861472710991045141809079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177240981807327363427872719 265861472710991045141809079)
      ·
        refine ⟨398792209066486567712713619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265861472710991045141809079 398792209066486567712713619)
        ·
          refine ⟨598188313599729851569070429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398792209066486567712713619 598188313599729851569070429)
          ·
            refine ⟨224320617599898694338401411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598188313599729851569070429 224320617599898694338401411)
            ·
              refine ⟨336480926399848041507602117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224320617599898694338401411 336480926399848041507602117)
              ·
                refine ⟨63090173699971507782675397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 336480926399848041507602117 63090173699971507782675397)
                ·
                  refine ⟨11829407568744657709251637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63090173699971507782675397 11829407568744657709251637)
                  ·
                    refine ⟨1109006959569811660242341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11829407568744657709251637 1109006959569811660242341)
                    ·
                      rfl

theorem cell22_3239675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 4, 5].length) (baseStart_3239675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239675 prefixEnd_3239675 := by exact prefixLift 3239675
  have htrace : WordTrace (prefixWord ++ tailWord_3239675) baseStart_3239675 baseEnd_3239675 := by
    simpa [prefixWord, tailWord_3239675, baseEnd_3239675] using wordTrace_append hprefix tailTrace_3239675
  have hstable : (prefixWord ++ tailWord_3239675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239675).length < 2 ^ (prefixWord ++ tailWord_3239675).sum := by decide
  have hdescent : baseEnd_3239675 < baseStart_3239675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239681 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 1, 3]
def baseStart_3239681 : Nat := 118140960795 + 3239681 * 2 ^ 59
def prefixEnd_3239681 : Nat := 4983230072969 + 3 ^ 40 * 3239681 * 2
def baseEnd_3239681 : Nat := 1109009013492429644592323

theorem tailTrace_3239681 : CollatzResearch.WordTrace tailWord_3239681 prefixEnd_3239681 1109009013492429644592323 := by
  unfold tailWord_3239681
  simp only [CollatzResearch.WordTrace]
  refine ⟨118160873376196505309966897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78773915584131003539977931 118160873376196505309966897)
  ·
    refine ⟨88620655032147378982475173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118160873376196505309966897 88620655032147378982475173)
    ·
      refine ⟨16616372818527633559214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88620655032147378982475173 16616372818527633559214095)
      ·
        refine ⟨24924559227791450338821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16616372818527633559214095 24924559227791450338821143)
        ·
          refine ⟨37386838841687175508231715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24924559227791450338821143 37386838841687175508231715)
          ·
            refine ⟨56080258262530763262347573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37386838841687175508231715 56080258262530763262347573)
            ·
              refine ⟨5257524212112259055845085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56080258262530763262347573 5257524212112259055845085)
              ·
                refine ⟨1971571579542097145941907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5257524212112259055845085 1971571579542097145941907)
                ·
                  refine ⟨2957357369313145718912861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971571579542097145941907 2957357369313145718912861)
                  ·
                    refine ⟨1109009013492429644592323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957357369313145718912861 1109009013492429644592323)
                    ·
                      rfl

theorem cell22_3239681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_3239681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239681 prefixEnd_3239681 := by exact prefixLift 3239681
  have htrace : WordTrace (prefixWord ++ tailWord_3239681) baseStart_3239681 baseEnd_3239681 := by
    simpa [prefixWord, tailWord_3239681, baseEnd_3239681] using wordTrace_append hprefix tailTrace_3239681
  have hstable : (prefixWord ++ tailWord_3239681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239681).length < 2 ^ (prefixWord ++ tailWord_3239681).sum := by decide
  have hdescent : baseEnd_3239681 < baseStart_3239681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239698 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_3239698 : Nat := 118140960795 + 3239698 * 2 ^ 59
def prefixEnd_3239698 : Nat := 4983230072969 + 3 ^ 40 * 3239698 * 2
def baseEnd_3239698 : Nat := 1109014832939847266917271

theorem tailTrace_3239698 : CollatzResearch.WordTrace tailWord_3239698 prefixEnd_3239698 1109014832939847266917271 := by
  unfold tailWord_3239698
  simp only [CollatzResearch.WordTrace]
  refine ⟨29540373354283729303333937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78774328944756611475557165 29540373354283729303333937)
  ·
    refine ⟨22155280015712796977500453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29540373354283729303333937 22155280015712796977500453)
    ·
      refine ⟨4154115002946149433281335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22155280015712796977500453 4154115002946149433281335)
      ·
        refine ⟨6231172504419224149922003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154115002946149433281335 6231172504419224149922003)
        ·
          refine ⟨9346758756628836224883005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231172504419224149922003 9346758756628836224883005)
          ·
            refine ⟨3505034533735813584331127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9346758756628836224883005 3505034533735813584331127)
            ·
              refine ⟨5257551800603720376496691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505034533735813584331127 5257551800603720376496691)
              ·
                refine ⟨7886327700905580564745037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257551800603720376496691 7886327700905580564745037)
                ·
                  refine ⟨2957372887839592711779389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7886327700905580564745037 2957372887839592711779389)
                  ·
                    refine ⟨1109014832939847266917271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957372887839592711779389 1109014832939847266917271)
                    ·
                      rfl

theorem cell22_3239698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_3239698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239698 prefixEnd_3239698 := by exact prefixLift 3239698
  have htrace : WordTrace (prefixWord ++ tailWord_3239698) baseStart_3239698 baseEnd_3239698 := by
    simpa [prefixWord, tailWord_3239698, baseEnd_3239698] using wordTrace_append hprefix tailTrace_3239698
  have hstable : (prefixWord ++ tailWord_3239698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239698).length < 2 ^ (prefixWord ++ tailWord_3239698).sum := by decide
  have hdescent : baseEnd_3239698 < baseStart_3239698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239724 : List Nat := [2, 2, 1, 1, 1, 5, 3, 2, 1, 4]
def baseStart_3239724 : Nat := 118140960795 + 3239724 * 2 ^ 59
def prefixEnd_3239724 : Nat := 4983230072969 + 3 ^ 40 * 3239724 * 2
def baseEnd_3239724 : Nat := 1109023733271191865767191

theorem tailTrace_3239724 : CollatzResearch.WordTrace tailWord_3239724 prefixEnd_3239724 1109023733271191865767191 := by
  unfold tailWord_3239724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59081220857520361826891113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78774961143360482435854817 59081220857520361826891113)
  ·
    refine ⟨44310915643140271370168335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59081220857520361826891113 44310915643140271370168335)
    ·
      refine ⟨66466373464710407055252503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44310915643140271370168335 66466373464710407055252503)
      ·
        refine ⟨99699560197065610582878755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66466373464710407055252503 99699560197065610582878755)
        ·
          refine ⟨149549340295598415874318133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99699560197065610582878755 149549340295598415874318133)
          ·
            refine ⟨14020250652712351488217325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149549340295598415874318133 14020250652712351488217325)
            ·
              refine ⟨5257593994767131808081497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14020250652712351488217325 5257593994767131808081497)
              ·
                refine ⟨3943195496075348856061123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257593994767131808081497 3943195496075348856061123)
                ·
                  refine ⟨5914793244113023284091685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943195496075348856061123 5914793244113023284091685)
                  ·
                    refine ⟨1109023733271191865767191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5914793244113023284091685 1109023733271191865767191)
                    ·
                      rfl

theorem cell22_3239724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_3239724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239724 prefixEnd_3239724 := by exact prefixLift 3239724
  have htrace : WordTrace (prefixWord ++ tailWord_3239724) baseStart_3239724 baseEnd_3239724 := by
    simpa [prefixWord, tailWord_3239724, baseEnd_3239724] using wordTrace_append hprefix tailTrace_3239724
  have hstable : (prefixWord ++ tailWord_3239724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239724).length < 2 ^ (prefixWord ++ tailWord_3239724).sum := by decide
  have hdescent : baseEnd_3239724 < baseStart_3239724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239756 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 4]
def baseStart_3239756 : Nat := 118140960795 + 3239756 * 2 ^ 59
def prefixEnd_3239756 : Nat := 4983230072969 + 3 ^ 40 * 3239756 * 2
def baseEnd_3239756 : Nat := 369678229175051482989031

theorem tailTrace_3239756 : CollatzResearch.WordTrace tailWord_3239756 prefixEnd_3239756 369678229175051482989031 := by
  unfold tailWord_3239756
  simp only [CollatzResearch.WordTrace]
  refine ⟨59081804425462396559473561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78775739233949862079298081 59081804425462396559473561)
  ·
    refine ⟨44311353319096797419605171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59081804425462396559473561 44311353319096797419605171)
    ·
      refine ⟨66467029978645196129407757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44311353319096797419605171 66467029978645196129407757)
      ·
        refine ⟨24925136241991948548527909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66467029978645196129407757 24925136241991948548527909)
        ·
          refine ⟨4673463045373490352848983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24925136241991948548527909 4673463045373490352848983)
          ·
            refine ⟨7010194568060235529273475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673463045373490352848983 7010194568060235529273475)
            ·
              refine ⟨10515291852090353293910213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010194568060235529273475 10515291852090353293910213)
              ·
                refine ⟨1971617222266941242608165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10515291852090353293910213 1971617222266941242608165)
                ·
                  refine ⟨369678229175051482989031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971617222266941242608165 369678229175051482989031)
                  ·
                    rfl

theorem cell22_3239756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 4].length) (baseStart_3239756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239756 prefixEnd_3239756 := by exact prefixLift 3239756
  have htrace : WordTrace (prefixWord ++ tailWord_3239756) baseStart_3239756 baseEnd_3239756 := by
    simpa [prefixWord, tailWord_3239756, baseEnd_3239756] using wordTrace_append hprefix tailTrace_3239756
  have hstable : (prefixWord ++ tailWord_3239756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239756).length < 2 ^ (prefixWord ++ tailWord_3239756).sum := by decide
  have hdescent : baseEnd_3239756 < baseStart_3239756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239784 : List Nat := [2, 1, 4, 2, 1, 1, 5, 6]
def baseStart_3239784 : Nat := 118140960795 + 3239784 * 2 ^ 59
def prefixEnd_3239784 : Nat := 4983230072969 + 3 ^ 40 * 3239784 * 2
def baseEnd_3239784 : Nat := 123227141388596856585223

theorem tailTrace_3239784 : CollatzResearch.WordTrace tailWord_3239784 prefixEnd_3239784 123227141388596856585223 := by
  unfold tailWord_3239784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59082315047411676950483203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78776420063215569267310937 59082315047411676950483203)
  ·
    refine ⟨88623472571117515425724805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59082315047411676950483203 88623472571117515425724805)
    ·
      refine ⟨16616901107084534142323401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88623472571117515425724805 16616901107084534142323401)
      ·
        refine ⟨12462675830313400606742551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16616901107084534142323401 12462675830313400606742551)
        ·
          refine ⟨18694013745470100910113827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12462675830313400606742551 18694013745470100910113827)
          ·
            refine ⟨28041020618205151365170741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18694013745470100910113827 28041020618205151365170741)
            ·
              refine ⟨2628845682956732940484757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28041020618205151365170741 2628845682956732940484757)
              ·
                refine ⟨123227141388596856585223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2628845682956732940484757 123227141388596856585223)
                ·
                  rfl

theorem cell22_3239784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 6].length) (baseStart_3239784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239784 prefixEnd_3239784 := by exact prefixLift 3239784
  have htrace : WordTrace (prefixWord ++ tailWord_3239784) baseStart_3239784 baseEnd_3239784 := by
    simpa [prefixWord, tailWord_3239784, baseEnd_3239784] using wordTrace_append hprefix tailTrace_3239784
  have hstable : (prefixWord ++ tailWord_3239784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239784).length < 2 ^ (prefixWord ++ tailWord_3239784).sum := by decide
  have hdescent : baseEnd_3239784 < baseStart_3239784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239786 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_3239786 : Nat := 118140960795 + 3239786 * 2 ^ 59
def prefixEnd_3239786 : Nat := 4983230072969 + 3 ^ 40 * 3239786 * 2
def baseEnd_3239786 : Nat := 1109044957138244370717001

theorem tailTrace_3239786 : CollatzResearch.WordTrace tailWord_3239786 prefixEnd_3239786 1109044957138244370717001 := by
  unfold tailWord_3239786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29541175760204027060634803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78776468693877405495026141 29541175760204027060634803)
  ·
    refine ⟨44311763640306040590952205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29541175760204027060634803 44311763640306040590952205)
    ·
      refine ⟨16616911365114765221607077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44311763640306040590952205 16616911365114765221607077)
      ·
        refine ⟨3115670880959018479051327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16616911365114765221607077 3115670880959018479051327)
        ·
          refine ⟨4673506321438527718576991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115670880959018479051327 4673506321438527718576991)
          ·
            refine ⟨7010259482157791577865487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673506321438527718576991 7010259482157791577865487)
            ·
              refine ⟨10515389223236687366798231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010259482157791577865487 10515389223236687366798231)
              ·
                refine ⟨15773083834855031050197347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10515389223236687366798231 15773083834855031050197347)
                ·
                  refine ⟨23659625752282546575296021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15773083834855031050197347 23659625752282546575296021)
                  ·
                    refine ⟨1109044957138244370717001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23659625752282546575296021 1109044957138244370717001)
                    ·
                      rfl

theorem cell22_3239786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_3239786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239786 prefixEnd_3239786 := by exact prefixLift 3239786
  have htrace : WordTrace (prefixWord ++ tailWord_3239786) baseStart_3239786 baseEnd_3239786 := by
    simpa [prefixWord, tailWord_3239786, baseEnd_3239786] using wordTrace_append hprefix tailTrace_3239786
  have hstable : (prefixWord ++ tailWord_3239786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239786).length < 2 ^ (prefixWord ++ tailWord_3239786).sum := by decide
  have hdescent : baseEnd_3239786 < baseStart_3239786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239859 : List Nat := [1, 1, 1, 2, 3, 1, 3, 5, 1, 4]
def baseStart_3239859 : Nat := 118140960795 + 3239859 * 2 ^ 59
def prefixEnd_3239859 : Nat := 4983230072969 + 3 ^ 40 * 3239859 * 2
def baseEnd_3239859 : Nat := 1109069946530096513641777

theorem tailTrace_3239859 : CollatzResearch.WordTrace tailWord_3239859 prefixEnd_3239859 1109069946530096513641777 := by
  unfold tailWord_3239859
  simp only [CollatzResearch.WordTrace]
  refine ⟨118167365569551641709946631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78778243713034427806631087 118167365569551641709946631)
  ·
    refine ⟨177251048354327462564919947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118167365569551641709946631 177251048354327462564919947)
    ·
      refine ⟨265876572531491193847379921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177251048354327462564919947 265876572531491193847379921)
      ·
        refine ⟨199407429398618395385534941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265876572531491193847379921 199407429398618395385534941)
        ·
          refine ⟨74777786024481898269575603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199407429398618395385534941 74777786024481898269575603)
          ·
            refine ⟨112166679036722847404363405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74777786024481898269575603 112166679036722847404363405)
            ·
              refine ⟨42062504638771067776636277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112166679036722847404363405 42062504638771067776636277)
              ·
                refine ⟨3943359809884787604059651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42062504638771067776636277 3943359809884787604059651)
                ·
                  refine ⟨5915039714827181406089477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943359809884787604059651 5915039714827181406089477)
                  ·
                    refine ⟨1109069946530096513641777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915039714827181406089477 1109069946530096513641777)
                    ·
                      rfl

theorem cell22_3239859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 4].length) (baseStart_3239859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239859 prefixEnd_3239859 := by exact prefixLift 3239859
  have htrace : WordTrace (prefixWord ++ tailWord_3239859) baseStart_3239859 baseEnd_3239859 := by
    simpa [prefixWord, tailWord_3239859, baseEnd_3239859] using wordTrace_append hprefix tailTrace_3239859
  have hstable : (prefixWord ++ tailWord_3239859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239859).length < 2 ^ (prefixWord ++ tailWord_3239859).sum := by decide
  have hdescent : baseEnd_3239859 < baseStart_3239859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239889 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 6, 3]
def baseStart_3239889 : Nat := 118140960795 + 3239889 * 2 ^ 59
def prefixEnd_3239889 : Nat := 4983230072969 + 3 ^ 40 * 3239889 * 2
def baseEnd_3239889 : Nat := 1109080216143186435391685

theorem tailTrace_3239889 : CollatzResearch.WordTrace tailWord_3239889 prefixEnd_3239889 1109080216143186435391685 := by
  unfold tailWord_3239889
  simp only [CollatzResearch.WordTrace]
  refine ⟨118168459759442956833538721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78778973172961971222359147 118168459759442956833538721)
  ·
    refine ⟨88626344819582217625154041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118168459759442956833538721 88626344819582217625154041)
    ·
      refine ⟨66469758614686663218865531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88626344819582217625154041 66469758614686663218865531)
      ·
        refine ⟨99704637922029994828298297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66469758614686663218865531 99704637922029994828298297)
        ·
          refine ⟨74778478441522496121223723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99704637922029994828298297 74778478441522496121223723)
          ·
            refine ⟨112167717662283744181835585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74778478441522496121223723 112167717662283744181835585)
            ·
              refine ⟨84125788246712808136376689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112167717662283744181835585 84125788246712808136376689)
              ·
                refine ⟨63094341185034606102282517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84125788246712808136376689 63094341185034606102282517)
                ·
                  refine ⟨2957547243048497161044493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63094341185034606102282517 2957547243048497161044493)
                  ·
                    refine ⟨1109080216143186435391685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957547243048497161044493 1109080216143186435391685)
                    ·
                      rfl

theorem cell22_3239889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_3239889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239889 prefixEnd_3239889 := by exact prefixLift 3239889
  have htrace : WordTrace (prefixWord ++ tailWord_3239889) baseStart_3239889 baseEnd_3239889 := by
    simpa [prefixWord, tailWord_3239889, baseEnd_3239889] using wordTrace_append hprefix tailTrace_3239889
  have hstable : (prefixWord ++ tailWord_3239889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239889).length < 2 ^ (prefixWord ++ tailWord_3239889).sum := by decide
  have hdescent : baseEnd_3239889 < baseStart_3239889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239893 : List Nat := [1, 3, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_3239893 : Nat := 118140960795 + 3239893 * 2 ^ 59
def prefixEnd_3239893 : Nat := 4983230072969 + 3 ^ 40 * 3239893 * 2
def baseEnd_3239893 : Nat := 1109081585424931758291673

theorem tailTrace_3239893 : CollatzResearch.WordTrace tailWord_3239893 prefixEnd_3239893 1109081585424931758291673 := by
  unfold tailWord_3239893
  simp only [CollatzResearch.WordTrace]
  refine ⟨118168605651428465516684333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78779070434285643677789555 118168605651428465516684333)
  ·
    refine ⟨44313227119285674568756625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118168605651428465516684333 44313227119285674568756625)
    ·
      refine ⟨33234920339464255926567469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44313227119285674568756625 33234920339464255926567469)
      ·
        refine ⟨12463095127299095972462801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33234920339464255926567469 12463095127299095972462801)
        ·
          refine ⟨9347321345474321979347101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12463095127299095972462801 9347321345474321979347101)
          ·
            refine ⟨3505245504552870742255163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9347321345474321979347101 3505245504552870742255163)
            ·
              refine ⟨5257868256829306113382745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505245504552870742255163 5257868256829306113382745)
              ·
                refine ⟨3943401192621979585037059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5257868256829306113382745 3943401192621979585037059)
                ·
                  refine ⟨5915101788932969377555589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943401192621979585037059 5915101788932969377555589)
                  ·
                    refine ⟨1109081585424931758291673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915101788932969377555589 1109081585424931758291673)
                    ·
                      rfl

theorem cell22_3239893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_3239893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239893 prefixEnd_3239893 := by exact prefixLift 3239893
  have htrace : WordTrace (prefixWord ++ tailWord_3239893) baseStart_3239893 baseEnd_3239893 := by
    simpa [prefixWord, tailWord_3239893, baseEnd_3239893] using wordTrace_append hprefix tailTrace_3239893
  have hstable : (prefixWord ++ tailWord_3239893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239893).length < 2 ^ (prefixWord ++ tailWord_3239893).sum := by decide
  have hdescent : baseEnd_3239893 < baseStart_3239893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3239942 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3239942 : Nat := 118140960795 + 3239942 * 2 ^ 59
def prefixEnd_3239942 : Nat := 4983230072969 + 3 ^ 40 * 3239942 * 2
def baseEnd_3239942 : Nat := 369699453042103987938841

theorem tailTrace_3239942 : CollatzResearch.WordTrace tailWord_3239942 prefixEnd_3239942 369699453042103987938841 := by
  unfold tailWord_3239942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692824775882842090163065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78780261885500631256812053 3692824775882842090163065)
  ·
    refine ⟨2769618581912131567622299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3692824775882842090163065 2769618581912131567622299)
    ·
      refine ⟨4154427872868197351433449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769618581912131567622299 4154427872868197351433449)
      ·
        refine ⟨3115820904651148013575087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4154427872868197351433449 3115820904651148013575087)
        ·
          refine ⟨4673731356976722020362631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115820904651148013575087 4673731356976722020362631)
          ·
            refine ⟨7010597035465083030543947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4673731356976722020362631 7010597035465083030543947)
            ·
              refine ⟨10515895553197624545815921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7010597035465083030543947 10515895553197624545815921)
              ·
                refine ⟨7886921664898218409361941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10515895553197624545815921 7886921664898218409361941)
                ·
                  refine ⟨369699453042103987938841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7886921664898218409361941 369699453042103987938841)
                  ·
                    rfl

theorem cell22_3239942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3239942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3239942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3239942 prefixEnd_3239942 := by exact prefixLift 3239942
  have htrace : WordTrace (prefixWord ++ tailWord_3239942) baseStart_3239942 baseEnd_3239942 := by
    simpa [prefixWord, tailWord_3239942, baseEnd_3239942] using wordTrace_append hprefix tailTrace_3239942
  have hstable : (prefixWord ++ tailWord_3239942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3239942).length < 2 ^ (prefixWord ++ tailWord_3239942).sum := by decide
  have hdescent : baseEnd_3239942 < baseStart_3239942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3239942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240009 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 6]
def baseStart_3240009 : Nat := 118140960795 + 3240009 * 2 ^ 59
def prefixEnd_3240009 : Nat := 4983230072969 + 3 ^ 40 * 3240009 * 2
def baseEnd_3240009 : Nat := 369707098198515374130439

theorem tailTrace_3240009 : CollatzResearch.WordTrace tailWord_3240009 prefixEnd_3240009 369707098198515374130439 := by
  unfold tailWord_3240009
  simp only [CollatzResearch.WordTrace]
  refine ⟨118172836519008217327907081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78781891012672144885271387 118172836519008217327907081)
  ·
    refine ⟨88629627389256162995930311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118172836519008217327907081 88629627389256162995930311)
    ·
      refine ⟨132944441083884244493895467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88629627389256162995930311 132944441083884244493895467)
      ·
        refine ⟨199416661625826366740843201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132944441083884244493895467 199416661625826366740843201)
        ·
          refine ⟨149562496219369775055632401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199416661625826366740843201 149562496219369775055632401)
          ·
            refine ⟨112171872164527331291724301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149562496219369775055632401 112171872164527331291724301)
            ·
              refine ⟨42064452061697749234396613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112171872164527331291724301 42064452061697749234396613)
              ·
                refine ⟨7887084761568327981449365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42064452061697749234396613 7887084761568327981449365)
                ·
                  refine ⟨369707098198515374130439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7887084761568327981449365 369707098198515374130439)
                  ·
                    rfl

theorem cell22_3240009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 6].length) (baseStart_3240009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240009 prefixEnd_3240009 := by exact prefixLift 3240009
  have htrace : WordTrace (prefixWord ++ tailWord_3240009) baseStart_3240009 baseEnd_3240009 := by
    simpa [prefixWord, tailWord_3240009, baseEnd_3240009] using wordTrace_append hprefix tailTrace_3240009
  have hstable : (prefixWord ++ tailWord_3240009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240009).length < 2 ^ (prefixWord ++ tailWord_3240009).sum := by decide
  have hdescent : baseEnd_3240009 < baseStart_3240009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240028 : List Nat := [2, 2, 4, 1, 1, 2, 2, 3, 1, 4]
def baseStart_3240028 : Nat := 118140960795 + 3240028 * 2 ^ 59
def prefixEnd_3240028 : Nat := 4983230072969 + 3 ^ 40 * 3240028 * 2
def baseEnd_3240028 : Nat := 1109127798683836406166259

theorem tailTrace_3240028 : CollatzResearch.WordTrace tailWord_3240028 prefixEnd_3240028 1109127798683836406166259 := by
  unfold tailWord_3240028
  simp only [CollatzResearch.WordTrace]
  refine ⟨59086764752969691786424369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78782353003959589048565825 59086764752969691786424369)
  ·
    refine ⟨44315073564727268839818277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59086764752969691786424369 44315073564727268839818277)
    ·
      refine ⟨8309076293386362907465927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44315073564727268839818277 8309076293386362907465927)
      ·
        refine ⟨12463614440079544361198891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309076293386362907465927 12463614440079544361198891)
        ·
          refine ⟨18695421660119316541798337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12463614440079544361198891 18695421660119316541798337)
          ·
            refine ⟨14021566245089487406348753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18695421660119316541798337 14021566245089487406348753)
            ·
              refine ⟨10516174683817115554761565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14021566245089487406348753 10516174683817115554761565)
              ·
                refine ⟨3943565506431418333035587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10516174683817115554761565 3943565506431418333035587)
                ·
                  refine ⟨5915348259647127499553381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943565506431418333035587 5915348259647127499553381)
                  ·
                    refine ⟨1109127798683836406166259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915348259647127499553381 1109127798683836406166259)
                    ·
                      rfl

theorem cell22_3240028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_3240028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240028 prefixEnd_3240028 := by exact prefixLift 3240028
  have htrace : WordTrace (prefixWord ++ tailWord_3240028) baseStart_3240028 baseEnd_3240028 := by
    simpa [prefixWord, tailWord_3240028, baseEnd_3240028] using wordTrace_append hprefix tailTrace_3240028
  have hstable : (prefixWord ++ tailWord_3240028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240028).length < 2 ^ (prefixWord ++ tailWord_3240028).sum := by decide
  have hdescent : baseEnd_3240028 < baseStart_3240028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240041 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 4, 3]
def baseStart_3240041 : Nat := 118140960795 + 3240041 * 2 ^ 59
def prefixEnd_3240041 : Nat := 4983230072969 + 3 ^ 40 * 3240041 * 2
def baseEnd_3240041 : Nat := 1109132248849508705591219

theorem tailTrace_3240041 : CollatzResearch.WordTrace tailWord_3240041 prefixEnd_3240041 1109132248849508705591219 := by
  unfold tailWord_3240041
  simp only [CollatzResearch.WordTrace]
  refine ⟨118174003654892286793071977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78782669103261524528714651 118174003654892286793071977)
  ·
    refine ⟨88630502741169215094803983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118174003654892286793071977 88630502741169215094803983)
    ·
      refine ⟨132945754111753822642205975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88630502741169215094803983 132945754111753822642205975)
      ·
        refine ⟨199418631167630733963308963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132945754111753822642205975 199418631167630733963308963)
        ·
          refine ⟨299127946751446100944963445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199418631167630733963308963 299127946751446100944963445)
          ·
            refine ⟨28043245007948071963590323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299127946751446100944963445 28043245007948071963590323)
            ·
              refine ⟨42064867511922107945385485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28043245007948071963590323 42064867511922107945385485)
              ·
                refine ⟨15774325316970790479519557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42064867511922107945385485 15774325316970790479519557)
                ·
                  refine ⟨2957685996932023214909917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15774325316970790479519557 2957685996932023214909917)
                  ·
                    refine ⟨1109132248849508705591219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957685996932023214909917 1109132248849508705591219)
                    ·
                      rfl

theorem cell22_3240041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 4, 3].length) (baseStart_3240041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240041 prefixEnd_3240041 := by exact prefixLift 3240041
  have htrace : WordTrace (prefixWord ++ tailWord_3240041) baseStart_3240041 baseEnd_3240041 := by
    simpa [prefixWord, tailWord_3240041, baseEnd_3240041] using wordTrace_append hprefix tailTrace_3240041
  have hstable : (prefixWord ++ tailWord_3240041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240041).length < 2 ^ (prefixWord ++ tailWord_3240041).sum := by decide
  have hdescent : baseEnd_3240041 < baseStart_3240041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240094 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3240094 : Nat := 118140960795 + 3240094 * 2 ^ 59
def prefixEnd_3240094 : Nat := 4983230072969 + 3 ^ 40 * 3240094 * 2
def baseEnd_3240094 : Nat := 369716797277544744672019

theorem tailTrace_3240094 : CollatzResearch.WordTrace tailWord_3240094 prefixEnd_3240094 369716797277544744672019 := by
  unfold tailWord_3240094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771992090462534605593917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78783957815800184563167557 14771992090462534605593917)
  ·
    refine ⟨5539497033923450477097719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14771992090462534605593917 5539497033923450477097719)
    ·
      refine ⟨8309245550885175715646579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5539497033923450477097719 8309245550885175715646579)
      ·
        refine ⟨12463868326327763573469869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8309245550885175715646579 12463868326327763573469869)
        ·
          refine ⟨4673950622372911340051201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12463868326327763573469869 4673950622372911340051201)
          ·
            refine ⟨3505462966779683505038401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4673950622372911340051201 3505462966779683505038401)
            ·
              refine ⟨2629097225084762628778801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505462966779683505038401 2629097225084762628778801)
              ·
                refine ⟨1971822918813571971584101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629097225084762628778801 1971822918813571971584101)
                ·
                  refine ⟨369716797277544744672019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1971822918813571971584101 369716797277544744672019)
                  ·
                    rfl

theorem cell22_3240094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3240094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240094 prefixEnd_3240094 := by exact prefixLift 3240094
  have htrace : WordTrace (prefixWord ++ tailWord_3240094) baseStart_3240094 baseEnd_3240094 := by
    simpa [prefixWord, tailWord_3240094, baseEnd_3240094] using wordTrace_append hprefix tailTrace_3240094
  have hstable : (prefixWord ++ tailWord_3240094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240094).length < 2 ^ (prefixWord ++ tailWord_3240094).sum := by decide
  have hdescent : baseEnd_3240094 < baseStart_3240094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240150 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3240150 : Nat := 118140960795 + 3240150 * 2 ^ 59
def prefixEnd_3240150 : Nat := 4983230072969 + 3 ^ 40 * 3240150 * 2
def baseEnd_3240150 : Nat := 369723187259022918205295

theorem tailTrace_3240150 : CollatzResearch.WordTrace tailWord_3240150 prefixEnd_3240150 369723187259022918205295 := by
  unfold tailWord_3240150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7386123700718587400549369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78785319474331598939193269 7386123700718587400549369)
  ·
    refine ⟨5539592775538940550412027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7386123700718587400549369 5539592775538940550412027)
    ·
      refine ⟨8309389163308410825618041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5539592775538940550412027 8309389163308410825618041)
      ·
        refine ⟨6232041872481308119213531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8309389163308410825618041 6232041872481308119213531)
        ·
          refine ⟨9348062808721962178820297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6232041872481308119213531 9348062808721962178820297)
          ·
            refine ⟨7011047106541471634115223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9348062808721962178820297 7011047106541471634115223)
            ·
              refine ⟨10516570659812207451172835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011047106541471634115223 10516570659812207451172835)
              ·
                refine ⟨15774855989718311176759253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10516570659812207451172835 15774855989718311176759253)
                ·
                  refine ⟨369723187259022918205295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15774855989718311176759253 369723187259022918205295)
                  ·
                    rfl

theorem cell22_3240150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3240150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240150 prefixEnd_3240150 := by exact prefixLift 3240150
  have htrace : WordTrace (prefixWord ++ tailWord_3240150) baseStart_3240150 baseEnd_3240150 := by
    simpa [prefixWord, tailWord_3240150, baseEnd_3240150] using wordTrace_append hprefix tailTrace_3240150
  have hstable : (prefixWord ++ tailWord_3240150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240150).length < 2 ^ (prefixWord ++ tailWord_3240150).sum := by decide
  have hdescent : baseEnd_3240150 < baseStart_3240150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240178 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_3240178 : Nat := 118140960795 + 3240178 * 2 ^ 59
def prefixEnd_3240178 : Nat := 4983230072969 + 3 ^ 40 * 3240178 * 2
def baseEnd_3240178 : Nat := 369726382249762004971933

theorem tailTrace_3240178 : CollatzResearch.WordTrace tailWord_3240178 prefixEnd_3240178 369726382249762004971933 := by
  unfold tailWord_3240178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29544750113848989797702297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78786000303597306127206125 29544750113848989797702297)
  ·
    refine ⟨22158562585386742348276723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29544750113848989797702297 22158562585386742348276723)
    ·
      refine ⟨33237843878080113522415085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22158562585386742348276723 33237843878080113522415085)
      ·
        refine ⟨12464191454280042570905657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33237843878080113522415085 12464191454280042570905657)
        ·
          refine ⟨9348143590710031928179243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12464191454280042570905657 9348143590710031928179243)
          ·
            refine ⟨14022215386065047892268865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9348143590710031928179243 14022215386065047892268865)
            ·
              refine ⟨10516661539548785919201649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14022215386065047892268865 10516661539548785919201649)
              ·
                refine ⟨7887496154661589439401237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10516661539548785919201649 7887496154661589439401237)
                ·
                  refine ⟨369726382249762004971933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7887496154661589439401237 369726382249762004971933)
                  ·
                    rfl

theorem cell22_3240178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_3240178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240178 prefixEnd_3240178 := by exact prefixLift 3240178
  have htrace : WordTrace (prefixWord ++ tailWord_3240178) baseStart_3240178 baseEnd_3240178 := by
    simpa [prefixWord, tailWord_3240178, baseEnd_3240178] using wordTrace_append hprefix tailTrace_3240178
  have hstable : (prefixWord ++ tailWord_3240178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240178).length < 2 ^ (prefixWord ++ tailWord_3240178).sum := by decide
  have hdescent : baseEnd_3240178 < baseStart_3240178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240191 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 1, 6]
def baseStart_3240191 : Nat := 118140960795 + 3240191 * 2 ^ 59
def prefixEnd_3240191 : Nat := 4983230072969 + 3 ^ 40 * 3240191 * 2
def baseEnd_3240191 : Nat := 1109183596914958314340759

theorem tailTrace_3240191 : CollatzResearch.WordTrace tailWord_3240191 prefixEnd_3240191 1109183596914958314340759 := by
  unfold tailWord_3240191
  simp only [CollatzResearch.WordTrace]
  refine ⟨118179474604348862411032427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78786316402899241607354951 118179474604348862411032427)
  ·
    refine ⟨177269211906523293616548641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118179474604348862411032427 177269211906523293616548641)
    ·
      refine ⟨132951908929892470212411481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177269211906523293616548641 132951908929892470212411481)
      ·
        refine ⟨99713931697419352659308611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132951908929892470212411481 99713931697419352659308611)
        ·
          refine ⟨149570897546129028988962917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99713931697419352659308611 149570897546129028988962917)
          ·
            refine ⟨28044543289899192935430547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149570897546129028988962917 28044543289899192935430547)
            ·
              refine ⟨42066814934848789403145821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28044543289899192935430547 42066814934848789403145821)
              ·
                refine ⟨15775055600568296026179683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42066814934848789403145821 15775055600568296026179683)
                ·
                  refine ⟨23662583400852444039269525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15775055600568296026179683 23662583400852444039269525)
                  ·
                    refine ⟨1109183596914958314340759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23662583400852444039269525 1109183596914958314340759)
                    ·
                      rfl

theorem cell22_3240191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_3240191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240191 prefixEnd_3240191 := by exact prefixLift 3240191
  have htrace : WordTrace (prefixWord ++ tailWord_3240191) baseStart_3240191 baseEnd_3240191 := by
    simpa [prefixWord, tailWord_3240191, baseEnd_3240191] using wordTrace_append hprefix tailTrace_3240191
  have hstable : (prefixWord ++ tailWord_3240191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240191).length < 2 ^ (prefixWord ++ tailWord_3240191).sum := by decide
  have hdescent : baseEnd_3240191 < baseStart_3240191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240193 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 6, 3]
def baseStart_3240193 : Nat := 118140960795 + 3240193 * 2 ^ 59
def prefixEnd_3240193 : Nat := 4983230072969 + 3 ^ 40 * 3240193 * 2
def baseEnd_3240193 : Nat := 1109184281555830975790753

theorem tailTrace_3240193 : CollatzResearch.WordTrace tailWord_3240193 prefixEnd_3240193 1109184281555830975790753 := by
  unfold tailWord_3240193
  simp only [CollatzResearch.WordTrace]
  refine ⟨118179547550341616752605233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78786365033561077835070155 118179547550341616752605233)
  ·
    refine ⟨88634660662756212564453925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118179547550341616752605233 88634660662756212564453925)
    ·
      refine ⟨16618998874266789855835111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88634660662756212564453925 16618998874266789855835111)
      ·
        refine ⟨24928498311400184783752667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16618998874266789855835111 24928498311400184783752667)
        ·
          refine ⟨37392747467100277175629001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24928498311400184783752667 37392747467100277175629001)
          ·
            refine ⟨28044560600325207881721751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37392747467100277175629001 28044560600325207881721751)
            ·
              refine ⟨42066840900487811822582627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28044560600325207881721751 42066840900487811822582627)
              ·
                refine ⟨63100261350731717733873941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42066840900487811822582627 63100261350731717733873941)
                ·
                  refine ⟨2957824750815549268775341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63100261350731717733873941 2957824750815549268775341)
                  ·
                    refine ⟨1109184281555830975790753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957824750815549268775341 1109184281555830975790753)
                    ·
                      rfl

theorem cell22_3240193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_3240193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240193 prefixEnd_3240193 := by exact prefixLift 3240193
  have htrace : WordTrace (prefixWord ++ tailWord_3240193) baseStart_3240193 baseEnd_3240193 := by
    simpa [prefixWord, tailWord_3240193, baseEnd_3240193] using wordTrace_append hprefix tailTrace_3240193
  have hstable : (prefixWord ++ tailWord_3240193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240193).length < 2 ^ (prefixWord ++ tailWord_3240193).sum := by decide
  have hdescent : baseEnd_3240193 < baseStart_3240193 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240223 : List Nat := [1, 1, 2, 4, 3, 2, 2, 7]
def baseStart_3240223 : Nat := 118140960795 + 3240223 * 2 ^ 59
def prefixEnd_3240223 : Nat := 4983230072969 + 3 ^ 40 * 3240223 * 2
def baseEnd_3240223 : Nat := 123243839018768988615629

theorem tailTrace_3240223 : CollatzResearch.WordTrace tailWord_3240223 prefixEnd_3240223 123243839018768988615629 := by
  unfold tailWord_3240223
  simp only [CollatzResearch.WordTrace]
  refine ⟨118180641740232931876197323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78787094493488621250798215 118180641740232931876197323)
  ·
    refine ⟨177270962610349397814295985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118180641740232931876197323 177270962610349397814295985)
    ·
      refine ⟨132953221957762048360721989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177270962610349397814295985 132953221957762048360721989)
      ·
        refine ⟨24928729117080384067635373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 132953221957762048360721989 24928729117080384067635373)
        ·
          refine ⟨9348273418905144025363265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24928729117080384067635373 9348273418905144025363265)
          ·
            refine ⟨7011205064178858019022449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9348273418905144025363265 7011205064178858019022449)
            ·
              refine ⟨5258403798134143514266837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7011205064178858019022449 5258403798134143514266837)
              ·
                refine ⟨123243839018768988615629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5258403798134143514266837 123243839018768988615629)
                ·
                  rfl

theorem cell22_3240223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 7].length) (baseStart_3240223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240223 prefixEnd_3240223 := by exact prefixLift 3240223
  have htrace : WordTrace (prefixWord ++ tailWord_3240223) baseStart_3240223 baseEnd_3240223 := by
    simpa [prefixWord, tailWord_3240223, baseEnd_3240223] using wordTrace_append hprefix tailTrace_3240223
  have hstable : (prefixWord ++ tailWord_3240223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240223).length < 2 ^ (prefixWord ++ tailWord_3240223).sum := by decide
  have hdescent : baseEnd_3240223 < baseStart_3240223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240231 : List Nat := [1, 1, 8, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3240231 : Nat := 118140960795 + 3240231 * 2 ^ 59
def prefixEnd_3240231 : Nat := 4983230072969 + 3 ^ 40 * 3240231 * 2
def baseEnd_3240231 : Nat := 1109197289732411543340637

theorem tailTrace_3240231 : CollatzResearch.WordTrace tailWord_3240231 prefixEnd_3240231 1109197289732411543340637 := by
  unfold tailWord_3240231
  simp only [CollatzResearch.WordTrace]
  refine ⟨118180933524203949242488547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78787289016135966161659031 118180933524203949242488547)
  ·
    refine ⟨177271400286305923863732821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118180933524203949242488547 177271400286305923863732821)
    ·
      refine ⟨2077399222105147545278119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 177271400286305923863732821 2077399222105147545278119)
      ·
        refine ⟨3116098833157721317917179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077399222105147545278119 3116098833157721317917179)
        ·
          refine ⟨4674148249736581976875769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116098833157721317917179 4674148249736581976875769)
          ·
            refine ⟨3505611187302436482656827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674148249736581976875769 3505611187302436482656827)
            ·
              refine ⟨5258416780953654723985241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505611187302436482656827 5258416780953654723985241)
              ·
                refine ⟨3943812585715241042988931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5258416780953654723985241 3943812585715241042988931)
                ·
                  refine ⟨5915718878572861564483397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943812585715241042988931 5915718878572861564483397)
                  ·
                    refine ⟨1109197289732411543340637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915718878572861564483397 1109197289732411543340637)
                    ·
                      rfl

theorem cell22_3240231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3240231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240231 prefixEnd_3240231 := by exact prefixLift 3240231
  have htrace : WordTrace (prefixWord ++ tailWord_3240231) baseStart_3240231 baseEnd_3240231 := by
    simpa [prefixWord, tailWord_3240231, baseEnd_3240231] using wordTrace_append hprefix tailTrace_3240231
  have hstable : (prefixWord ++ tailWord_3240231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240231).length < 2 ^ (prefixWord ++ tailWord_3240231).sum := by decide
  have hdescent : baseEnd_3240231 < baseStart_3240231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240272 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 1, 3]
def baseStart_3240272 : Nat := 118140960795 + 3240272 * 2 ^ 59
def prefixEnd_3240272 : Nat := 4983230072969 + 3 ^ 40 * 3240272 * 2
def baseEnd_3240272 : Nat := 1109211324870301103065511

theorem tailTrace_3240272 : CollatzResearch.WordTrace tailWord_3240272 prefixEnd_3240272 1109211324870301103065511 := by
  unfold tailWord_3240272
  simp only [CollatzResearch.WordTrace]
  refine ⟨59091214458527706622365535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78788285944703608829820713 59091214458527706622365535)
  ·
    refine ⟨88636821687791559933548303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59091214458527706622365535 88636821687791559933548303)
    ·
      refine ⟨132955232531687339900322455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88636821687791559933548303 132955232531687339900322455)
      ·
        refine ⟨199432848797531009850483683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132955232531687339900322455 199432848797531009850483683)
        ·
          refine ⟨299149273196296514775725525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199432848797531009850483683 299149273196296514775725525)
          ·
            refine ⟨7011311090538199565056067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 299149273196296514775725525 7011311090538199565056067)
            ·
              refine ⟨10516966635807299347584101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011311090538199565056067 10516966635807299347584101)
              ·
                refine ⟨1971931244213868627672019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10516966635807299347584101 1971931244213868627672019)
                ·
                  refine ⟨2957896866320802941508029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1971931244213868627672019 2957896866320802941508029)
                  ·
                    refine ⟨1109211324870301103065511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957896866320802941508029 1109211324870301103065511)
                    ·
                      rfl

theorem cell22_3240272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 1, 3].length) (baseStart_3240272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240272 prefixEnd_3240272 := by exact prefixLift 3240272
  have htrace : WordTrace (prefixWord ++ tailWord_3240272) baseStart_3240272 baseEnd_3240272 := by
    simpa [prefixWord, tailWord_3240272, baseEnd_3240272] using wordTrace_append hprefix tailTrace_3240272
  have hstable : (prefixWord ++ tailWord_3240272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240272).length < 2 ^ (prefixWord ++ tailWord_3240272).sum := by decide
  have hdescent : baseEnd_3240272 < baseStart_3240272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240315 : List Nat := [1, 1, 1, 1, 1, 8, 1, 3, 1, 4]
def baseStart_3240315 : Nat := 118140960795 + 3240315 * 2 ^ 59
def prefixEnd_3240315 : Nat := 4983230072969 + 3 ^ 40 * 3240315 * 2
def baseEnd_3240315 : Nat := 1109226044649063324240379

theorem tailTrace_3240315 : CollatzResearch.WordTrace tailWord_3240315 prefixEnd_3240315 1109226044649063324240379 := by
  unfold tailWord_3240315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118183997255899631588546399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78789331503933087725697599 118183997255899631588546399)
  ·
    refine ⟨177275995883849447382819599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118183997255899631588546399 177275995883849447382819599)
    ·
      refine ⟨265913993825774171074229399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177275995883849447382819599 265913993825774171074229399)
      ·
        refine ⟨398870990738661256611344099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265913993825774171074229399 398870990738661256611344099)
        ·
          refine ⟨598306486107991884917016149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398870990738661256611344099 598306486107991884917016149)
          ·
            refine ⟨7011404134078029901371283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 598306486107991884917016149 7011404134078029901371283)
            ·
              refine ⟨10517106201117044852056925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011404134078029901371283 10517106201117044852056925)
              ·
                refine ⟨3943914825418891819521347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10517106201117044852056925 3943914825418891819521347)
                ·
                  refine ⟨5915872238128337729282021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3943914825418891819521347 5915872238128337729282021)
                  ·
                    refine ⟨1109226044649063324240379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5915872238128337729282021 1109226044649063324240379)
                    ·
                      rfl

theorem cell22_3240315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 4].length) (baseStart_3240315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240315 prefixEnd_3240315 := by exact prefixLift 3240315
  have htrace : WordTrace (prefixWord ++ tailWord_3240315) baseStart_3240315 baseEnd_3240315 := by
    simpa [prefixWord, tailWord_3240315, baseEnd_3240315] using wordTrace_append hprefix tailTrace_3240315
  have hstable : (prefixWord ++ tailWord_3240315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240315).length < 2 ^ (prefixWord ++ tailWord_3240315).sum := by decide
  have hdescent : baseEnd_3240315 < baseStart_3240315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240343 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 6]
def baseStart_3240343 : Nat := 118140960795 + 3240343 * 2 ^ 59
def prefixEnd_3240343 : Nat := 4983230072969 + 3 ^ 40 * 3240343 * 2
def baseEnd_3240343 : Nat := 1109235629621280584540293

theorem tailTrace_3240343 : CollatzResearch.WordTrace tailWord_3240343 prefixEnd_3240343 1109235629621280584540293 := by
  unfold tailWord_3240343
  simp only [CollatzResearch.WordTrace]
  refine ⟨118185018499798192370565683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78790012333198794913710455 118185018499798192370565683)
  ·
    refine ⟨177277527749697288555848525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118185018499798192370565683 177277527749697288555848525)
    ·
      refine ⟨66479072906136483208443197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177277527749697288555848525 66479072906136483208443197)
      ·
        refine ⟨24929652339801181203166199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66479072906136483208443197 24929652339801181203166199)
        ·
          refine ⟨37394478509701771804749299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24929652339801181203166199 37394478509701771804749299)
          ·
            refine ⟨56091717764552657707123949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37394478509701771804749299 56091717764552657707123949)
            ·
              refine ⟨21034394161707246640171481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56091717764552657707123949 21034394161707246640171481)
              ·
                refine ⟨15775795621280434980128611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21034394161707246640171481 15775795621280434980128611)
                ·
                  refine ⟨23663693431920652470192917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15775795621280434980128611 23663693431920652470192917)
                  ·
                    refine ⟨1109235629621280584540293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23663693431920652470192917 1109235629621280584540293)
                    ·
                      rfl

theorem cell22_3240343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_3240343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240343 prefixEnd_3240343 := by exact prefixLift 3240343
  have htrace : WordTrace (prefixWord ++ tailWord_3240343) baseStart_3240343 baseEnd_3240343 := by
    simpa [prefixWord, tailWord_3240343, baseEnd_3240343] using wordTrace_append hprefix tailTrace_3240343
  have hstable : (prefixWord ++ tailWord_3240343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240343).length < 2 ^ (prefixWord ++ tailWord_3240343).sum := by decide
  have hdescent : baseEnd_3240343 < baseStart_3240343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240396 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 2, 3]
def baseStart_3240396 : Nat := 118140960795 + 3240396 * 2 ^ 59
def prefixEnd_3240396 : Nat := 4983230072969 + 3 ^ 40 * 3240396 * 2
def baseEnd_3240396 : Nat := 1109253772604406112965131

theorem tailTrace_3240396 : CollatzResearch.WordTrace tailWord_3240396 prefixEnd_3240396 1109253772604406112965131 := by
  unfold tailWord_3240396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59093475784303091211122521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78791301045737454948163361 59093475784303091211122521)
  ·
    refine ⟨44320106838227318408341891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59093475784303091211122521 44320106838227318408341891)
    ·
      refine ⟨66480160257340977612512837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44320106838227318408341891 66480160257340977612512837)
      ·
        refine ⟨12465030048251433302346157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66480160257340977612512837 12465030048251433302346157)
        ·
          refine ⟨4674386268094287488379809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12465030048251433302346157 4674386268094287488379809)
          ·
            refine ⟨3505789701070715616284857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674386268094287488379809 3505789701070715616284857)
            ·
              refine ⟨2629342275803036712213643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505789701070715616284857 2629342275803036712213643)
              ·
                refine ⟨3944013413704555068320465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629342275803036712213643 3944013413704555068320465)
                ·
                  refine ⟨2958010060278416301240349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944013413704555068320465 2958010060278416301240349)
                  ·
                    refine ⟨1109253772604406112965131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958010060278416301240349 1109253772604406112965131)
                    ·
                      rfl

theorem cell22_3240396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_3240396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240396 prefixEnd_3240396 := by exact prefixLift 3240396
  have htrace : WordTrace (prefixWord ++ tailWord_3240396) baseStart_3240396 baseEnd_3240396 := by
    simpa [prefixWord, tailWord_3240396, baseEnd_3240396] using wordTrace_append hprefix tailTrace_3240396
  have hstable : (prefixWord ++ tailWord_3240396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240396).length < 2 ^ (prefixWord ++ tailWord_3240396).sum := by decide
  have hdescent : baseEnd_3240396 < baseStart_3240396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240448 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_3240448 : Nat := 118140960795 + 3240448 * 2 ^ 59
def prefixEnd_3240448 : Nat := 4983230072969 + 3 ^ 40 * 3240448 * 2
def baseEnd_3240448 : Nat := 369757191089031770221657

theorem tailTrace_3240448 : CollatzResearch.WordTrace tailWord_3240448 prefixEnd_3240448 369757191089031770221657 := by
  unfold tailWord_3240448
  simp only [CollatzResearch.WordTrace]
  refine ⟨59094424082208897651568999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78792565442945196868758665 59094424082208897651568999)
  ·
    refine ⟨88641636123313346477353499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59094424082208897651568999 88641636123313346477353499)
    ·
      refine ⟨132962454184970019716030249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88641636123313346477353499 132962454184970019716030249)
      ·
        refine ⟨99721840638727514787022687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 132962454184970019716030249 99721840638727514787022687)
        ·
          refine ⟨149582760958091272180534031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99721840638727514787022687 149582760958091272180534031)
          ·
            refine ⟨224374141437136908270801047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149582760958091272180534031 224374141437136908270801047)
            ·
              refine ⟨336561212155705362406201571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224374141437136908270801047 336561212155705362406201571)
              ·
                refine ⟨504841818233558043609302357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336561212155705362406201571 504841818233558043609302357)
                ·
                  refine ⟨369757191089031770221657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 504841818233558043609302357 369757191089031770221657)
                  ·
                    rfl

theorem cell22_3240448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_3240448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240448 prefixEnd_3240448 := by exact prefixLift 3240448
  have htrace : WordTrace (prefixWord ++ tailWord_3240448) baseStart_3240448 baseEnd_3240448 := by
    simpa [prefixWord, tailWord_3240448, baseEnd_3240448] using wordTrace_append hprefix tailTrace_3240448
  have hstable : (prefixWord ++ tailWord_3240448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240448).length < 2 ^ (prefixWord ++ tailWord_3240448).sum := by decide
  have hdescent : baseEnd_3240448 < baseStart_3240448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240452 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_3240452 : Nat := 118140960795 + 3240452 * 2 ^ 59
def prefixEnd_3240452 : Nat := 4983230072969 + 3 ^ 40 * 3240452 * 2
def baseEnd_3240452 : Nat := 1109272942548840633564959

theorem tailTrace_3240452 : CollatzResearch.WordTrace tailWord_3240452 prefixEnd_3240452 1109272942548840633564959 := by
  unfold tailWord_3240452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59094497028201651993141805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78792662704268869324189073 59094497028201651993141805)
  ·
    refine ⟨22160436385575619497428177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59094497028201651993141805 22160436385575619497428177)
    ·
      refine ⟨16620327289181714623071133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22160436385575619497428177 16620327289181714623071133)
      ·
        refine ⟨6232622733443142983651675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16620327289181714623071133 6232622733443142983651675)
        ·
          refine ⟨9348934100164714475477513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6232622733443142983651675 9348934100164714475477513)
          ·
            refine ⟨7011700575123535856608135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9348934100164714475477513 7011700575123535856608135)
            ·
              refine ⟨10517550862685303784912203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011700575123535856608135 10517550862685303784912203)
              ·
                refine ⟨15776326294027955677368305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10517550862685303784912203 15776326294027955677368305)
                ·
                  refine ⟨11832244720520966758026229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15776326294027955677368305 11832244720520966758026229)
                  ·
                    refine ⟨1109272942548840633564959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11832244720520966758026229 1109272942548840633564959)
                    ·
                      rfl

theorem cell22_3240452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_3240452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240452 prefixEnd_3240452 := by exact prefixLift 3240452
  have htrace : WordTrace (prefixWord ++ tailWord_3240452) baseStart_3240452 baseEnd_3240452 := by
    simpa [prefixWord, tailWord_3240452, baseEnd_3240452] using wordTrace_append hprefix tailTrace_3240452
  have hstable : (prefixWord ++ tailWord_3240452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240452).length < 2 ^ (prefixWord ++ tailWord_3240452).sum := by decide
  have hdescent : baseEnd_3240452 < baseStart_3240452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240546 : List Nat := [3, 3, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_3240546 : Nat := 118140960795 + 3240546 * 2 ^ 59
def prefixEnd_3240546 : Nat := 4983230072969 + 3 ^ 40 * 3240546 * 2
def baseEnd_3240546 : Nat := 1109305120669855721714671

theorem tailTrace_3240546 : CollatzResearch.WordTrace tailWord_3240546 prefixEnd_3240546 1109305120669855721714671 := by
  unfold tailWord_3240546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29548105629515689510051373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78794948345375172026803661 29548105629515689510051373)
  ·
    refine ⟨11080539611068383566269265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29548105629515689510051373 11080539611068383566269265)
    ·
      refine ⟨8310404708301287674701949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11080539611068383566269265 8310404708301287674701949)
      ·
        refine ⟨3116401765612982878013231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8310404708301287674701949 3116401765612982878013231)
        ·
          refine ⟨4674602648419474317019847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116401765612982878013231 4674602648419474317019847)
          ·
            refine ⟨7011903972629211475529771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674602648419474317019847 7011903972629211475529771)
            ·
              refine ⟨10517855958943817213294657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7011903972629211475529771 10517855958943817213294657)
              ·
                refine ⟨7888391969207862909970993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10517855958943817213294657 7888391969207862909970993)
                ·
                  refine ⟨5916293976905897182478245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888391969207862909970993 5916293976905897182478245)
                  ·
                    refine ⟨1109305120669855721714671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916293976905897182478245 1109305120669855721714671)
                    ·
                      rfl

theorem cell22_3240546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_3240546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240546 prefixEnd_3240546 := by exact prefixLift 3240546
  have htrace : WordTrace (prefixWord ++ tailWord_3240546) baseStart_3240546 baseEnd_3240546 := by
    simpa [prefixWord, tailWord_3240546, baseEnd_3240546] using wordTrace_append hprefix tailTrace_3240546
  have hstable : (prefixWord ++ tailWord_3240546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240546).length < 2 ^ (prefixWord ++ tailWord_3240546).sum := by decide
  have hdescent : baseEnd_3240546 < baseStart_3240546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240559 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 1, 3]
def baseStart_3240559 : Nat := 118140960795 + 3240559 * 2 ^ 59
def prefixEnd_3240559 : Nat := 4983230072969 + 3 ^ 40 * 3240559 * 2
def baseEnd_3240559 : Nat := 1109309570835528021139631

theorem tailTrace_3240559 : CollatzResearch.WordTrace tailWord_3240559 prefixEnd_3240559 1109309570835528021139631 := by
  unfold tailWord_3240559
  simp only [CollatzResearch.WordTrace]
  refine ⟨118192896667015661260428731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78795264444677107506952487 118192896667015661260428731)
  ·
    refine ⟨177289345000523491890643097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118192896667015661260428731 177289345000523491890643097)
    ·
      refine ⟨132967008750392618917982323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177289345000523491890643097 132967008750392618917982323)
      ·
        refine ⟨199450513125588928376973485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132967008750392618917982323 199450513125588928376973485)
        ·
          refine ⟨74793942422095848141365057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199450513125588928376973485 74793942422095848141365057)
          ·
            refine ⟨56095456816571886106023793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74793942422095848141365057 56095456816571886106023793)
            ·
              refine ⟨42071592612428914579517845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56095456816571886106023793 42071592612428914579517845)
              ·
                refine ⟨1972105903707605370914899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42071592612428914579517845 1972105903707605370914899)
                ·
                  refine ⟨2958158855561408056372349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972105903707605370914899 2958158855561408056372349)
                  ·
                    refine ⟨1109309570835528021139631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958158855561408056372349 1109309570835528021139631)
                    ·
                      rfl

theorem cell22_3240559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_3240559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240559 prefixEnd_3240559 := by exact prefixLift 3240559
  have htrace : WordTrace (prefixWord ++ tailWord_3240559) baseStart_3240559 baseEnd_3240559 := by
    simpa [prefixWord, tailWord_3240559, baseEnd_3240559] using wordTrace_append hprefix tailTrace_3240559
  have hstable : (prefixWord ++ tailWord_3240559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240559).length < 2 ^ (prefixWord ++ tailWord_3240559).sum := by decide
  have hdescent : baseEnd_3240559 < baseStart_3240559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240565 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_3240565 : Nat := 118140960795 + 3240565 * 2 ^ 59
def prefixEnd_3240565 : Nat := 4983230072969 + 3 ^ 40 * 3240565 * 2
def baseEnd_3240565 : Nat := 1109311624758146005489613

theorem tailTrace_3240565 : CollatzResearch.WordTrace tailWord_3240565 prefixEnd_3240565 1109311624758146005489613 := by
  unfold tailWord_3240565
  simp only [CollatzResearch.WordTrace]
  refine ⟨118193115504993924285147149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78795410336662616190098099 118193115504993924285147149)
  ·
    refine ⟨44322418314372721606930181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118193115504993924285147149 44322418314372721606930181)
    ·
      refine ⟨8310453433944885301299409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44322418314372721606930181 8310453433944885301299409)
      ·
        refine ⟨6232840075458663975974557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8310453433944885301299409 6232840075458663975974557)
        ·
          refine ⟨2337315028296998990990459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6232840075458663975974557 2337315028296998990990459)
          ·
            refine ⟨3505972542445498486485689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337315028296998990990459 3505972542445498486485689)
            ·
              refine ⟨2629479406834123864864267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3505972542445498486485689 2629479406834123864864267)
              ·
                refine ⟨3944219110251185797296401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629479406834123864864267 3944219110251185797296401)
                ·
                  refine ⟨2958164332688389347972301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944219110251185797296401 2958164332688389347972301)
                  ·
                    refine ⟨1109311624758146005489613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958164332688389347972301 1109311624758146005489613)
                    ·
                      rfl

theorem cell22_3240565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_3240565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240565 prefixEnd_3240565 := by exact prefixLift 3240565
  have htrace : WordTrace (prefixWord ++ tailWord_3240565) baseStart_3240565 baseEnd_3240565 := by
    simpa [prefixWord, tailWord_3240565, baseEnd_3240565] using wordTrace_append hprefix tailTrace_3240565
  have hstable : (prefixWord ++ tailWord_3240565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240565).length < 2 ^ (prefixWord ++ tailWord_3240565).sum := by decide
  have hdescent : baseEnd_3240565 < baseStart_3240565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240570 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_3240570 : Nat := 118140960795 + 3240570 * 2 ^ 59
def prefixEnd_3240570 : Nat := 4983230072969 + 3 ^ 40 * 3240570 * 2
def baseEnd_3240570 : Nat := 1109313336360327659114597

theorem tailTrace_3240570 : CollatzResearch.WordTrace tailWord_3240570 prefixEnd_3240570 1109313336360327659114597 := by
  unfold tailWord_3240570
  simp only [CollatzResearch.WordTrace]
  refine ⟨29548324467493952534769791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78795531913317206759386109 29548324467493952534769791)
  ·
    refine ⟨44322486701240928802154687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29548324467493952534769791 44322486701240928802154687)
    ·
      refine ⟨66483730051861393203232031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44322486701240928802154687 66483730051861393203232031)
      ·
        refine ⟨99725595077792089804848047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66483730051861393203232031 99725595077792089804848047)
        ·
          refine ⟨149588392616688134707272071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99725595077792089804848047 149588392616688134707272071)
          ·
            refine ⟨224382588925032202060908107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149588392616688134707272071 224382588925032202060908107)
            ·
              refine ⟨336573883387548303091362161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224382588925032202060908107 336573883387548303091362161)
              ·
                refine ⟨252430412540661227318521621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336573883387548303091362161 252430412540661227318521621)
                ·
                  refine ⟨11832675587843495030555701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 252430412540661227318521621 11832675587843495030555701)
                  ·
                    refine ⟨1109313336360327659114597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11832675587843495030555701 1109313336360327659114597)
                    ·
                      rfl

theorem cell22_3240570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_3240570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240570 prefixEnd_3240570 := by exact prefixLift 3240570
  have htrace : WordTrace (prefixWord ++ tailWord_3240570) baseStart_3240570 baseEnd_3240570 := by
    simpa [prefixWord, tailWord_3240570, baseEnd_3240570] using wordTrace_append hprefix tailTrace_3240570
  have hstable : (prefixWord ++ tailWord_3240570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240570).length < 2 ^ (prefixWord ++ tailWord_3240570).sum := by decide
  have hdescent : baseEnd_3240570 < baseStart_3240570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240632 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 8, 3]
def baseStart_3240632 : Nat := 118140960795 + 3240632 * 2 ^ 59
def prefixEnd_3240632 : Nat := 4983230072969 + 3 ^ 40 * 3240632 * 2
def baseEnd_3240632 : Nat := 1109334560227380164064407

theorem tailTrace_3240632 : CollatzResearch.WordTrace tailWord_3240632 prefixEnd_3240632 1109334560227380164064407 := by
  unfold tailWord_3240632
  simp only [CollatzResearch.WordTrace]
  refine ⟨59097779597875597363918075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78797039463834129818557433 59097779597875597363918075)
  ·
    refine ⟨88646669396813396045877113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59097779597875597363918075 88646669396813396045877113)
    ·
      refine ⟨66485002047610047034407835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88646669396813396045877113 66485002047610047034407835)
      ·
        refine ⟨99727503071415070551611753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66485002047610047034407835 99727503071415070551611753)
        ·
          refine ⟨74795627303561302913708815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99727503071415070551611753 74795627303561302913708815)
          ·
            refine ⟨112193440955341954370563223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74795627303561302913708815 112193440955341954370563223)
            ·
              refine ⟨168290161433012931555844835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112193440955341954370563223 168290161433012931555844835)
              ·
                refine ⟨252435242149519397333767253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168290161433012931555844835 252435242149519397333767253)
                ·
                  refine ⟨2958225493939680437505085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 252435242149519397333767253 2958225493939680437505085)
                  ·
                    refine ⟨1109334560227380164064407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958225493939680437505085 1109334560227380164064407)
                    ·
                      rfl

theorem cell22_3240632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_3240632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240632 prefixEnd_3240632 := by exact prefixLift 3240632
  have htrace : WordTrace (prefixWord ++ tailWord_3240632) baseStart_3240632 baseEnd_3240632 := by
    simpa [prefixWord, tailWord_3240632, baseEnd_3240632] using wordTrace_append hprefix tailTrace_3240632
  have hstable : (prefixWord ++ tailWord_3240632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240632).length < 2 ^ (prefixWord ++ tailWord_3240632).sum := by decide
  have hdescent : baseEnd_3240632 < baseStart_3240632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240647 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_3240647 : Nat := 118140960795 + 3240647 * 2 ^ 59
def prefixEnd_3240647 : Nat := 4983230072969 + 3 ^ 40 * 3240647 * 2
def baseEnd_3240647 : Nat := 1109339695033925124939361

theorem tailTrace_3240647 : CollatzResearch.WordTrace tailWord_3240647 prefixEnd_3240647 1109339695033925124939361 := by
  unfold tailWord_3240647
  simp only [CollatzResearch.WordTrace]
  refine ⟨118196106290696852289632195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78797404193797901526421463 118196106290696852289632195)
  ·
    refine ⟨177294159436045278434448293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118196106290696852289632195 177294159436045278434448293)
    ·
      refine ⟨33242654894258489706459055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177294159436045278434448293 33242654894258489706459055)
      ·
        refine ⟨49863982341387734559688583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33242654894258489706459055 49863982341387734559688583)
        ·
          refine ⟨74795973512081601839532875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49863982341387734559688583 74795973512081601839532875)
          ·
            refine ⟨112193960268122402759299313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74795973512081601839532875 112193960268122402759299313)
            ·
              refine ⟨84145470201091802069474485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112193960268122402759299313 84145470201091802069474485)
              ·
                refine ⟨7888637831352356444013233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84145470201091802069474485 7888637831352356444013233)
                ·
                  refine ⟨5916478373514267333009925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7888637831352356444013233 5916478373514267333009925)
                  ·
                    refine ⟨1109339695033925124939361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916478373514267333009925 1109339695033925124939361)
                    ·
                      rfl

theorem cell22_3240647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_3240647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240647 prefixEnd_3240647 := by exact prefixLift 3240647
  have htrace : WordTrace (prefixWord ++ tailWord_3240647) baseStart_3240647 baseEnd_3240647 := by
    simpa [prefixWord, tailWord_3240647, baseEnd_3240647] using wordTrace_append hprefix tailTrace_3240647
  have hstable : (prefixWord ++ tailWord_3240647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240647).length < 2 ^ (prefixWord ++ tailWord_3240647).sum := by decide
  have hdescent : baseEnd_3240647 < baseStart_3240647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240653 : List Nat := [1, 6, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3240653 : Nat := 118140960795 + 3240653 * 2 ^ 59
def prefixEnd_3240653 : Nat := 4983230072969 + 3 ^ 40 * 3240653 * 2
def baseEnd_3240653 : Nat := 1109341748956543109289343

theorem tailTrace_3240653 : CollatzResearch.WordTrace tailWord_3240653 prefixEnd_3240653 1109341748956543109289343 := by
  unfold tailWord_3240653
  simp only [CollatzResearch.WordTrace]
  refine ⟨118196325128675115314350613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78797550085783410209567075 118196325128675115314350613)
  ·
    refine ⟨5540452740406646030360185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118196325128675115314350613 5540452740406646030360185)
    ·
      refine ⟨4155339555304984522770139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5540452740406646030360185 4155339555304984522770139)
      ·
        refine ⟨6233009332957476784155209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4155339555304984522770139 6233009332957476784155209)
        ·
          refine ⟨4674756999718107588116407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6233009332957476784155209 4674756999718107588116407)
          ·
            refine ⟨7012135499577161382174611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674756999718107588116407 7012135499577161382174611)
            ·
              refine ⟨10518203249365742073261917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7012135499577161382174611 10518203249365742073261917)
              ·
                refine ⟨3944326218512153277473219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10518203249365742073261917 3944326218512153277473219)
                ·
                  refine ⟨5916489327768229916209829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944326218512153277473219 5916489327768229916209829)
                  ·
                    refine ⟨1109341748956543109289343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916489327768229916209829 1109341748956543109289343)
                    ·
                      rfl

theorem cell22_3240653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3240653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240653 prefixEnd_3240653 := by exact prefixLift 3240653
  have htrace : WordTrace (prefixWord ++ tailWord_3240653) baseStart_3240653 baseEnd_3240653 := by
    simpa [prefixWord, tailWord_3240653, baseEnd_3240653] using wordTrace_append hprefix tailTrace_3240653
  have hstable : (prefixWord ++ tailWord_3240653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240653).length < 2 ^ (prefixWord ++ tailWord_3240653).sum := by decide
  have hdescent : baseEnd_3240653 < baseStart_3240653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240752 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_3240752 : Nat := 118140960795 + 3240752 * 2 ^ 59
def prefixEnd_3240752 : Nat := 4983230072969 + 3 ^ 40 * 3240752 * 2
def baseEnd_3240752 : Nat := 369791879559913283688013

theorem tailTrace_3240752 : CollatzResearch.WordTrace tailWord_3240752 prefixEnd_3240752 369791879559913283688013 := by
  unfold tailWord_3240752
  simp only [CollatzResearch.WordTrace]
  refine ⟨59099967977658227611102255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78799957303544303481469673 59099967977658227611102255)
  ·
    refine ⟨88649951966487341416653383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59099967977658227611102255 88649951966487341416653383)
    ·
      refine ⟨132974927949731012124980075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88649951966487341416653383 132974927949731012124980075)
      ·
        refine ⟨199462391924596518187470113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132974927949731012124980075 199462391924596518187470113)
        ·
          refine ⟨149596793943447388640602585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199462391924596518187470113 149596793943447388640602585)
          ·
            refine ⟨112197595457585541480451939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149596793943447388640602585 112197595457585541480451939)
            ·
              refine ⟨168296393186378312220677909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112197595457585541480451939 168296393186378312220677909)
              ·
                refine ⟨7888893430611483385344277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168296393186378312220677909 7888893430611483385344277)
                ·
                  refine ⟨369791879559913283688013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7888893430611483385344277 369791879559913283688013)
                  ·
                    rfl

theorem cell22_3240752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_3240752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240752 prefixEnd_3240752 := by exact prefixLift 3240752
  have htrace : WordTrace (prefixWord ++ tailWord_3240752) baseStart_3240752 baseEnd_3240752 := by
    simpa [prefixWord, tailWord_3240752, baseEnd_3240752] using wordTrace_append hprefix tailTrace_3240752
  have hstable : (prefixWord ++ tailWord_3240752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240752).length < 2 ^ (prefixWord ++ tailWord_3240752).sum := by decide
  have hdescent : baseEnd_3240752 < baseStart_3240752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240754 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_3240754 : Nat := 118140960795 + 3240754 * 2 ^ 59
def prefixEnd_3240754 : Nat := 4983230072969 + 3 ^ 40 * 3240754 * 2
def baseEnd_3240754 : Nat := 1109376323320612512514033

theorem tailTrace_3240754 : CollatzResearch.WordTrace tailWord_3240754 prefixEnd_3240754 1109376323320612512514033 := by
  unfold tailWord_3240754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550002225327302390944329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78800005934206139709184877 29550002225327302390944329)
  ·
    refine ⟨22162501668995476793208247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29550002225327302390944329 22162501668995476793208247)
    ·
      refine ⟨33243752503493215189812371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22162501668995476793208247 33243752503493215189812371)
      ·
        refine ⟨49865628755239822784718557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33243752503493215189812371 49865628755239822784718557)
        ·
          refine ⟨18699610783214933544269459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49865628755239822784718557 18699610783214933544269459)
          ·
            refine ⟨28049416174822400316404189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18699610783214933544269459 28049416174822400316404189)
            ·
              refine ⟨10518531065558400118651571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28049416174822400316404189 10518531065558400118651571)
              ·
                refine ⟨15777796598337600177977357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10518531065558400118651571 15777796598337600177977357)
                ·
                  refine ⟨5916673724376600066741509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15777796598337600177977357 5916673724376600066741509)
                  ·
                    refine ⟨1109376323320612512514033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916673724376600066741509 1109376323320612512514033)
                    ·
                      rfl

theorem cell22_3240754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_3240754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240754 prefixEnd_3240754 := by exact prefixLift 3240754
  have htrace : WordTrace (prefixWord ++ tailWord_3240754) baseStart_3240754 baseEnd_3240754 := by
    simpa [prefixWord, tailWord_3240754, baseEnd_3240754] using wordTrace_append hprefix tailTrace_3240754
  have hstable : (prefixWord ++ tailWord_3240754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240754).length < 2 ^ (prefixWord ++ tailWord_3240754).sum := by decide
  have hdescent : baseEnd_3240754 < baseStart_3240754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240771 : List Nat := [1, 1, 1, 3, 1, 4, 5, 1, 1, 4]
def baseStart_3240771 : Nat := 118140960795 + 3240771 * 2 ^ 59
def prefixEnd_3240771 : Nat := 4983230072969 + 3 ^ 40 * 3240771 * 2
def baseEnd_3240771 : Nat := 1109382142768030134838981

theorem tailTrace_3240771 : CollatzResearch.WordTrace tailWord_3240771 prefixEnd_3240771 1109382142768030134838981 := by
  unfold tailWord_3240771
  simp only [CollatzResearch.WordTrace]
  refine ⟨118200628942247621467146167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78800419294831747644764111 118200628942247621467146167)
  ·
    refine ⟨177300943413371432200719251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118200628942247621467146167 177300943413371432200719251)
    ·
      refine ⟨265951415120057148301078877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177300943413371432200719251 265951415120057148301078877)
      ·
        refine ⟨99731780670021430612904579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 265951415120057148301078877 99731780670021430612904579)
        ·
          refine ⟨149597671005032145919356869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99731780670021430612904579 149597671005032145919356869)
          ·
            refine ⟨28049563313443527359879413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149597671005032145919356869 28049563313443527359879413)
            ·
              refine ⟨2629646560635330689988695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28049563313443527359879413 2629646560635330689988695)
              ·
                refine ⟨3944469840952996034983043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629646560635330689988695 3944469840952996034983043)
                ·
                  refine ⟨5916704761429494052474565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3944469840952996034983043 5916704761429494052474565)
                  ·
                    refine ⟨1109382142768030134838981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5916704761429494052474565 1109382142768030134838981)
                    ·
                      rfl

theorem cell22_3240771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 5, 1, 1, 4].length) (baseStart_3240771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240771 prefixEnd_3240771 := by exact prefixLift 3240771
  have htrace : WordTrace (prefixWord ++ tailWord_3240771) baseStart_3240771 baseEnd_3240771 := by
    simpa [prefixWord, tailWord_3240771, baseEnd_3240771] using wordTrace_append hprefix tailTrace_3240771
  have hstable : (prefixWord ++ tailWord_3240771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240771).length < 2 ^ (prefixWord ++ tailWord_3240771).sum := by decide
  have hdescent : baseEnd_3240771 < baseStart_3240771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240784 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 4, 3]
def baseStart_3240784 : Nat := 118140960795 + 3240784 * 2 ^ 59
def prefixEnd_3240784 : Nat := 4983230072969 + 3 ^ 40 * 3240784 * 2
def baseEnd_3240784 : Nat := 1109386592933702434263941

theorem tailTrace_3240784 : CollatzResearch.WordTrace tailWord_3240784 prefixEnd_3240784 1109386592933702434263941 := by
  unfold tailWord_3240784
  simp only [CollatzResearch.WordTrace]
  refine ⟨59100551545600262343684703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78800735394133683124912937 59100551545600262343684703)
  ·
    refine ⟨88650827318400393515527055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59100551545600262343684703 88650827318400393515527055)
    ·
      refine ⟨132976240977600590273290583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88650827318400393515527055 132976240977600590273290583)
      ·
        refine ⟨199464361466400885409935875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 132976240977600590273290583 199464361466400885409935875)
        ·
          refine ⟨299196542199601328114903813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199464361466400885409935875 299196542199601328114903813)
          ·
            refine ⟨56099351662425249021544465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299196542199601328114903813 56099351662425249021544465)
            ·
              refine ⟨42074513746818936766158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56099351662425249021544465 42074513746818936766158349)
              ·
                refine ⟨15777942655057101287309381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42074513746818936766158349 15777942655057101287309381)
                ·
                  refine ⟨2958364247823206491370509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15777942655057101287309381 2958364247823206491370509)
                  ·
                    refine ⟨1109386592933702434263941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958364247823206491370509 1109386592933702434263941)
                    ·
                      rfl

theorem cell22_3240784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 4, 3].length) (baseStart_3240784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240784 prefixEnd_3240784 := by exact prefixLift 3240784
  have htrace : WordTrace (prefixWord ++ tailWord_3240784) baseStart_3240784 baseEnd_3240784 := by
    simpa [prefixWord, tailWord_3240784, baseEnd_3240784] using wordTrace_append hprefix tailTrace_3240784
  have hstable : (prefixWord ++ tailWord_3240784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240784).length < 2 ^ (prefixWord ++ tailWord_3240784).sum := by decide
  have hdescent : baseEnd_3240784 < baseStart_3240784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240786 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 4]
def baseStart_3240786 : Nat := 118140960795 + 3240786 * 2 ^ 59
def prefixEnd_3240786 : Nat := 4983230072969 + 3 ^ 40 * 3240786 * 2
def baseEnd_3240786 : Nat := 369795759191525031904645

theorem tailTrace_3240786 : CollatzResearch.WordTrace tailWord_3240786 prefixEnd_3240786 369795759191525031904645 := by
  unfold tailWord_3240786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29550294009298319757235553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78800784024795519352628141 29550294009298319757235553)
  ·
    refine ⟨22162720506973739817926665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29550294009298319757235553 22162720506973739817926665)
    ·
      refine ⟨16622040380230304863444999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22162720506973739817926665 16622040380230304863444999)
      ·
        refine ⟨24933060570345457295167499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16622040380230304863444999 24933060570345457295167499)
        ·
          refine ⟨37399590855518185942751249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24933060570345457295167499 37399590855518185942751249)
          ·
            refine ⟨28049693141638639457063437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37399590855518185942751249 28049693141638639457063437)
            ·
              refine ⟨10518634928114489796398789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28049693141638639457063437 10518634928114489796398789)
              ·
                refine ⟨1972244049021466836824773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10518634928114489796398789 1972244049021466836824773)
                ·
                  refine ⟨369795759191525031904645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972244049021466836824773 369795759191525031904645)
                  ·
                    rfl

theorem cell22_3240786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_3240786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240786 prefixEnd_3240786 := by exact prefixLift 3240786
  have htrace : WordTrace (prefixWord ++ tailWord_3240786) baseStart_3240786 baseEnd_3240786 := by
    simpa [prefixWord, tailWord_3240786, baseEnd_3240786] using wordTrace_append hprefix tailTrace_3240786
  have hstable : (prefixWord ++ tailWord_3240786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240786).length < 2 ^ (prefixWord ++ tailWord_3240786).sum := by decide
  have hdescent : baseEnd_3240786 < baseStart_3240786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240936 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 6, 3]
def baseStart_3240936 : Nat := 118140960795 + 3240936 * 2 ^ 59
def prefixEnd_3240936 : Nat := 4983230072969 + 3 ^ 40 * 3240936 * 2
def baseEnd_3240936 : Nat := 1109438625640024704463475

theorem tailTrace_3240936 : CollatzResearch.WordTrace tailWord_3240936 prefixEnd_3240936 1109438625640024704463475 := by
  unfold tailWord_3240936
  simp only [CollatzResearch.WordTrace]
  refine ⟨59103323493324927323451331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78804431324433236431268441 59103323493324927323451331)
  ·
    refine ⟨88654985239987390985176997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59103323493324927323451331 88654985239987390985176997)
    ·
      refine ⟨16622809732497635809720687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88654985239987390985176997 16622809732497635809720687)
      ·
        refine ⟨24934214598746453714581031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16622809732497635809720687 24934214598746453714581031)
        ·
          refine ⟨37401321898119680571871547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24934214598746453714581031 37401321898119680571871547)
          ·
            refine ⟨56101982847179520857807321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37401321898119680571871547 56101982847179520857807321)
            ·
              refine ⟨42076487135384640643355491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56101982847179520857807321 42076487135384640643355491)
              ·
                refine ⟨63114730703076960965033237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42076487135384640643355491 63114730703076960965033237)
                ·
                  refine ⟨2958503001706732545235933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63114730703076960965033237 2958503001706732545235933)
                  ·
                    refine ⟨1109438625640024704463475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958503001706732545235933 1109438625640024704463475)
                    ·
                      rfl

theorem cell22_3240936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_3240936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240936 prefixEnd_3240936 := by exact prefixLift 3240936
  have htrace : WordTrace (prefixWord ++ tailWord_3240936) baseStart_3240936 baseEnd_3240936 := by
    simpa [prefixWord, tailWord_3240936, baseEnd_3240936] using wordTrace_append hprefix tailTrace_3240936
  have hstable : (prefixWord ++ tailWord_3240936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240936).length < 2 ^ (prefixWord ++ tailWord_3240936).sum := by decide
  have hdescent : baseEnd_3240936 < baseStart_3240936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240953 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 2, 3]
def baseStart_3240953 : Nat := 118140960795 + 3240953 * 2 ^ 59
def prefixEnd_3240953 : Nat := 4983230072969 + 3 ^ 40 * 3240953 * 2
def baseEnd_3240953 : Nat := 1109444445087442326788423

theorem tailTrace_3240953 : CollatzResearch.WordTrace tailWord_3240953 prefixEnd_3240953 1109444445087442326788423 := by
  unfold tailWord_3240953
  simp only [CollatzResearch.WordTrace]
  refine ⟨118207267027588266550271513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78804844685058844366847675 118207267027588266550271513)
  ·
    refine ⟨88655450270691199912703635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118207267027588266550271513 88655450270691199912703635)
    ·
      refine ⟨132983175406036799869055453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88655450270691199912703635 132983175406036799869055453)
      ·
        refine ⟨49868690777263799950895795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 132983175406036799869055453 49868690777263799950895795)
        ·
          refine ⟨74803036165895699926343693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49868690777263799950895795 74803036165895699926343693)
          ·
            refine ⟨28051138562210887472378885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74803036165895699926343693 28051138562210887472378885)
            ·
              refine ⟨5259588480414541401071041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28051138562210887472378885 5259588480414541401071041)
              ·
                refine ⟨3944691360310906050803281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5259588480414541401071041 3944691360310906050803281)
                ·
                  refine ⟨2958518520233179538102461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3944691360310906050803281 2958518520233179538102461)
                  ·
                    refine ⟨1109444445087442326788423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958518520233179538102461 1109444445087442326788423)
                    ·
                      rfl

theorem cell22_3240953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 2, 3].length) (baseStart_3240953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240953 prefixEnd_3240953 := by exact prefixLift 3240953
  have htrace : WordTrace (prefixWord ++ tailWord_3240953) baseStart_3240953 baseEnd_3240953 := by
    simpa [prefixWord, tailWord_3240953, baseEnd_3240953] using wordTrace_append hprefix tailTrace_3240953
  have hstable : (prefixWord ++ tailWord_3240953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240953).length < 2 ^ (prefixWord ++ tailWord_3240953).sum := by decide
  have hdescent : baseEnd_3240953 < baseStart_3240953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240979 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_3240979 : Nat := 118140960795 + 3240979 * 2 ^ 59
def prefixEnd_3240979 : Nat := 4983230072969 + 3 ^ 40 * 3240979 * 2
def baseEnd_3240979 : Nat := 1109453345418786925638343

theorem tailTrace_3240979 : CollatzResearch.WordTrace tailWord_3240979 prefixEnd_3240979 1109453345418786925638343 := by
  unfold tailWord_3240979
  simp only [CollatzResearch.WordTrace]
  refine ⟨118208215325494072990717991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78805476883662715327145327 118208215325494072990717991)
  ·
    refine ⟨177312322988241109486076987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118208215325494072990717991 177312322988241109486076987)
    ·
      refine ⟨265968484482361664229115481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177312322988241109486076987 265968484482361664229115481)
      ·
        refine ⟨199476363361771248171836611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265968484482361664229115481 199476363361771248171836611)
        ·
          refine ⟨299214545042656872257754917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199476363361771248171836611 299214545042656872257754917)
          ·
            refine ⟨56102727195498163548329047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299214545042656872257754917 56102727195498163548329047)
            ·
              refine ⟨84154090793247245322493571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56102727195498163548329047 84154090793247245322493571)
              ·
                refine ⟨126231136189870867983740357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84154090793247245322493571 126231136189870867983740357)
                ·
                  refine ⟨23668338035600787746951317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126231136189870867983740357 23668338035600787746951317)
                  ·
                    refine ⟨1109453345418786925638343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23668338035600787746951317 1109453345418786925638343)
                    ·
                      rfl

theorem cell22_3240979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_3240979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240979 prefixEnd_3240979 := by exact prefixLift 3240979
  have htrace : WordTrace (prefixWord ++ tailWord_3240979) baseStart_3240979 baseEnd_3240979 := by
    simpa [prefixWord, tailWord_3240979, baseEnd_3240979] using wordTrace_append hprefix tailTrace_3240979
  have hstable : (prefixWord ++ tailWord_3240979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240979).length < 2 ^ (prefixWord ++ tailWord_3240979).sum := by decide
  have hdescent : baseEnd_3240979 < baseStart_3240979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3240983 : List Nat := [1, 1, 3, 5, 1, 2, 3, 6]
def baseStart_3240983 : Nat := 118140960795 + 3240983 * 2 ^ 59
def prefixEnd_3240983 : Nat := 4983230072969 + 3 ^ 40 * 3240983 * 2
def baseEnd_3240983 : Nat := 123272746077836916504259

theorem tailTrace_3240983 : CollatzResearch.WordTrace tailWord_3240983 prefixEnd_3240983 123272746077836916504259 := by
  unfold tailWord_3240983
  simp only [CollatzResearch.WordTrace]
  refine ⟨118208361217479581673863603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78805574144986387782575735 118208361217479581673863603)
  ·
    refine ⟨177312541826219372510795405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118208361217479581673863603 177312541826219372510795405)
    ·
      refine ⟨66492203184832264691548277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177312541826219372510795405 66492203184832264691548277)
      ·
        refine ⟨6233644048578024814832651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66492203184832264691548277 6233644048578024814832651)
        ·
          refine ⟨9350466072867037222248977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6233644048578024814832651 9350466072867037222248977)
          ·
            refine ⟨7012849554650277916686733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9350466072867037222248977 7012849554650277916686733)
            ·
              refine ⟨2629818582993854218757525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7012849554650277916686733 2629818582993854218757525)
              ·
                refine ⟨123272746077836916504259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2629818582993854218757525 123272746077836916504259)
                ·
                  rfl

theorem cell22_3240983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 6].length) (baseStart_3240983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3240983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3240983 prefixEnd_3240983 := by exact prefixLift 3240983
  have htrace : WordTrace (prefixWord ++ tailWord_3240983) baseStart_3240983 baseEnd_3240983 := by
    simpa [prefixWord, tailWord_3240983, baseEnd_3240983] using wordTrace_append hprefix tailTrace_3240983
  have hstable : (prefixWord ++ tailWord_3240983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3240983).length < 2 ^ (prefixWord ++ tailWord_3240983).sum := by decide
  have hdescent : baseEnd_3240983 < baseStart_3240983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3240983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241041 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_3241041 : Nat := 118140960795 + 3241041 * 2 ^ 59
def prefixEnd_3241041 : Nat := 4983230072969 + 3 ^ 40 * 3241041 * 2
def baseEnd_3241041 : Nat := 1109474569285839430588153

theorem tailTrace_3241041 : CollatzResearch.WordTrace tailWord_3241041 prefixEnd_3241041 1109474569285839430588153 := by
  unfold tailWord_3241041
  simp only [CollatzResearch.WordTrace]
  refine ⟨118210476651269457579474977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78806984434179638386316651 118210476651269457579474977)
  ·
    refine ⟨88657857488452093184606233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118210476651269457579474977 88657857488452093184606233)
    ·
      refine ⟨66493393116339069888454675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88657857488452093184606233 66493393116339069888454675)
      ·
        refine ⟨99740089674508604832682013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66493393116339069888454675 99740089674508604832682013)
        ·
          refine ⟨37402533627940726812255755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99740089674508604832682013 37402533627940726812255755)
          ·
            refine ⟨56103800441911090218383633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37402533627940726812255755 56103800441911090218383633)
            ·
              refine ⟨42077850331433317663787725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56103800441911090218383633 42077850331433317663787725)
              ·
                refine ⟨15779193874287494123920397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42077850331433317663787725 15779193874287494123920397)
                ·
                  refine ⟨5917197702857810296470149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15779193874287494123920397 5917197702857810296470149)
                  ·
                    refine ⟨1109474569285839430588153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5917197702857810296470149 1109474569285839430588153)
                    ·
                      rfl

theorem cell22_3241041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_3241041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241041 prefixEnd_3241041 := by exact prefixLift 3241041
  have htrace : WordTrace (prefixWord ++ tailWord_3241041) baseStart_3241041 baseEnd_3241041 := by
    simpa [prefixWord, tailWord_3241041, baseEnd_3241041] using wordTrace_append hprefix tailTrace_3241041
  have hstable : (prefixWord ++ tailWord_3241041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241041).length < 2 ^ (prefixWord ++ tailWord_3241041).sum := by decide
  have hdescent : baseEnd_3241041 < baseStart_3241041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241118 : List Nat := [4, 3, 1, 1, 2, 11]
def baseStart_3241118 : Nat := 118140960795 + 3241118 * 2 ^ 59
def prefixEnd_3241118 : Nat := 4983230072969 + 3 ^ 40 * 3241118 * 2
def baseEnd_3241118 : Nat := 13697542320486875264357

theorem tailTrace_3241118 : CollatzResearch.WordTrace tailWord_3241118 prefixEnd_3241118 13697542320486875264357 := by
  unfold tailWord_3241118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776660633998812466253501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78808856714660333153352005 14776660633998812466253501)
  ·
    refine ⟨5541247737749554674845063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14776660633998812466253501 5541247737749554674845063)
    ·
      refine ⟨8311871606624332012267595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541247737749554674845063 8311871606624332012267595)
      ·
        refine ⟨12467807409936498018401393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8311871606624332012267595 12467807409936498018401393)
        ·
          refine ⟨9350855557452373513801045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12467807409936498018401393 9350855557452373513801045)
          ·
            refine ⟨13697542320486875264357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9350855557452373513801045 13697542320486875264357)
            ·
              rfl

theorem cell22_3241118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 11].length) (baseStart_3241118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241118 prefixEnd_3241118 := by exact prefixLift 3241118
  have htrace : WordTrace (prefixWord ++ tailWord_3241118) baseStart_3241118 baseEnd_3241118 := by
    simpa [prefixWord, tailWord_3241118, baseEnd_3241118] using wordTrace_append hprefix tailTrace_3241118
  have hstable : (prefixWord ++ tailWord_3241118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241118).length < 2 ^ (prefixWord ++ tailWord_3241118).sum := by decide
  have hdescent : baseEnd_3241118 < baseStart_3241118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241146 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_3241146 : Nat := 118140960795 + 3241146 * 2 ^ 59
def prefixEnd_3241146 : Nat := 4983230072969 + 3 ^ 40 * 3241146 * 2
def baseEnd_3241146 : Nat := 369836837643884718904277

theorem tailTrace_3241146 : CollatzResearch.WordTrace tailWord_3241146 prefixEnd_3241146 369836837643884718904277 := by
  unfold tailWord_3241146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29553576578972265128011823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78809537543926040341364861 29553576578972265128011823)
  ·
    refine ⟨44330364868458397692017735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29553576578972265128011823 44330364868458397692017735)
    ·
      refine ⟨66495547302687596538026603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44330364868458397692017735 66495547302687596538026603)
      ·
        refine ⟨99743320954031394807039905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66495547302687596538026603 99743320954031394807039905)
        ·
          refine ⟨74807490715523546105279929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99743320954031394807039905 74807490715523546105279929)
          ·
            refine ⟨56105618036642659578959947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74807490715523546105279929 56105618036642659578959947)
            ·
              refine ⟨84158427054963989368439921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56105618036642659578959947 84158427054963989368439921)
              ·
                refine ⟨63118820291222992026329941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84158427054963989368439921 63118820291222992026329941)
                ·
                  refine ⟨369836837643884718904277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63118820291222992026329941 369836837643884718904277)
                  ·
                    rfl

theorem cell22_3241146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_3241146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241146 prefixEnd_3241146 := by exact prefixLift 3241146
  have htrace : WordTrace (prefixWord ++ tailWord_3241146) baseStart_3241146 baseEnd_3241146 := by
    simpa [prefixWord, tailWord_3241146, baseEnd_3241146] using wordTrace_append hprefix tailTrace_3241146
  have hstable : (prefixWord ++ tailWord_3241146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241146).length < 2 ^ (prefixWord ++ tailWord_3241146).sum := by decide
  have hdescent : baseEnd_3241146 < baseStart_3241146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241150 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_3241150 : Nat := 118140960795 + 3241150 * 2 ^ 59
def prefixEnd_3241150 : Nat := 4983230072969 + 3 ^ 40 * 3241150 * 2
def baseEnd_3241150 : Nat := 1109511882213399479612819

theorem tailTrace_3241150 : CollatzResearch.WordTrace tailWord_3241150 prefixEnd_3241150 1109511882213399479612819 := by
  unfold tailWord_3241150
  simp only [CollatzResearch.WordTrace]
  refine ⟨14776806525984321149399113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78809634805249712796795269 14776806525984321149399113)
  ·
    refine ⟨11082604894488240862049335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14776806525984321149399113 11082604894488240862049335)
    ·
      refine ⟨16623907341732361293074003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082604894488240862049335 16623907341732361293074003)
      ·
        refine ⟨24935861012598541939611005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16623907341732361293074003 24935861012598541939611005)
        ·
          refine ⟨9350947879724453227354127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24935861012598541939611005 9350947879724453227354127)
          ·
            refine ⟨14026421819586679841031191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9350947879724453227354127 14026421819586679841031191)
            ·
              refine ⟨21039632729380019761546787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14026421819586679841031191 21039632729380019761546787)
              ·
                refine ⟨31559449094070029642320181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21039632729380019761546787 31559449094070029642320181)
                ·
                  refine ⟨2958698352569065278967517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31559449094070029642320181 2958698352569065278967517)
                  ·
                    refine ⟨1109511882213399479612819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958698352569065278967517 1109511882213399479612819)
                    ·
                      rfl

theorem cell22_3241150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_3241150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241150 prefixEnd_3241150 := by exact prefixLift 3241150
  have htrace : WordTrace (prefixWord ++ tailWord_3241150) baseStart_3241150 baseEnd_3241150 := by
    simpa [prefixWord, tailWord_3241150, baseEnd_3241150] using wordTrace_append hprefix tailTrace_3241150
  have hstable : (prefixWord ++ tailWord_3241150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241150).length < 2 ^ (prefixWord ++ tailWord_3241150).sum := by decide
  have hdescent : baseEnd_3241150 < baseStart_3241150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241197 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3241197 : Nat := 118140960795 + 3241197 * 2 ^ 59
def prefixEnd_3241197 : Nat := 4983230072969 + 3 ^ 40 * 3241197 * 2
def baseEnd_3241197 : Nat := 369842657091302341229225

theorem tailTrace_3241197 : CollatzResearch.WordTrace tailWord_3241197 prefixEnd_3241197 369842657091302341229225 := by
  unfold tailWord_3241197
  simp only [CollatzResearch.WordTrace]
  refine ⟨118216166438704296222153845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78810777625802864148102563 118216166438704296222153845)
  ·
    refine ⟨11082765603628527770826923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118216166438704296222153845 11082765603628527770826923)
    ·
      refine ⟨16624148405442791656240385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11082765603628527770826923 16624148405442791656240385)
      ·
        refine ⟨12468111304082093742180289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16624148405442791656240385 12468111304082093742180289)
        ·
          refine ⟨9351083478061570306635217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12468111304082093742180289 9351083478061570306635217)
          ·
            refine ⟨7013312608546177729976413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9351083478061570306635217 7013312608546177729976413)
            ·
              refine ⟨2629992228204816648741155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7013312608546177729976413 2629992228204816648741155)
              ·
                refine ⟨3944988342307224973111733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2629992228204816648741155 3944988342307224973111733)
                ·
                  refine ⟨369842657091302341229225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3944988342307224973111733 369842657091302341229225)
                  ·
                    rfl

theorem cell22_3241197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3241197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241197 prefixEnd_3241197 := by exact prefixLift 3241197
  have htrace : WordTrace (prefixWord ++ tailWord_3241197) baseStart_3241197 baseEnd_3241197 := by
    simpa [prefixWord, tailWord_3241197, baseEnd_3241197] using wordTrace_append hprefix tailTrace_3241197
  have hstable : (prefixWord ++ tailWord_3241197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241197).length < 2 ^ (prefixWord ++ tailWord_3241197).sum := by decide
  have hdescent : baseEnd_3241197 < baseStart_3241197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241210 : List Nat := [3, 1, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_3241210 : Nat := 118140960795 + 3241210 * 2 ^ 59
def prefixEnd_3241210 : Nat := 4983230072969 + 3 ^ 40 * 3241210 * 2
def baseEnd_3241210 : Nat := 1109532421439579323112635

theorem tailTrace_3241210 : CollatzResearch.WordTrace tailWord_3241210 prefixEnd_3241210 1109532421439579323112635 := by
  unfold tailWord_3241210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29554160146914299860594271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78811093725104799628251389 29554160146914299860594271)
  ·
    refine ⟨44331240220371449790891407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29554160146914299860594271 44331240220371449790891407)
    ·
      refine ⟨66496860330557174686337111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44331240220371449790891407 66496860330557174686337111)
      ·
        refine ⟨99745290495835762029505667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66496860330557174686337111 99745290495835762029505667)
        ·
          refine ⟨149617935743753643044258501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99745290495835762029505667 149617935743753643044258501)
          ·
            refine ⟨28053362951953808070798469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149617935743753643044258501 28053362951953808070798469)
            ·
              refine ⟨5260005553491339013274713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28053362951953808070798469 5260005553491339013274713)
              ·
                refine ⟨3945004165118504259956035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5260005553491339013274713 3945004165118504259956035)
                ·
                  refine ⟨5917506247677756389934053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945004165118504259956035 5917506247677756389934053)
                  ·
                    refine ⟨1109532421439579323112635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5917506247677756389934053 1109532421439579323112635)
                    ·
                      rfl

theorem cell22_3241210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_3241210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241210 prefixEnd_3241210 := by exact prefixLift 3241210
  have htrace : WordTrace (prefixWord ++ tailWord_3241210) baseStart_3241210 baseEnd_3241210 := by
    simpa [prefixWord, tailWord_3241210, baseEnd_3241210] using wordTrace_append hprefix tailTrace_3241210
  have hstable : (prefixWord ++ tailWord_3241210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241210).length < 2 ^ (prefixWord ++ tailWord_3241210).sum := by decide
  have hdescent : baseEnd_3241210 < baseStart_3241210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241218 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_3241218 : Nat := 118140960795 + 3241218 * 2 ^ 59
def prefixEnd_3241218 : Nat := 4983230072969 + 3 ^ 40 * 3241218 * 2
def baseEnd_3241218 : Nat := 1109535160003069968912611

theorem tailTrace_3241218 : CollatzResearch.WordTrace tailWord_3241218 prefixEnd_3241218 1109535160003069968912611 := by
  unfold tailWord_3241218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29554233092907054202167077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78811288247752144539112205 29554233092907054202167077)
  ·
    refine ⟨5541418704920072662906327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29554233092907054202167077 5541418704920072662906327)
    ·
      refine ⟨8312128057380108994359491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541418704920072662906327 8312128057380108994359491)
      ·
        refine ⟨12468192086070163491539237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312128057380108994359491 12468192086070163491539237)
        ·
          refine ⟨2337786016138155654663607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12468192086070163491539237 2337786016138155654663607)
          ·
            refine ⟨3506679024207233481995411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2337786016138155654663607 3506679024207233481995411)
            ·
              refine ⟨5260018536310850222993117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3506679024207233481995411 5260018536310850222993117)
              ·
                refine ⟨1972506951116568833622419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260018536310850222993117 1972506951116568833622419)
                ·
                  refine ⟨2958760426674853250433629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1972506951116568833622419 2958760426674853250433629)
                  ·
                    refine ⟨1109535160003069968912611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958760426674853250433629 1109535160003069968912611)
                    ·
                      rfl

theorem cell22_3241218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_3241218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241218 prefixEnd_3241218 := by exact prefixLift 3241218
  have htrace : WordTrace (prefixWord ++ tailWord_3241218) baseStart_3241218 baseEnd_3241218 := by
    simpa [prefixWord, tailWord_3241218, baseEnd_3241218] using wordTrace_append hprefix tailTrace_3241218
  have hstable : (prefixWord ++ tailWord_3241218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241218).length < 2 ^ (prefixWord ++ tailWord_3241218).sum := by decide
  have hdescent : baseEnd_3241218 < baseStart_3241218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241240 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 4, 3]
def baseStart_3241240 : Nat := 118140960795 + 3241240 * 2 ^ 59
def prefixEnd_3241240 : Nat := 4983230072969 + 3 ^ 40 * 3241240 * 2
def baseEnd_3241240 : Nat := 1109542691052669244862543

theorem tailTrace_3241240 : CollatzResearch.WordTrace tailWord_3241240 prefixEnd_3241240 1109542691052669244862543 := by
  unfold tailWord_3241240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59108867388774257282984587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78811823185032343043979449 59108867388774257282984587)
  ·
    refine ⟨88663301083161385924476881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59108867388774257282984587 88663301083161385924476881)
    ·
      refine ⟨66497475812371039443357661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88663301083161385924476881 66497475812371039443357661)
      ·
        refine ⟨24936553429639139791259123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66497475812371039443357661 24936553429639139791259123)
        ·
          refine ⟨37404830144458709686888685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24936553429639139791259123 37404830144458709686888685)
          ·
            refine ⟨14026811304172016132583257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37404830144458709686888685 14026811304172016132583257)
            ·
              refine ⟨10520108478129012099437443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14026811304172016132583257 10520108478129012099437443)
              ·
                refine ⟨15780162717193518149156165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520108478129012099437443 15780162717193518149156165)
                ·
                  refine ⟨2958780509473784652966781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15780162717193518149156165 2958780509473784652966781)
                  ·
                    refine ⟨1109542691052669244862543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2958780509473784652966781 1109542691052669244862543)
                    ·
                      rfl

theorem cell22_3241240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_3241240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241240 prefixEnd_3241240 := by exact prefixLift 3241240
  have htrace : WordTrace (prefixWord ++ tailWord_3241240) baseStart_3241240 baseEnd_3241240 := by
    simpa [prefixWord, tailWord_3241240, baseEnd_3241240] using wordTrace_append hprefix tailTrace_3241240
  have hstable : (prefixWord ++ tailWord_3241240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241240).length < 2 ^ (prefixWord ++ tailWord_3241240).sum := by decide
  have hdescent : baseEnd_3241240 < baseStart_3241240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241253 : List Nat := [1, 3, 1, 2, 4, 1, 1, 9]
def baseStart_3241253 : Nat := 118140960795 + 3241253 * 2 ^ 59
def prefixEnd_3241253 : Nat := 4983230072969 + 3 ^ 40 * 3241253 * 2
def baseEnd_3241253 : Nat := 123283015690926838254167

theorem tailTrace_3241253 : CollatzResearch.WordTrace tailWord_3241253 prefixEnd_3241253 123283015690926838254167 := by
  unfold tailWord_3241253
  simp only [CollatzResearch.WordTrace]
  refine ⟨118218208926501417786192413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78812139284334278524128275 118218208926501417786192413)
  ·
    refine ⟨44331828347438031669822155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118218208926501417786192413 44331828347438031669822155)
    ·
      refine ⟨66497742521157047504733233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44331828347438031669822155 66497742521157047504733233)
      ·
        refine ⟨49873306890867785628549925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66497742521157047504733233 49873306890867785628549925)
        ·
          refine ⟨9351245042037709805353111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49873306890867785628549925 9351245042037709805353111)
          ·
            refine ⟨14026867563056564708029667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9351245042037709805353111 14026867563056564708029667)
            ·
              refine ⟨21040301344584847062044501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14026867563056564708029667 21040301344584847062044501)
              ·
                refine ⟨123283015690926838254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21040301344584847062044501 123283015690926838254167)
                ·
                  rfl

theorem cell22_3241253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 9].length) (baseStart_3241253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241253 prefixEnd_3241253 := by exact prefixLift 3241253
  have htrace : WordTrace (prefixWord ++ tailWord_3241253) baseStart_3241253 baseEnd_3241253 := by
    simpa [prefixWord, tailWord_3241253, baseEnd_3241253] using wordTrace_append hprefix tailTrace_3241253
  have hstable : (prefixWord ++ tailWord_3241253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241253).length < 2 ^ (prefixWord ++ tailWord_3241253).sum := by decide
  have hdescent : baseEnd_3241253 < baseStart_3241253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241293 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3241293 : Nat := 118140960795 + 3241293 * 2 ^ 59
def prefixEnd_3241293 : Nat := 4983230072969 + 3 ^ 40 * 3241293 * 2
def baseEnd_3241293 : Nat := 369853611345264924429127

theorem tailTrace_3241293 : CollatzResearch.WordTrace tailWord_3241293 prefixEnd_3241293 369853611345264924429127 := by
  unfold tailWord_3241293
  simp only [CollatzResearch.WordTrace]
  refine ⟨118219667846356504617648533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78813111897571003078432355 118219667846356504617648533)
  ·
    refine ⟨5541546930297961153952275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 118219667846356504617648533 5541546930297961153952275)
    ·
      refine ⟨8312320395446941730928413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5541546930297961153952275 8312320395446941730928413)
      ·
        refine ⟨3117120148292603149098155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8312320395446941730928413 3117120148292603149098155)
        ·
          refine ⟨4675680222438904723647233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3117120148292603149098155 4675680222438904723647233)
          ·
            refine ⟨3506760166829178542735425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4675680222438904723647233 3506760166829178542735425)
            ·
              refine ⟨2630070125121883907051569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3506760166829178542735425 2630070125121883907051569)
              ·
                refine ⟨1972552593841412930288677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2630070125121883907051569 1972552593841412930288677)
                ·
                  refine ⟨369853611345264924429127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972552593841412930288677 369853611345264924429127)
                  ·
                    rfl

theorem cell22_3241293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3241293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241293 prefixEnd_3241293 := by exact prefixLift 3241293
  have htrace : WordTrace (prefixWord ++ tailWord_3241293) baseStart_3241293 baseEnd_3241293 := by
    simpa [prefixWord, tailWord_3241293, baseEnd_3241293] using wordTrace_append hprefix tailTrace_3241293
  have hstable : (prefixWord ++ tailWord_3241293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241293).length < 2 ^ (prefixWord ++ tailWord_3241293).sum := by decide
  have hdescent : baseEnd_3241293 < baseStart_3241293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241315 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 5]
def baseStart_3241315 : Nat := 118140960795 + 3241315 * 2 ^ 59
def prefixEnd_3241315 : Nat := 4983230072969 + 3 ^ 40 * 3241315 * 2
def baseEnd_3241315 : Nat := 369856121695131349745771

theorem tailTrace_3241315 : CollatzResearch.WordTrace tailWord_3241315 prefixEnd_3241315 369856121695131349745771 := by
  unfold tailWord_3241315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118220470252276802374949399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78813646834851201583299599 118220470252276802374949399)
  ·
    refine ⟨177330705378415203562424099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118220470252276802374949399 177330705378415203562424099)
    ·
      refine ⟨265996058067622805343636149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177330705378415203562424099 265996058067622805343636149)
      ·
        refine ⟨24937130443839638000965889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 265996058067622805343636149 24937130443839638000965889)
        ·
          refine ⟨18702847832879728500724417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24937130443839638000965889 18702847832879728500724417)
          ·
            refine ⟨14027135874659796375543313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18702847832879728500724417 14027135874659796375543313)
            ·
              refine ⟨10520351905994847281657485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14027135874659796375543313 10520351905994847281657485)
              ·
                refine ⟨3945131964748067730621557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10520351905994847281657485 3945131964748067730621557)
                ·
                  refine ⟨369856121695131349745771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3945131964748067730621557 369856121695131349745771)
                  ·
                    rfl

theorem cell22_3241315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 5].length) (baseStart_3241315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241315 prefixEnd_3241315 := by exact prefixLift 3241315
  have htrace : WordTrace (prefixWord ++ tailWord_3241315) baseStart_3241315 baseEnd_3241315 := by
    simpa [prefixWord, tailWord_3241315, baseEnd_3241315] using wordTrace_append hprefix tailTrace_3241315
  have hstable : (prefixWord ++ tailWord_3241315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241315).length < 2 ^ (prefixWord ++ tailWord_3241315).sum := by decide
  have hdescent : baseEnd_3241315 < baseStart_3241315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241465 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_3241465 : Nat := 118140960795 + 3241465 * 2 ^ 59
def prefixEnd_3241465 : Nat := 4983230072969 + 3 ^ 40 * 3241465 * 2
def baseEnd_3241465 : Nat := 1109619713150843657986853

theorem tailTrace_3241465 : CollatzResearch.WordTrace tailWord_3241465 prefixEnd_3241465 1109619713150843657986853 := by
  unfold tailWord_3241465
  simp only [CollatzResearch.WordTrace]
  refine ⟨118225941201733377992909849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78817294134488918661939899 118225941201733377992909849)
  ·
    refine ⟨88669455901300033494682387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118225941201733377992909849 88669455901300033494682387)
    ·
      refine ⟨133004183851950050242023581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88669455901300033494682387 133004183851950050242023581)
      ·
        refine ⟨49876568944481268840758843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133004183851950050242023581 49876568944481268840758843)
        ·
          refine ⟨74814853416721903261138265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49876568944481268840758843 74814853416721903261138265)
          ·
            refine ⟨56111140062541427445853699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74814853416721903261138265 56111140062541427445853699)
            ·
              refine ⟨84166710093812141168780549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56111140062541427445853699 84166710093812141168780549)
              ·
                refine ⟨15781258142589776469146353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84166710093812141168780549 15781258142589776469146353)
                ·
                  refine ⟨11835943606942332351859765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15781258142589776469146353 11835943606942332351859765)
                  ·
                    refine ⟨1109619713150843657986853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11835943606942332351859765 1109619713150843657986853)
                    ·
                      rfl

theorem cell22_3241465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_3241465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241465 prefixEnd_3241465 := by exact prefixLift 3241465
  have htrace : WordTrace (prefixWord ++ tailWord_3241465) baseStart_3241465 baseEnd_3241465 := by
    simpa [prefixWord, tailWord_3241465, baseEnd_3241465] using wordTrace_append hprefix tailTrace_3241465
  have hstable : (prefixWord ++ tailWord_3241465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241465).length < 2 ^ (prefixWord ++ tailWord_3241465).sum := by decide
  have hdescent : baseEnd_3241465 < baseStart_3241465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241482 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_3241482 : Nat := 118140960795 + 3241482 * 2 ^ 59
def prefixEnd_3241482 : Nat := 4983230072969 + 3 ^ 40 * 3241482 * 2
def baseEnd_3241482 : Nat := 1109625532598261280311801

theorem tailTrace_3241482 : CollatzResearch.WordTrace tailWord_3241482 prefixEnd_3241482 1109625532598261280311801 := by
  unfold tailWord_3241482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29556640310667947474069675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78817707495114526597519133 29556640310667947474069675)
  ·
    refine ⟨44334960466001921211104513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29556640310667947474069675 44334960466001921211104513)
    ·
      refine ⟨33251220349501440908328385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44334960466001921211104513 33251220349501440908328385)
      ·
        refine ⟨24938415262126080681246289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33251220349501440908328385 24938415262126080681246289)
        ·
          refine ⟨18703811446594560510934717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24938415262126080681246289 18703811446594560510934717)
          ·
            refine ⟨7013929292472960191600519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18703811446594560510934717 7013929292472960191600519)
            ·
              refine ⟨10520893938709440287400779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7013929292472960191600519 10520893938709440287400779)
              ·
                refine ⟨15781340908064160431101169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10520893938709440287400779 15781340908064160431101169)
                ·
                  refine ⟨11836005681048120323325877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15781340908064160431101169 11836005681048120323325877)
                  ·
                    refine ⟨1109625532598261280311801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11836005681048120323325877 1109625532598261280311801)
                    ·
                      rfl

theorem cell22_3241482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_3241482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241482 prefixEnd_3241482 := by exact prefixLift 3241482
  have htrace : WordTrace (prefixWord ++ tailWord_3241482) baseStart_3241482 baseEnd_3241482 := by
    simpa [prefixWord, tailWord_3241482, baseEnd_3241482] using wordTrace_append hprefix tailTrace_3241482
  have hstable : (prefixWord ++ tailWord_3241482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241482).length < 2 ^ (prefixWord ++ tailWord_3241482).sum := by decide
  have hdescent : baseEnd_3241482 < baseStart_3241482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241514 : List Nat := [3, 1, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_3241514 : Nat := 118140960795 + 3241514 * 2 ^ 59
def prefixEnd_3241514 : Nat := 4983230072969 + 3 ^ 40 * 3241514 * 2
def baseEnd_3241514 : Nat := 1109636486852223863511703

theorem tailTrace_3241514 : CollatzResearch.WordTrace tailWord_3241514 prefixEnd_3241514 1109636486852223863511703 := by
  unfold tailWord_3241514
  simp only [CollatzResearch.WordTrace]
  refine ⟨29556932094638964840360899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78818485585703906240962397 29556932094638964840360899)
  ·
    refine ⟨44335398141958447260541349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29556932094638964840360899 44335398141958447260541349)
    ·
      refine ⟨8312887151617208861351503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44335398141958447260541349 8312887151617208861351503)
      ·
        refine ⟨12469330727425813292027255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8312887151617208861351503 12469330727425813292027255)
        ·
          refine ⟨18703996091138719938040883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469330727425813292027255 18703996091138719938040883)
          ·
            refine ⟨28055994136708079907061325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18703996091138719938040883 28055994136708079907061325)
            ·
              refine ⟨10520997801265529965147997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28055994136708079907061325 10520997801265529965147997)
              ·
                refine ⟨3945374175474573736930499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10520997801265529965147997 3945374175474573736930499)
                ·
                  refine ⟨5918061263211860605395749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945374175474573736930499 5918061263211860605395749)
                  ·
                    refine ⟨1109636486852223863511703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5918061263211860605395749 1109636486852223863511703)
                    ·
                      rfl

theorem cell22_3241514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_3241514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241514 prefixEnd_3241514 := by exact prefixLift 3241514
  have htrace : WordTrace (prefixWord ++ tailWord_3241514) baseStart_3241514 baseEnd_3241514 := by
    simpa [prefixWord, tailWord_3241514, baseEnd_3241514] using wordTrace_append hprefix tailTrace_3241514
  have hstable : (prefixWord ++ tailWord_3241514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241514).length < 2 ^ (prefixWord ++ tailWord_3241514).sum := by decide
  have hdescent : baseEnd_3241514 < baseStart_3241514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241529 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 4]
def baseStart_3241529 : Nat := 118140960795 + 3241529 * 2 ^ 59
def prefixEnd_3241529 : Nat := 4983230072969 + 3 ^ 40 * 3241529 * 2
def baseEnd_3241529 : Nat := 369880540552922941462219

theorem tailTrace_3241529 : CollatzResearch.WordTrace tailWord_3241529 prefixEnd_3241529 369880540552922941462219 := by
  unfold tailWord_3241529
  simp only [CollatzResearch.WordTrace]
  refine ⟨118228275473501516923239641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78818850315667677948826427 118228275473501516923239641)
  ·
    refine ⟨88671206605126137692429731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118228275473501516923239641 88671206605126137692429731)
    ·
      refine ⟨133006809907689206538644597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88671206605126137692429731 133006809907689206538644597)
      ·
        refine ⟨12469388428845863112997931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133006809907689206538644597 12469388428845863112997931)
        ·
          refine ⟨18704082643268794669496897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12469388428845863112997931 18704082643268794669496897)
          ·
            refine ⟨14028061982451596002122673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18704082643268794669496897 14028061982451596002122673)
            ·
              refine ⟨10521046486838697001592005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14028061982451596002122673 10521046486838697001592005)
              ·
                refine ⟨1972696216282255687798501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10521046486838697001592005 1972696216282255687798501)
                ·
                  refine ⟨369880540552922941462219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972696216282255687798501 369880540552922941462219)
                  ·
                    rfl

theorem cell22_3241529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 4].length) (baseStart_3241529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241529 prefixEnd_3241529 := by exact prefixLift 3241529
  have htrace : WordTrace (prefixWord ++ tailWord_3241529) baseStart_3241529 baseEnd_3241529 := by
    simpa [prefixWord, tailWord_3241529, baseEnd_3241529] using wordTrace_append hprefix tailTrace_3241529
  have hstable : (prefixWord ++ tailWord_3241529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241529).length < 2 ^ (prefixWord ++ tailWord_3241529).sum := by decide
  have hdescent : baseEnd_3241529 < baseStart_3241529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241647 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 6]
def baseStart_3241647 : Nat := 118140960795 + 3241647 * 2 ^ 59
def prefixEnd_3241647 : Nat := 4983230072969 + 3 ^ 40 * 3241647 * 2
def baseEnd_3241647 : Nat := 369894005156751949978765

theorem tailTrace_3241647 : CollatzResearch.WordTrace tailWord_3241647 prefixEnd_3241647 369894005156751949978765 := by
  unfold tailWord_3241647
  simp only [CollatzResearch.WordTrace]
  refine ⟨118232579287074023076035195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78821719524716015384023463 118232579287074023076035195)
  ·
    refine ⟨177348868930611034614052793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118232579287074023076035195 177348868930611034614052793)
    ·
      refine ⟨133011651697958275960539595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177348868930611034614052793 133011651697958275960539595)
      ·
        refine ⟨199517477546937413940809393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133011651697958275960539595 199517477546937413940809393)
        ·
          refine ⟨149638108160203060455607045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199517477546937413940809393 149638108160203060455607045)
          ·
            refine ⟨28057145280038073835426321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149638108160203060455607045 28057145280038073835426321)
            ·
              refine ⟨21042858960028555376569741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28057145280038073835426321 21042858960028555376569741)
              ·
                refine ⟨7891072110010708266213653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21042858960028555376569741 7891072110010708266213653)
                ·
                  refine ⟨369894005156751949978765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7891072110010708266213653 369894005156751949978765)
                  ·
                    rfl

theorem cell22_3241647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_3241647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241647 prefixEnd_3241647 := by exact prefixLift 3241647
  have htrace : WordTrace (prefixWord ++ tailWord_3241647) baseStart_3241647 baseEnd_3241647 := by
    simpa [prefixWord, tailWord_3241647, baseEnd_3241647] using wordTrace_append hprefix tailTrace_3241647
  have hstable : (prefixWord ++ tailWord_3241647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241647).length < 2 ^ (prefixWord ++ tailWord_3241647).sum := by decide
  have hdescent : baseEnd_3241647 < baseStart_3241647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241681 : List Nat := [1, 2, 2, 1, 2, 5, 2, 3, 4]
def baseStart_3241681 : Nat := 118140960795 + 3241681 * 2 ^ 59
def prefixEnd_3241681 : Nat := 4983230072969 + 3 ^ 40 * 3241681 * 2
def baseEnd_3241681 : Nat := 369897884788363698195397

theorem tailTrace_3241681 : CollatzResearch.WordTrace tailWord_3241681 prefixEnd_3241681 369897884788363698195397 := by
  unfold tailWord_3241681
  simp only [CollatzResearch.WordTrace]
  refine ⟨118233819368950846882772897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78822546245967231255181931 118233819368950846882772897)
  ·
    refine ⟨88675364526713135162079673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118233819368950846882772897 88675364526713135162079673)
    ·
      refine ⟨66506523395034851371559755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88675364526713135162079673 66506523395034851371559755)
      ·
        refine ⟨99759785092552277057339633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66506523395034851371559755 99759785092552277057339633)
        ·
          refine ⟨74819838819414207793004725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99759785092552277057339633 74819838819414207793004725)
          ·
            refine ⟨7014359889320081980594193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74819838819414207793004725 7014359889320081980594193)
            ·
              refine ⟨5260769916990061485445645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7014359889320081980594193 5260769916990061485445645)
              ·
                refine ⟨1972788718871273057042117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5260769916990061485445645 1972788718871273057042117)
                ·
                  refine ⟨369897884788363698195397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1972788718871273057042117 369897884788363698195397)
                  ·
                    rfl

theorem cell22_3241681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 4].length) (baseStart_3241681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241681 prefixEnd_3241681 := by exact prefixLift 3241681
  have htrace : WordTrace (prefixWord ++ tailWord_3241681) baseStart_3241681 baseEnd_3241681 := by
    simpa [prefixWord, tailWord_3241681, baseEnd_3241681] using wordTrace_append hprefix tailTrace_3241681
  have hstable : (prefixWord ++ tailWord_3241681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241681).length < 2 ^ (prefixWord ++ tailWord_3241681).sum := by decide
  have hdescent : baseEnd_3241681 < baseStart_3241681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241696 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 2, 3]
def baseStart_3241696 : Nat := 118140960795 + 3241696 * 2 ^ 59
def prefixEnd_3241696 : Nat := 4983230072969 + 3 ^ 40 * 3241696 * 2
def baseEnd_3241696 : Nat := 1109698789171636055461145

theorem tailTrace_3241696 : CollatzResearch.WordTrace tailWord_3241696 prefixEnd_3241696 1109698789171636055461145 := by
  unfold tailWord_3241696
  simp only [CollatzResearch.WordTrace]
  refine ⟨59117183231948252222284471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78822910975931002963045961 59117183231948252222284471)
  ·
    refine ⟨88675774847922378333426707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59117183231948252222284471 88675774847922378333426707)
    ·
      refine ⟨133013662271883567500140061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88675774847922378333426707 133013662271883567500140061)
      ·
        refine ⟨49880123351956337812552523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133013662271883567500140061 49880123351956337812552523)
        ·
          refine ⟨74820185027934506718828785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49880123351956337812552523 74820185027934506718828785)
          ·
            refine ⟨56115138770950880039121589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74820185027934506718828785 56115138770950880039121589)
            ·
              refine ⟨5260794259776645003667649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56115138770950880039121589 5260794259776645003667649)
              ·
                refine ⟨3945595694832483752750737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5260794259776645003667649 3945595694832483752750737)
                ·
                  refine ⟨2959196771124362814563053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3945595694832483752750737 2959196771124362814563053)
                  ·
                    refine ⟨1109698789171636055461145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2959196771124362814563053 1109698789171636055461145)
                    ·
                      rfl

theorem cell22_3241696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 2, 3].length) (baseStart_3241696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241696 prefixEnd_3241696 := by exact prefixLift 3241696
  have htrace : WordTrace (prefixWord ++ tailWord_3241696) baseStart_3241696 baseEnd_3241696 := by
    simpa [prefixWord, tailWord_3241696, baseEnd_3241696] using wordTrace_append hprefix tailTrace_3241696
  have hstable : (prefixWord ++ tailWord_3241696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241696).length < 2 ^ (prefixWord ++ tailWord_3241696).sum := by decide
  have hdescent : baseEnd_3241696 < baseStart_3241696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241713 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 2, 3]
def baseStart_3241713 : Nat := 118140960795 + 3241713 * 2 ^ 59
def prefixEnd_3241713 : Nat := 4983230072969 + 3 ^ 40 * 3241713 * 2
def baseEnd_3241713 : Nat := 1109704608619053677786093

theorem tailTrace_3241713 : CollatzResearch.WordTrace tailWord_3241713 prefixEnd_3241713 1109704608619053677786093 := by
  unfold tailWord_3241713
  simp only [CollatzResearch.WordTrace]
  refine ⟨118234986504834916347937793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78823324336556610898625195 118234986504834916347937793)
  ·
    refine ⟨88676239878626187260953345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118234986504834916347937793 88676239878626187260953345)
    ·
      refine ⟨66507179908969640445715009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88676239878626187260953345 66507179908969640445715009)
      ·
        refine ⟨49880384931727230334286257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66507179908969640445715009 49880384931727230334286257)
        ·
          refine ⟨37410288698795422750714693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49880384931727230334286257 37410288698795422750714693)
          ·
            refine ⟨7014429131024141765759005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37410288698795422750714693 7014429131024141765759005)
            ·
              refine ⟨2630410924134053162159627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7014429131024141765759005 2630410924134053162159627)
              ·
                refine ⟨3945616386201079743239441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2630410924134053162159627 3945616386201079743239441)
                ·
                  refine ⟨2959212289650809807429581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3945616386201079743239441 2959212289650809807429581)
                  ·
                    refine ⟨1109704608619053677786093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2959212289650809807429581 1109704608619053677786093)
                    ·
                      rfl

theorem cell22_3241713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_3241713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241713 prefixEnd_3241713 := by exact prefixLift 3241713
  have htrace : WordTrace (prefixWord ++ tailWord_3241713) baseStart_3241713 baseEnd_3241713 := by
    simpa [prefixWord, tailWord_3241713, baseEnd_3241713] using wordTrace_append hprefix tailTrace_3241713
  have hstable : (prefixWord ++ tailWord_3241713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241713).length < 2 ^ (prefixWord ++ tailWord_3241713).sum := by decide
  have hdescent : baseEnd_3241713 < baseStart_3241713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241726 : List Nat := [4, 2, 2, 1, 3, 1, 1, 8]
def baseStart_3241726 : Nat := 118140960795 + 3241726 * 2 ^ 59
def prefixEnd_3241726 : Nat := 4983230072969 + 3 ^ 40 * 3241726 * 2
def baseEnd_3241726 : Nat := 123301006531636219690117

theorem tailTrace_3241726 : CollatzResearch.WordTrace tailWord_3241726 prefixEnd_3241726 123301006531636219690117 := by
  unfold tailWord_3241726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779432581723477446020129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78823640435858546378774021 14779432581723477446020129)
  ·
    refine ⟨11084574436292608084515097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14779432581723477446020129 11084574436292608084515097)
    ·
      refine ⟨8313430827219456063386323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11084574436292608084515097 8313430827219456063386323)
      ·
        refine ⟨12470146240829184095079485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313430827219456063386323 12470146240829184095079485)
        ·
          refine ⟨4676304840310944035654807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12470146240829184095079485 4676304840310944035654807)
          ·
            refine ⟨7014457260466416053482211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676304840310944035654807 7014457260466416053482211)
            ·
              refine ⟨10521685890699624080223317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7014457260466416053482211 10521685890699624080223317)
              ·
                refine ⟨123301006531636219690117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10521685890699624080223317 123301006531636219690117)
                ·
                  rfl

theorem cell22_3241726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_3241726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241726 prefixEnd_3241726 := by exact prefixLift 3241726
  have htrace : WordTrace (prefixWord ++ tailWord_3241726) baseStart_3241726 baseEnd_3241726 := by
    simpa [prefixWord, tailWord_3241726, baseEnd_3241726] using wordTrace_append hprefix tailTrace_3241726
  have hstable : (prefixWord ++ tailWord_3241726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241726).length < 2 ^ (prefixWord ++ tailWord_3241726).sum := by decide
  have hdescent : baseEnd_3241726 < baseStart_3241726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241754 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_3241754 : Nat := 118140960795 + 3241754 * 2 ^ 59
def prefixEnd_3241754 : Nat := 4983230072969 + 3 ^ 40 * 3241754 * 2
def baseEnd_3241754 : Nat := 369906214585647745836989

theorem tailTrace_3241754 : CollatzResearch.WordTrace tailWord_3241754 prefixEnd_3241754 369906214585647745836989 := by
  unfold tailWord_3241754
  simp only [CollatzResearch.WordTrace]
  refine ⟨29559120474421595087545079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78824321265124253566786877 29559120474421595087545079)
  ·
    refine ⟨44338680711632392631317619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29559120474421595087545079 44338680711632392631317619)
    ·
      refine ⟨66508021067448588946976429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44338680711632392631317619 66508021067448588946976429)
      ·
        refine ⟨24940507900293220855116161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66508021067448588946976429 24940507900293220855116161)
        ·
          refine ⟨18705380925219915641337121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24940507900293220855116161 18705380925219915641337121)
          ·
            refine ⟨14029035693914936731002841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18705380925219915641337121 14029035693914936731002841)
            ·
              refine ⟨10521776770436202548252131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14029035693914936731002841 10521776770436202548252131)
              ·
                refine ⟨15782665155654303822378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10521776770436202548252131 15782665155654303822378197)
                ·
                  refine ⟨369906214585647745836989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15782665155654303822378197 369906214585647745836989)
                  ·
                    rfl

theorem cell22_3241754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_3241754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241754 prefixEnd_3241754 := by exact prefixLift 3241754
  have htrace : WordTrace (prefixWord ++ tailWord_3241754) baseStart_3241754 baseEnd_3241754 := by
    simpa [prefixWord, tailWord_3241754, baseEnd_3241754] using wordTrace_append hprefix tailTrace_3241754
  have hstable : (prefixWord ++ tailWord_3241754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241754).length < 2 ^ (prefixWord ++ tailWord_3241754).sum := by decide
  have hdescent : baseEnd_3241754 < baseStart_3241754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241829 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_3241829 : Nat := 118140960795 + 3241829 * 2 ^ 59
def prefixEnd_3241829 : Nat := 4983230072969 + 3 ^ 40 * 3241829 * 2
def baseEnd_3241829 : Nat := 1109744317789668041885737

theorem tailTrace_3241829 : CollatzResearch.WordTrace tailWord_3241829 prefixEnd_3241829 1109744317789668041885737 := by
  unfold tailWord_3241829
  simp only [CollatzResearch.WordTrace]
  refine ⟨118239217372414668159160541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78826144914943112106107027 118239217372414668159160541)
  ·
    refine ⟨44339706514655500559685203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118239217372414668159160541 44339706514655500559685203)
    ·
      refine ⟨66509559771983250839527805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44339706514655500559685203 66509559771983250839527805)
      ·
        refine ⟨24941084914493719064822927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66509559771983250839527805 24941084914493719064822927)
        ·
          refine ⟨37411627371740578597234391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24941084914493719064822927 37411627371740578597234391)
          ·
            refine ⟨56117441057610867895851587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37411627371740578597234391 56117441057610867895851587)
            ·
              refine ⟨84176161586416301843777381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56117441057610867895851587 84176161586416301843777381)
              ·
                refine ⟨15783030297453056595708259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84176161586416301843777381 15783030297453056595708259)
                ·
                  refine ⟨23674545446179584893562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15783030297453056595708259 23674545446179584893562389)
                  ·
                    refine ⟨1109744317789668041885737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23674545446179584893562389 1109744317789668041885737)
                    ·
                      rfl

theorem cell22_3241829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_3241829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241829 prefixEnd_3241829 := by exact prefixLift 3241829
  have htrace : WordTrace (prefixWord ++ tailWord_3241829) baseStart_3241829 baseEnd_3241829 := by
    simpa [prefixWord, tailWord_3241829, baseEnd_3241829] using wordTrace_append hprefix tailTrace_3241829
  have hstable : (prefixWord ++ tailWord_3241829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241829).length < 2 ^ (prefixWord ++ tailWord_3241829).sum := by decide
  have hdescent : baseEnd_3241829 < baseStart_3241829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241831 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 1, 5]
def baseStart_3241831 : Nat := 118140960795 + 3241831 * 2 ^ 59
def prefixEnd_3241831 : Nat := 4983230072969 + 3 ^ 40 * 3241831 * 2
def baseEnd_3241831 : Nat := 1109745002430540703335731

theorem tailTrace_3241831 : CollatzResearch.WordTrace tailWord_3241831 prefixEnd_3241831 1109745002430540703335731 := by
  unfold tailWord_3241831
  simp only [CollatzResearch.WordTrace]
  refine ⟨118239290318407422500733347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78826193545604948333822231 118239290318407422500733347)
  ·
    refine ⟨177358935477611133751100021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118239290318407422500733347 177358935477611133751100021)
    ·
      refine ⟨16627400201026043789165627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177358935477611133751100021 16627400201026043789165627)
      ·
        refine ⟨24941100301539065683748441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16627400201026043789165627 24941100301539065683748441)
        ·
          refine ⟨18705825226154299262811331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24941100301539065683748441 18705825226154299262811331)
          ·
            refine ⟨28058737839231448894216997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18705825226154299262811331 28058737839231448894216997)
            ·
              refine ⟨5261013344855896667665687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28058737839231448894216997 5261013344855896667665687)
              ·
                refine ⟨7891520017283845001498531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261013344855896667665687 7891520017283845001498531)
                ·
                  refine ⟨11837280025925767502247797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7891520017283845001498531 11837280025925767502247797)
                  ·
                    refine ⟨1109745002430540703335731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11837280025925767502247797 1109745002430540703335731)
                    ·
                      rfl

theorem cell22_3241831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_3241831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241831 prefixEnd_3241831 := by exact prefixLift 3241831
  have htrace : WordTrace (prefixWord ++ tailWord_3241831) baseStart_3241831 baseEnd_3241831 := by
    simpa [prefixWord, tailWord_3241831, baseEnd_3241831] using wordTrace_append hprefix tailTrace_3241831
  have hstable : (prefixWord ++ tailWord_3241831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241831).length < 2 ^ (prefixWord ++ tailWord_3241831).sum := by decide
  have hdescent : baseEnd_3241831 < baseStart_3241831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3241953 : List Nat := [1, 2, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3241953 : Nat := 118140960795 + 3241953 * 2 ^ 59
def prefixEnd_3241953 : Nat := 4983230072969 + 3 ^ 40 * 3241953 * 2
def baseEnd_3241953 : Nat := 1109786765523773051785357

theorem tailTrace_3241953 : CollatzResearch.WordTrace tailWord_3241953 prefixEnd_3241953 1109786765523773051785357 := by
  unfold tailWord_3241953
  simp only [CollatzResearch.WordTrace]
  refine ⟨118243740023965437336674513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78829160015976958224449675 118243740023965437336674513)
  ·
    refine ⟨88682805017974078002505885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118243740023965437336674513 88682805017974078002505885)
    ·
      refine ⟨33256051881740279250939707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88682805017974078002505885 33256051881740279250939707)
      ·
        refine ⟨49884077822610418876409561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33256051881740279250939707 49884077822610418876409561)
        ·
          refine ⟨37413058366957814157307171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49884077822610418876409561 37413058366957814157307171)
          ·
            refine ⟨56119587550436721235960757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37413058366957814157307171 56119587550436721235960757)
            ·
              refine ⟨5261211332853442615871321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56119587550436721235960757 5261211332853442615871321)
              ·
                refine ⟨3945908499640081961903491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261211332853442615871321 3945908499640081961903491)
                ·
                  refine ⟨5918862749460122942855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3945908499640081961903491 5918862749460122942855237)
                  ·
                    refine ⟨1109786765523773051785357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5918862749460122942855237 1109786765523773051785357)
                    ·
                      rfl

theorem cell22_3241953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3241953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3241953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3241953 prefixEnd_3241953 := by exact prefixLift 3241953
  have htrace : WordTrace (prefixWord ++ tailWord_3241953) baseStart_3241953 baseEnd_3241953 := by
    simpa [prefixWord, tailWord_3241953, baseEnd_3241953] using wordTrace_append hprefix tailTrace_3241953
  have hstable : (prefixWord ++ tailWord_3241953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3241953).length < 2 ^ (prefixWord ++ tailWord_3241953).sum := by decide
  have hdescent : baseEnd_3241953 < baseStart_3241953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3241953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242045 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_3242045 : Nat := 118140960795 + 3242045 * 2 ^ 59
def prefixEnd_3242045 : Nat := 4983230072969 + 3 ^ 40 * 3242045 * 2
def baseEnd_3242045 : Nat := 1109818259003915478485075

theorem tailTrace_3242045 : CollatzResearch.WordTrace tailWord_3242045 prefixEnd_3242045 1109818259003915478485075 := by
  unfold tailWord_3242045
  simp only [CollatzResearch.WordTrace]
  refine ⟨118247095539632137049023589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78831397026421424699349059 118247095539632137049023589)
  ·
    refine ⟨22171330413681025696691923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118247095539632137049023589 22171330413681025696691923)
    ·
      refine ⟨33256995620521538545037885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22171330413681025696691923 33256995620521538545037885)
      ·
        refine ⟨12471373357695576954389207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33256995620521538545037885 12471373357695576954389207)
        ·
          refine ⟨18707060036543365431583811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471373357695576954389207 18707060036543365431583811)
          ·
            refine ⟨28060590054815048147375717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707060036543365431583811 28060590054815048147375717)
            ·
              refine ⟨5261360635277821527632947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28060590054815048147375717 5261360635277821527632947)
              ·
                refine ⟨7892040952916732291449421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261360635277821527632947 7892040952916732291449421)
                ·
                  refine ⟨2959515357343774609293533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7892040952916732291449421 2959515357343774609293533)
                  ·
                    refine ⟨1109818259003915478485075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2959515357343774609293533 1109818259003915478485075)
                    ·
                      rfl

theorem cell22_3242045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_3242045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242045 prefixEnd_3242045 := by exact prefixLift 3242045
  have htrace : WordTrace (prefixWord ++ tailWord_3242045) baseStart_3242045 baseEnd_3242045 := by
    simpa [prefixWord, tailWord_3242045, baseEnd_3242045] using wordTrace_append hprefix tailTrace_3242045
  have hstable : (prefixWord ++ tailWord_3242045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242045).length < 2 ^ (prefixWord ++ tailWord_3242045).sum := by decide
  have hdescent : baseEnd_3242045 < baseStart_3242045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242056 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_3242056 : Nat := 118140960795 + 3242056 * 2 ^ 59
def prefixEnd_3242056 : Nat := 4983230072969 + 3 ^ 40 * 3242056 * 2
def baseEnd_3242056 : Nat := 1109822024528715116460041

theorem tailTrace_3242056 : CollatzResearch.WordTrace tailWord_3242056 prefixEnd_3242056 1109822024528715116460041 := by
  unfold tailWord_3242056
  simp only [CollatzResearch.WordTrace]
  refine ⟨59123748371296142963837011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78831664495061523951782681 59123748371296142963837011)
  ·
    refine ⟨88685622556944214445755517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59123748371296142963837011 88685622556944214445755517)
    ·
      refine ⟨33257108458854080417158319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88685622556944214445755517 33257108458854080417158319)
      ·
        refine ⟨49885662688281120625737479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33257108458854080417158319 49885662688281120625737479)
        ·
          refine ⟨74828494032421680938606219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49885662688281120625737479 74828494032421680938606219)
          ·
            refine ⟨112242741048632521407909329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74828494032421680938606219 112242741048632521407909329)
            ·
              refine ⟨84182055786474391055931997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112242741048632521407909329 84182055786474391055931997)
              ·
                refine ⟨31568270919927896645974499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84182055786474391055931997 31568270919927896645974499)
                ·
                  refine ⟨47352406379891844968961749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31568270919927896645974499 47352406379891844968961749)
                  ·
                    refine ⟨1109822024528715116460041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47352406379891844968961749 1109822024528715116460041)
                    ·
                      rfl

theorem cell22_3242056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_3242056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242056 prefixEnd_3242056 := by exact prefixLift 3242056
  have htrace : WordTrace (prefixWord ++ tailWord_3242056) baseStart_3242056 baseEnd_3242056 := by
    simpa [prefixWord, tailWord_3242056, baseEnd_3242056] using wordTrace_append hprefix tailTrace_3242056
  have hstable : (prefixWord ++ tailWord_3242056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242056).length < 2 ^ (prefixWord ++ tailWord_3242056).sum := by decide
  have hdescent : baseEnd_3242056 < baseStart_3242056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242103 : List Nat := [1, 1, 3, 1, 1, 5, 3, 1, 6]
def baseStart_3242103 : Nat := 118140960795 + 3242103 * 2 ^ 59
def prefixEnd_3242103 : Nat := 4983230072969 + 3 ^ 40 * 3242103 * 2
def baseEnd_3242103 : Nat := 369946037863074220178299

theorem tailTrace_3242103 : CollatzResearch.WordTrace tailWord_3242103 prefixEnd_3242103 369946037863074220178299 := by
  unfold tailWord_3242103
  simp only [CollatzResearch.WordTrace]
  refine ⟨118249210973422012954634963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78832807315614675303089975 118249210973422012954634963)
  ·
    refine ⟨177373816460133019431952445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118249210973422012954634963 177373816460133019431952445)
    ·
      refine ⟨66515181172549882286982167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177373816460133019431952445 66515181172549882286982167)
      ·
        refine ⟨99772771758824823430473251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66515181172549882286982167 99772771758824823430473251)
        ·
          refine ⟨149659157638237235145709877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99772771758824823430473251 149659157638237235145709877)
          ·
            refine ⟨14030546028584740794910301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149659157638237235145709877 14030546028584740794910301)
            ·
              refine ⟨5261454760719277798091363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14030546028584740794910301 5261454760719277798091363)
              ·
                refine ⟨7892182141078916697137045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261454760719277798091363 7892182141078916697137045)
                ·
                  refine ⟨369946037863074220178299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7892182141078916697137045 369946037863074220178299)
                  ·
                    rfl

theorem cell22_3242103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 6].length) (baseStart_3242103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242103 prefixEnd_3242103 := by exact prefixLift 3242103
  have htrace : WordTrace (prefixWord ++ tailWord_3242103) baseStart_3242103 baseEnd_3242103 := by
    simpa [prefixWord, tailWord_3242103, baseEnd_3242103] using wordTrace_append hprefix tailTrace_3242103
  have hstable : (prefixWord ++ tailWord_3242103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242103).length < 2 ^ (prefixWord ++ tailWord_3242103).sum := by decide
  have hdescent : baseEnd_3242103 < baseStart_3242103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242122 : List Nat := [3, 1, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_3242122 : Nat := 118140960795 + 3242122 * 2 ^ 59
def prefixEnd_3242122 : Nat := 4983230072969 + 3 ^ 40 * 3242122 * 2
def baseEnd_3242122 : Nat := 1109844617677512944309839

theorem tailTrace_3242122 : CollatzResearch.WordTrace tailWord_3242122 prefixEnd_3242122 1109844617677512944309839 := by
  unfold tailWord_3242122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29562475990088294799894155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78833269306902119466384413 29562475990088294799894155)
  ·
    refine ⟨44343713985132442199841233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29562475990088294799894155 44343713985132442199841233)
    ·
      refine ⟨33257785488849331649880925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44343713985132442199841233 33257785488849331649880925)
      ·
        refine ⟨12471669558318499368705347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33257785488849331649880925 12471669558318499368705347)
        ·
          refine ⟨18707504337477749053058021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471669558318499368705347 18707504337477749053058021)
          ·
            refine ⟨3507657063277077947448379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18707504337477749053058021 3507657063277077947448379)
            ·
              refine ⟨5261485594915616921172569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507657063277077947448379 5261485594915616921172569)
              ·
                refine ⟨3946114196186712690879427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5261485594915616921172569 3946114196186712690879427)
                ·
                  refine ⟨5919171294280069036319141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946114196186712690879427 5919171294280069036319141)
                  ·
                    refine ⟨1109844617677512944309839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919171294280069036319141 1109844617677512944309839)
                    ·
                      rfl

theorem cell22_3242122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_3242122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242122 prefixEnd_3242122 := by exact prefixLift 3242122
  have htrace : WordTrace (prefixWord ++ tailWord_3242122) baseStart_3242122 baseEnd_3242122 := by
    simpa [prefixWord, tailWord_3242122, baseEnd_3242122] using wordTrace_append hprefix tailTrace_3242122
  have hstable : (prefixWord ++ tailWord_3242122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242122).length < 2 ^ (prefixWord ++ tailWord_3242122).sum := by decide
  have hdescent : baseEnd_3242122 < baseStart_3242122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242135 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 1, 5]
def baseStart_3242135 : Nat := 118140960795 + 3242135 * 2 ^ 59
def prefixEnd_3242135 : Nat := 4983230072969 + 3 ^ 40 * 3242135 * 2
def baseEnd_3242135 : Nat := 1109849067843185243734799

theorem tailTrace_3242135 : CollatzResearch.WordTrace tailWord_3242135 prefixEnd_3242135 1109849067843185243734799 := by
  unfold tailWord_3242135
  simp only [CollatzResearch.WordTrace]
  refine ⟨118250378109306082419799859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78833585406204054946533239 118250378109306082419799859)
  ·
    refine ⟨177375567163959123629699789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118250378109306082419799859 177375567163959123629699789)
    ·
      refine ⟨66515837686484671361137421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177375567163959123629699789 66515837686484671361137421)
      ·
        refine ⟨24943439132431751760426533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66515837686484671361137421 24943439132431751760426533)
        ·
          refine ⟨4676894837330953455079975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24943439132431751760426533 4676894837330953455079975)
          ·
            refine ⟨7015342255996430182619963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676894837330953455079975 7015342255996430182619963)
            ·
              refine ⟨10523013383994645273929945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015342255996430182619963 10523013383994645273929945)
              ·
                refine ⟨7892260037995983955447459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10523013383994645273929945 7892260037995983955447459)
                ·
                  refine ⟨11838390056993975933171189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7892260037995983955447459 11838390056993975933171189)
                  ·
                    refine ⟨1109849067843185243734799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11838390056993975933171189 1109849067843185243734799)
                    ·
                      rfl

theorem cell22_3242135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_3242135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242135 prefixEnd_3242135 := by exact prefixLift 3242135
  have htrace : WordTrace (prefixWord ++ tailWord_3242135) baseStart_3242135 baseEnd_3242135 := by
    simpa [prefixWord, tailWord_3242135, baseEnd_3242135] using wordTrace_append hprefix tailTrace_3242135
  have hstable : (prefixWord ++ tailWord_3242135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242135).length < 2 ^ (prefixWord ++ tailWord_3242135).sum := by decide
  have hdescent : baseEnd_3242135 < baseStart_3242135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242148 : List Nat := [2, 3, 1, 2, 4, 10]
def baseStart_3242148 : Nat := 118140960795 + 3242148 * 2 ^ 59
def prefixEnd_3242148 : Nat := 4983230072969 + 3 ^ 40 * 3242148 * 2
def baseEnd_3242148 : Nat := 13701895284059969668639

theorem tailTrace_3242148 : CollatzResearch.WordTrace tailWord_3242148 prefixEnd_3242148 13701895284059969668639 := by
  unfold tailWord_3242148
  simp only [CollatzResearch.WordTrace]
  refine ⟨59125426129129492820011549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78833901505505990426682065 59125426129129492820011549)
  ·
    refine ⟨22172034798423559807504331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59125426129129492820011549 22172034798423559807504331)
    ·
      refine ⟨33258052197635339711256497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22172034798423559807504331 33258052197635339711256497)
      ·
        refine ⟨24943539148226504783442373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33258052197635339711256497 24943539148226504783442373)
        ·
          refine ⟨4676913590292469646895445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24943539148226504783442373 4676913590292469646895445)
          ·
            refine ⟨13701895284059969668639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4676913590292469646895445 13701895284059969668639)
            ·
              rfl

theorem cell22_3242148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 10].length) (baseStart_3242148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242148 prefixEnd_3242148 := by exact prefixLift 3242148
  have htrace : WordTrace (prefixWord ++ tailWord_3242148) baseStart_3242148 baseEnd_3242148 := by
    simpa [prefixWord, tailWord_3242148, baseEnd_3242148] using wordTrace_append hprefix tailTrace_3242148
  have hstable : (prefixWord ++ tailWord_3242148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242148).length < 2 ^ (prefixWord ++ tailWord_3242148).sum := by decide
  have hdescent : baseEnd_3242148 < baseStart_3242148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242154 : List Nat := [3, 1, 5, 1, 2, 1, 1, 4, 4]
def baseStart_3242154 : Nat := 118140960795 + 3242154 * 2 ^ 59
def prefixEnd_3242154 : Nat := 4983230072969 + 3 ^ 40 * 3242154 * 2
def baseEnd_3242154 : Nat := 369951857310491842503247

theorem tailTrace_3242154 : CollatzResearch.WordTrace tailWord_3242154 prefixEnd_3242154 369951857310491842503247 := by
  unfold tailWord_3242154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29562767774059312166185379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78834047397491499109827677 29562767774059312166185379)
  ·
    refine ⟨44344151661088968249278069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29562767774059312166185379 44344151661088968249278069)
    ·
      refine ⟨4157264218227090773369819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44344151661088968249278069 4157264218227090773369819)
      ·
        refine ⟨6235896327340636160054729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4157264218227090773369819 6235896327340636160054729)
        ·
          refine ⟨4676922245505477120041047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6235896327340636160054729 4676922245505477120041047)
          ·
            refine ⟨7015383368258215680061571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4676922245505477120041047 7015383368258215680061571)
            ·
              refine ⟨10523075052387323520092357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7015383368258215680061571 10523075052387323520092357)
              ·
                refine ⟨1973076572322623160017317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10523075052387323520092357 1973076572322623160017317)
                ·
                  refine ⟨369951857310491842503247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973076572322623160017317 369951857310491842503247)
                  ·
                    rfl

theorem cell22_3242154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_3242154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242154 prefixEnd_3242154 := by exact prefixLift 3242154
  have htrace : WordTrace (prefixWord ++ tailWord_3242154) baseStart_3242154 baseEnd_3242154 := by
    simpa [prefixWord, tailWord_3242154, baseEnd_3242154] using wordTrace_append hprefix tailTrace_3242154
  have hstable : (prefixWord ++ tailWord_3242154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242154).length < 2 ^ (prefixWord ++ tailWord_3242154).sum := by decide
  have hdescent : baseEnd_3242154 < baseStart_3242154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242208 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_3242208 : Nat := 118140960795 + 3242208 * 2 ^ 59
def prefixEnd_3242208 : Nat := 4983230072969 + 3 ^ 40 * 3242208 * 2
def baseEnd_3242208 : Nat := 1109874057235037386659575

theorem tailTrace_3242208 : CollatzResearch.WordTrace tailWord_3242208 prefixEnd_3242208 1109874057235037386659575 := by
  unfold tailWord_3242208
  simp only [CollatzResearch.WordTrace]
  refine ⟨59126520319020807943603639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78835360425361077258138185 59126520319020807943603639)
  ·
    refine ⟨88689780478531211915405459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59126520319020807943603639 88689780478531211915405459)
    ·
      refine ⟨133034670717796817873108189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88689780478531211915405459 133034670717796817873108189)
      ·
        refine ⟨49888001519173806702415571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133034670717796817873108189 49888001519173806702415571)
        ·
          refine ⟨74832002278760710053623357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49888001519173806702415571 74832002278760710053623357)
          ·
            refine ⟨28062000854535266270108759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74832002278760710053623357 28062000854535266270108759)
            ·
              refine ⟨42093001281802899405163139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28062000854535266270108759 42093001281802899405163139)
              ·
                refine ⟨63139501922704349107744709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42093001281802899405163139 63139501922704349107744709)
                ·
                  refine ⟨11838656610507065457702133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63139501922704349107744709 11838656610507065457702133)
                  ·
                    refine ⟨1109874057235037386659575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11838656610507065457702133 1109874057235037386659575)
                    ·
                      rfl

theorem cell22_3242208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_3242208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242208 prefixEnd_3242208 := by exact prefixLift 3242208
  have htrace : WordTrace (prefixWord ++ tailWord_3242208) baseStart_3242208 baseEnd_3242208 := by
    simpa [prefixWord, tailWord_3242208, baseEnd_3242208] using wordTrace_append hprefix tailTrace_3242208
  have hstable : (prefixWord ++ tailWord_3242208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242208).length < 2 ^ (prefixWord ++ tailWord_3242208).sum := by decide
  have hdescent : baseEnd_3242208 < baseStart_3242208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242240 : List Nat := [2, 1, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_3242240 : Nat := 118140960795 + 3242240 * 2 ^ 59
def prefixEnd_3242240 : Nat := 4983230072969 + 3 ^ 40 * 3242240 * 2
def baseEnd_3242240 : Nat := 1109885011488999969859477

theorem tailTrace_3242240 : CollatzResearch.WordTrace tailWord_3242240 prefixEnd_3242240 1109885011488999969859477 := by
  unfold tailWord_3242240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127103886962842676186087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78836138515950456901581449 59127103886962842676186087)
  ·
    refine ⟨88690655830444264014279131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59127103886962842676186087 88690655830444264014279131)
    ·
      refine ⟨133035983745666396021418697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88690655830444264014279131 133035983745666396021418697)
      ·
        refine ⟨99776987809249797016064023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133035983745666396021418697 99776987809249797016064023)
        ·
          refine ⟨149665481713874695524096035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99776987809249797016064023 149665481713874695524096035)
          ·
            refine ⟨224498222570812043286144053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149665481713874695524096035 224498222570812043286144053)
            ·
              refine ⟨21046708366013629058076005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224498222570812043286144053 21046708366013629058076005)
              ·
                refine ⟨3946257818627555448389251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21046708366013629058076005 3946257818627555448389251)
                ·
                  refine ⟨5919386727941333172583877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3946257818627555448389251 5919386727941333172583877)
                  ·
                    refine ⟨1109885011488999969859477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919386727941333172583877 1109885011488999969859477)
                    ·
                      rfl

theorem cell22_3242240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_3242240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242240 prefixEnd_3242240 := by exact prefixLift 3242240
  have htrace : WordTrace (prefixWord ++ tailWord_3242240) baseStart_3242240 baseEnd_3242240 := by
    simpa [prefixWord, tailWord_3242240, baseEnd_3242240] using wordTrace_append hprefix tailTrace_3242240
  have hstable : (prefixWord ++ tailWord_3242240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242240).length < 2 ^ (prefixWord ++ tailWord_3242240).sum := by decide
  have hdescent : baseEnd_3242240 < baseStart_3242240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242272 : List Nat := [2, 1, 1, 5, 2, 3, 1, 1, 6]
def baseStart_3242272 : Nat := 118140960795 + 3242272 * 2 ^ 59
def prefixEnd_3242272 : Nat := 4983230072969 + 3 ^ 40 * 3242272 * 2
def baseEnd_3242272 : Nat := 369965321914320851019793

theorem tailTrace_3242272 : CollatzResearch.WordTrace tailWord_3242272 prefixEnd_3242272 369965321914320851019793 := by
  unfold tailWord_3242272
  simp only [CollatzResearch.WordTrace]
  refine ⟨59127687454904877408768535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78836916606539836545024713 59127687454904877408768535)
  ·
    refine ⟨88691531182357316113152803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59127687454904877408768535 88691531182357316113152803)
    ·
      refine ⟨133037296773535974169729205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88691531182357316113152803 133037296773535974169729205)
      ·
        refine ⟨12472246572518997578412113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133037296773535974169729205 12472246572518997578412113)
        ·
          refine ⟨9354184929389248183809085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12472246572518997578412113 9354184929389248183809085)
          ·
            refine ⟨3507819348520968068928407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9354184929389248183809085 3507819348520968068928407)
            ·
              refine ⟨5261729022781452103392611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3507819348520968068928407 5261729022781452103392611)
              ·
                refine ⟨7892593534172178155088917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5261729022781452103392611 7892593534172178155088917)
                ·
                  refine ⟨369965321914320851019793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7892593534172178155088917 369965321914320851019793)
                  ·
                    rfl

theorem cell22_3242272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 6].length) (baseStart_3242272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242272 prefixEnd_3242272 := by exact prefixLift 3242272
  have htrace : WordTrace (prefixWord ++ tailWord_3242272) baseStart_3242272 baseEnd_3242272 := by
    simpa [prefixWord, tailWord_3242272, baseEnd_3242272] using wordTrace_append hprefix tailTrace_3242272
  have hstable : (prefixWord ++ tailWord_3242272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242272).length < 2 ^ (prefixWord ++ tailWord_3242272).sum := by decide
  have hdescent : baseEnd_3242272 < baseStart_3242272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242302 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_3242302 : Nat := 118140960795 + 3242302 * 2 ^ 59
def prefixEnd_3242302 : Nat := 4983230072969 + 3 ^ 40 * 3242302 * 2
def baseEnd_3242302 : Nat := 1109906235356052474809287

theorem tailTrace_3242302 : CollatzResearch.WordTrace tailWord_3242302 prefixEnd_3242302 1109906235356052474809287 := by
  unfold tailWord_3242302
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782058637462633742641145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78837646066467379960752773 14782058637462633742641145)
  ·
    refine ⟨11086543978096975306980859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14782058637462633742641145 11086543978096975306980859)
    ·
      refine ⟨16629815967145462960471289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086543978096975306980859 16629815967145462960471289)
      ·
        refine ⟨12472361975359097220353467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16629815967145462960471289 12472361975359097220353467)
        ·
          refine ⟨18708542963038645830530201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12472361975359097220353467 18708542963038645830530201)
          ·
            refine ⟨14031407222278984372897651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18708542963038645830530201 14031407222278984372897651)
            ·
              refine ⟨21047110833418476559346477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14031407222278984372897651 21047110833418476559346477)
              ·
                refine ⟨7892666562531928709754929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21047110833418476559346477 7892666562531928709754929)
                ·
                  refine ⟨5919499921898946532316197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7892666562531928709754929 5919499921898946532316197)
                  ·
                    refine ⟨1109906235356052474809287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919499921898946532316197 1109906235356052474809287)
                    ·
                      rfl

theorem cell22_3242302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_3242302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242302 prefixEnd_3242302 := by exact prefixLift 3242302
  have htrace : WordTrace (prefixWord ++ tailWord_3242302) baseStart_3242302 baseEnd_3242302 := by
    simpa [prefixWord, tailWord_3242302, baseEnd_3242302] using wordTrace_append hprefix tailTrace_3242302
  have hstable : (prefixWord ++ tailWord_3242302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242302).length < 2 ^ (prefixWord ++ tailWord_3242302).sum := by decide
  have hdescent : baseEnd_3242302 < baseStart_3242302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242315 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 7, 3]
def baseStart_3242315 : Nat := 118140960795 + 3242315 * 2 ^ 59
def prefixEnd_3242315 : Nat := 4983230072969 + 3 ^ 40 * 3242315 * 2
def baseEnd_3242315 : Nat := 1109910685521724774234247

theorem tailTrace_3242315 : CollatzResearch.WordTrace tailWord_3242315 prefixEnd_3242315 1109910685521724774234247 := by
  unfold tailWord_3242315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118256943248653973161352399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78837962165769315440901599 118256943248653973161352399)
  ·
    refine ⟨177385414872980959742028599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118256943248653973161352399 177385414872980959742028599)
    ·
      refine ⟨266078122309471439613042899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177385414872980959742028599 266078122309471439613042899)
      ·
        refine ⟨399117183464207159419564349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266078122309471439613042899 399117183464207159419564349)
        ·
          refine ⟨149668943799077684782336631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399117183464207159419564349 149668943799077684782336631)
          ·
            refine ⟨224503415698616527173504947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149668943799077684782336631 224503415698616527173504947)
            ·
              refine ⟨336755123547924790760257421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224503415698616527173504947 336755123547924790760257421)
              ·
                refine ⟨126283171330471796535096533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336755123547924790760257421 126283171330471796535096533)
                ·
                  refine ⟨2959761828057932731291325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 126283171330471796535096533 2959761828057932731291325)
                  ·
                    refine ⟨1109910685521724774234247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2959761828057932731291325 1109910685521724774234247)
                    ·
                      rfl

theorem cell22_3242315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 7, 3].length) (baseStart_3242315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242315 prefixEnd_3242315 := by exact prefixLift 3242315
  have htrace : WordTrace (prefixWord ++ tailWord_3242315) baseStart_3242315 baseEnd_3242315 := by
    simpa [prefixWord, tailWord_3242315, baseEnd_3242315] using wordTrace_append hprefix tailTrace_3242315
  have hstable : (prefixWord ++ tailWord_3242315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242315).length < 2 ^ (prefixWord ++ tailWord_3242315).sum := by decide
  have hdescent : baseEnd_3242315 < baseStart_3242315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242345 : List Nat := [1, 2, 1, 1, 1, 3, 3, 5, 5]
def baseStart_3242345 : Nat := 118140960795 + 3242345 * 2 ^ 59
def prefixEnd_3242345 : Nat := 4983230072969 + 3 ^ 40 * 3242345 * 2
def baseEnd_3242345 : Nat := 369973651711604898661385

theorem tailTrace_3242345 : CollatzResearch.WordTrace tailWord_3242345 prefixEnd_3242345 369973651711604898661385 := by
  unfold tailWord_3242345
  simp only [CollatzResearch.WordTrace]
  refine ⟨118258037438545288284944489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78838691625696858856629659 118258037438545288284944489)
  ·
    refine ⟨88693528078908966213708367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118258037438545288284944489 88693528078908966213708367)
    ·
      refine ⟨133040292118363449320562551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88693528078908966213708367 133040292118363449320562551)
      ·
        refine ⟨199560438177545173980843827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133040292118363449320562551 199560438177545173980843827)
        ·
          refine ⟨299340657266317760971265741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199560438177545173980843827 299340657266317760971265741)
          ·
            refine ⟨112252746474869160364224653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299340657266317760971265741 112252746474869160364224653)
            ·
              refine ⟨42094779928075935136584245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112252746474869160364224653 42094779928075935136584245)
              ·
                refine ⟨3946385618257118919054773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42094779928075935136584245 3946385618257118919054773)
                ·
                  refine ⟨369973651711604898661385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3946385618257118919054773 369973651711604898661385)
                  ·
                    rfl

theorem cell22_3242345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_3242345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242345 prefixEnd_3242345 := by exact prefixLift 3242345
  have htrace : WordTrace (prefixWord ++ tailWord_3242345) baseStart_3242345 baseEnd_3242345 := by
    simpa [prefixWord, tailWord_3242345, baseEnd_3242345] using wordTrace_append hprefix tailTrace_3242345
  have hstable : (prefixWord ++ tailWord_3242345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242345).length < 2 ^ (prefixWord ++ tailWord_3242345).sum := by decide
  have hdescent : baseEnd_3242345 < baseStart_3242345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242407 : List Nat := [1, 1, 6, 1, 1, 2, 2, 2, 6]
def baseStart_3242407 : Nat := 118140960795 + 3242407 * 2 ^ 59
def prefixEnd_3242407 : Nat := 4983230072969 + 3 ^ 40 * 3242407 * 2
def baseEnd_3242407 : Nat := 369980726333955733644655

theorem tailTrace_3242407 : CollatzResearch.WordTrace tailWord_3242407 prefixEnd_3242407 369980726333955733644655 := by
  unfold tailWord_3242407
  simp only [CollatzResearch.WordTrace]
  refine ⟨118260298764320672873701475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78840199176213781915800983 118260298764320672873701475)
  ·
    refine ⟨177390448146481009310552213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118260298764320672873701475 177390448146481009310552213)
    ·
      refine ⟨8315177256866297311432135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 177390448146481009310552213 8315177256866297311432135)
      ·
        refine ⟨12472765885299445967148203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315177256866297311432135 12472765885299445967148203)
        ·
          refine ⟨18709148827949168950722305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12472765885299445967148203 18709148827949168950722305)
          ·
            refine ⟨14031861620961876713041729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18709148827949168950722305 14031861620961876713041729)
            ·
              refine ⟨10523896215721407534781297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14031861620961876713041729 10523896215721407534781297)
              ·
                refine ⟨7892922161791055651085973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10523896215721407534781297 7892922161791055651085973)
                ·
                  refine ⟨369980726333955733644655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7892922161791055651085973 369980726333955733644655)
                  ·
                    rfl

theorem cell22_3242407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_3242407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242407 prefixEnd_3242407 := by exact prefixLift 3242407
  have htrace : WordTrace (prefixWord ++ tailWord_3242407) baseStart_3242407 baseEnd_3242407 := by
    simpa [prefixWord, tailWord_3242407, baseEnd_3242407] using wordTrace_append hprefix tailTrace_3242407
  have hstable : (prefixWord ++ tailWord_3242407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242407).length < 2 ^ (prefixWord ++ tailWord_3242407).sum := by decide
  have hdescent : baseEnd_3242407 < baseStart_3242407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242452 : List Nat := [2, 4, 1, 2, 2, 1, 1, 9]
def baseStart_3242452 : Nat := 118140960795 + 3242452 * 2 ^ 59
def prefixEnd_3242452 : Nat := 4983230072969 + 3 ^ 40 * 3242452 * 2
def baseEnd_3242452 : Nat := 123328620380166898173203

theorem tailTrace_3242452 : CollatzResearch.WordTrace tailWord_3242452 prefixEnd_3242452 123328620380166898173203 := by
  unfold tailWord_3242452
  simp only [CollatzResearch.WordTrace]
  refine ⟨59130970024578822779544805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78841293366105097039393073 59130970024578822779544805)
  ·
    refine ⟨11087056879608529271164651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59130970024578822779544805 11087056879608529271164651)
    ·
      refine ⟨16630585319412793906746977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11087056879608529271164651 16630585319412793906746977)
      ·
        refine ⟨12472938989559595430060233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16630585319412793906746977 12472938989559595430060233)
        ·
          refine ⟨9354704242169696572545175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12472938989559595430060233 9354704242169696572545175)
          ·
            refine ⟨14032056363254544858817763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9354704242169696572545175 14032056363254544858817763)
            ·
              refine ⟨21048084544881817288226645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14032056363254544858817763 21048084544881817288226645)
              ·
                refine ⟨123328620380166898173203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21048084544881817288226645 123328620380166898173203)
                ·
                  rfl

theorem cell22_3242452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_3242452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242452 prefixEnd_3242452 := by exact prefixLift 3242452
  have htrace : WordTrace (prefixWord ++ tailWord_3242452) baseStart_3242452 baseEnd_3242452 := by
    simpa [prefixWord, tailWord_3242452, baseEnd_3242452] using wordTrace_append hprefix tailTrace_3242452
  have hstable : (prefixWord ++ tailWord_3242452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242452).length < 2 ^ (prefixWord ++ tailWord_3242452).sum := by decide
  have hdescent : baseEnd_3242452 < baseStart_3242452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242454 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3242454 : Nat := 118140960795 + 3242454 * 2 ^ 59
def prefixEnd_3242454 : Nat := 4983230072969 + 3 ^ 40 * 3242454 * 2
def baseEnd_3242454 : Nat := 1109958268062374745008821

theorem tailTrace_3242454 : CollatzResearch.WordTrace tailWord_3242454 prefixEnd_3242454 1109958268062374745008821 := by
  unfold tailWord_3242454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7391375812196899993791401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78841341996766933267108277 7391375812196899993791401)
  ·
    refine ⟨5543531859147674995343551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7391375812196899993791401 5543531859147674995343551)
    ·
      refine ⟨8315297788721512493015327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5543531859147674995343551 8315297788721512493015327)
      ·
        refine ⟨12472946683082268739522991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8315297788721512493015327 12472946683082268739522991)
        ·
          refine ⟨18709420024623403109284487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12472946683082268739522991 18709420024623403109284487)
          ·
            refine ⟨28064130036935104663926731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18709420024623403109284487 28064130036935104663926731)
            ·
              refine ⟨42096195055402656995890097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28064130036935104663926731 42096195055402656995890097)
              ·
                refine ⟨31572146291551992746917573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42096195055402656995890097 31572146291551992746917573)
                ·
                  refine ⟨5919777429665998640047045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31572146291551992746917573 5919777429665998640047045)
                  ·
                    refine ⟨1109958268062374745008821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5919777429665998640047045 1109958268062374745008821)
                    ·
                      rfl

theorem cell22_3242454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3242454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242454 prefixEnd_3242454 := by exact prefixLift 3242454
  have htrace : WordTrace (prefixWord ++ tailWord_3242454) baseStart_3242454 baseEnd_3242454 := by
    simpa [prefixWord, tailWord_3242454, baseEnd_3242454] using wordTrace_append hprefix tailTrace_3242454
  have hstable : (prefixWord ++ tailWord_3242454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242454).length < 2 ^ (prefixWord ++ tailWord_3242454).sum := by decide
  have hdescent : baseEnd_3242454 < baseStart_3242454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242559 : List Nat := [1, 1, 2, 2, 3, 2, 1, 6, 4]
def baseStart_3242559 : Nat := 118140960795 + 3242559 * 2 ^ 59
def prefixEnd_3242559 : Nat := 4983230072969 + 3 ^ 40 * 3242559 * 2
def baseEnd_3242559 : Nat := 369998070569396490377833

theorem tailTrace_3242559 : CollatzResearch.WordTrace tailWord_3242559 prefixEnd_3242559 369998070569396490377833 := by
  unfold tailWord_3242559
  simp only [CollatzResearch.WordTrace]
  refine ⟨118265842659770002833234731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78843895106513335222156487 118265842659770002833234731)
  ·
    refine ⟨177398763989655004249852097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118265842659770002833234731 177398763989655004249852097)
    ·
      refine ⟨133049072992241253187389073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177398763989655004249852097 133049072992241253187389073)
      ·
        refine ⟨99786804744180939890541805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133049072992241253187389073 99786804744180939890541805)
        ·
          refine ⟨37420051779067852458953177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99786804744180939890541805 37420051779067852458953177)
          ·
            refine ⟨28065038834300889344214883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37420051779067852458953177 28065038834300889344214883)
            ·
              refine ⟨42097558251451334016322325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28065038834300889344214883 42097558251451334016322325)
              ·
                refine ⟨1973323043036781282015109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42097558251451334016322325 1973323043036781282015109)
                ·
                  refine ⟨369998070569396490377833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973323043036781282015109 369998070569396490377833)
                  ·
                    rfl

theorem cell22_3242559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 4].length) (baseStart_3242559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242559 prefixEnd_3242559 := by exact prefixLift 3242559
  have htrace : WordTrace (prefixWord ++ tailWord_3242559) baseStart_3242559 baseEnd_3242559 := by
    simpa [prefixWord, tailWord_3242559, baseEnd_3242559] using wordTrace_append hprefix tailTrace_3242559
  have hstable : (prefixWord ++ tailWord_3242559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242559).length < 2 ^ (prefixWord ++ tailWord_3242559).sum := by decide
  have hdescent : baseEnd_3242559 < baseStart_3242559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242572 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_3242572 : Nat := 118140960795 + 3242572 * 2 ^ 59
def prefixEnd_3242572 : Nat := 4983230072969 + 3 ^ 40 * 3242572 * 2
def baseEnd_3242572 : Nat := 1109998661873861770558459

theorem tailTrace_3242572 : CollatzResearch.WordTrace tailWord_3242572 prefixEnd_3242572 1109998661873861770558459 := by
  unfold tailWord_3242572
  simp only [CollatzResearch.WordTrace]
  refine ⟨59133158404361453026728985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78844211205815270702305313 59133158404361453026728985)
  ·
    refine ⟨44349868803271089770046739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59133158404361453026728985 44349868803271089770046739)
    ·
      refine ⟨66524803204906634655070109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44349868803271089770046739 66524803204906634655070109)
      ·
        refine ⟨24946801201839987995651291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66524803204906634655070109 24946801201839987995651291)
        ·
          refine ⟨37420201802759981993476937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24946801201839987995651291 37420201802759981993476937)
          ·
            refine ⟨28065151352069986495107703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37420201802759981993476937 28065151352069986495107703)
            ·
              refine ⟨42097727028104979742661555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28065151352069986495107703 42097727028104979742661555)
              ·
                refine ⟨63146590542157469613992333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42097727028104979742661555 63146590542157469613992333)
                ·
                  refine ⟨23679971453309051105247125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63146590542157469613992333 23679971453309051105247125)
                  ·
                    refine ⟨1109998661873861770558459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23679971453309051105247125 1109998661873861770558459)
                    ·
                      rfl

theorem cell22_3242572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_3242572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242572 prefixEnd_3242572 := by exact prefixLift 3242572
  have htrace : WordTrace (prefixWord ++ tailWord_3242572) baseStart_3242572 baseEnd_3242572 := by
    simpa [prefixWord, tailWord_3242572, baseEnd_3242572] using wordTrace_append hprefix tailTrace_3242572
  have hstable : (prefixWord ++ tailWord_3242572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242572).length < 2 ^ (prefixWord ++ tailWord_3242572).sum := by decide
  have hdescent : baseEnd_3242572 < baseStart_3242572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242574 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3242574 : Nat := 118140960795 + 3242574 * 2 ^ 59
def prefixEnd_3242574 : Nat := 4983230072969 + 3 ^ 40 * 3242574 * 2
def baseEnd_3242574 : Nat := 1109999346514734432008453

theorem tailTrace_3242574 : CollatzResearch.WordTrace tailWord_3242574 prefixEnd_3242574 1109999346514734432008453 := by
  unfold tailWord_3242574
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783298719339457549378847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78844259836477106930020517 14783298719339457549378847)
  ·
    refine ⟨22174948079009186324068271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14783298719339457549378847 22174948079009186324068271)
    ·
      refine ⟨33262422118513779486102407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22174948079009186324068271 33262422118513779486102407)
      ·
        refine ⟨49893633177770669229153611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33262422118513779486102407 49893633177770669229153611)
        ·
          refine ⟨74840449766656003843730417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49893633177770669229153611 74840449766656003843730417)
          ·
            refine ⟨56130337324992002882797813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74840449766656003843730417 56130337324992002882797813)
            ·
              refine ⟨5262219124218000270262295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56130337324992002882797813 5262219124218000270262295)
              ·
                refine ⟨7893328686327000405393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262219124218000270262295 7893328686327000405393443)
                ·
                  refine ⟨11839993029490500608090165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7893328686327000405393443 11839993029490500608090165)
                  ·
                    refine ⟨1109999346514734432008453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11839993029490500608090165 1109999346514734432008453)
                    ·
                      rfl

theorem cell22_3242574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3242574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242574 prefixEnd_3242574 := by exact prefixLift 3242574
  have htrace : WordTrace (prefixWord ++ tailWord_3242574) baseStart_3242574 baseEnd_3242574 := by
    simpa [prefixWord, tailWord_3242574, baseEnd_3242574] using wordTrace_append hprefix tailTrace_3242574
  have hstable : (prefixWord ++ tailWord_3242574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242574).length < 2 ^ (prefixWord ++ tailWord_3242574).sum := by decide
  have hdescent : baseEnd_3242574 < baseStart_3242574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242606 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3242606 : Nat := 118140960795 + 3242606 * 2 ^ 59
def prefixEnd_3242606 : Nat := 4983230072969 + 3 ^ 40 * 3242606 * 2
def baseEnd_3242606 : Nat := 1110010300768697015208355

theorem tailTrace_3242606 : CollatzResearch.WordTrace tailWord_3242606 prefixEnd_3242606 1110010300768697015208355 := by
  unfold tailWord_3242606
  simp only [CollatzResearch.WordTrace]
  refine ⟨14783444611324966232524459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78845037927066486573463781 14783444611324966232524459)
  ·
    refine ⟨22175166916987449348786689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14783444611324966232524459 22175166916987449348786689)
    ·
      refine ⟨16631375187740587011590017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22175166916987449348786689 16631375187740587011590017)
      ·
        refine ⟨12473531390805440258692513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16631375187740587011590017 12473531390805440258692513)
        ·
          refine ⟨9355148543104080194019385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12473531390805440258692513 9355148543104080194019385)
          ·
            refine ⟨7016361407328060145514539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9355148543104080194019385 7016361407328060145514539)
            ·
              refine ⟨10524542110992090218271809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7016361407328060145514539 10524542110992090218271809)
              ·
                refine ⟨7893406583244067663703857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10524542110992090218271809 7893406583244067663703857)
                ·
                  refine ⟨5920054937433050747777893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7893406583244067663703857 5920054937433050747777893)
                  ·
                    refine ⟨1110010300768697015208355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5920054937433050747777893 1110010300768697015208355)
                    ·
                      rfl

theorem cell22_3242606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3242606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242606 prefixEnd_3242606 := by exact prefixLift 3242606
  have htrace : WordTrace (prefixWord ++ tailWord_3242606) baseStart_3242606 baseEnd_3242606 := by
    simpa [prefixWord, tailWord_3242606, baseEnd_3242606] using wordTrace_append hprefix tailTrace_3242606
  have hstable : (prefixWord ++ tailWord_3242606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242606).length < 2 ^ (prefixWord ++ tailWord_3242606).sum := by decide
  have hdescent : baseEnd_3242606 < baseStart_3242606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242619 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 3, 3]
def baseStart_3242619 : Nat := 118140960795 + 3242619 * 2 ^ 59
def prefixEnd_3242619 : Nat := 4983230072969 + 3 ^ 40 * 3242619 * 2
def baseEnd_3242619 : Nat := 1110014750934369314633315

theorem tailTrace_3242619 : CollatzResearch.WordTrace tailWord_3242619 prefixEnd_3242619 1110014750934369314633315 := by
  unfold tailWord_3242619
  simp only [CollatzResearch.WordTrace]
  refine ⟨118268031039552633080418911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78845354026368422053612607 118268031039552633080418911)
  ·
    refine ⟨177402046559328949620628367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118268031039552633080418911 177402046559328949620628367)
    ·
      refine ⟨266103069838993424430942551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177402046559328949620628367 266103069838993424430942551)
      ·
        refine ⟨399154604758490136646413827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266103069838993424430942551 399154604758490136646413827)
        ·
          refine ⟨598731907137735204969620741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399154604758490136646413827 598731907137735204969620741)
          ·
            refine ⟨112262232588325350931803889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 598731907137735204969620741 112262232588325350931803889)
            ·
              refine ⟨84196674441244013198852917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112262232588325350931803889 84196674441244013198852917)
              ·
                refine ⟨7893438228866626237392461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84196674441244013198852917 7893438228866626237392461)
                ·
                  refine ⟨2960039335824984839022173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7893438228866626237392461 2960039335824984839022173)
                  ·
                    refine ⟨1110014750934369314633315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960039335824984839022173 1110014750934369314633315)
                    ·
                      rfl

theorem cell22_3242619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 3, 3].length) (baseStart_3242619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242619 prefixEnd_3242619 := by exact prefixLift 3242619
  have htrace : WordTrace (prefixWord ++ tailWord_3242619) baseStart_3242619 baseEnd_3242619 := by
    simpa [prefixWord, tailWord_3242619, baseEnd_3242619] using wordTrace_append hprefix tailTrace_3242619
  have hstable : (prefixWord ++ tailWord_3242619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242619).length < 2 ^ (prefixWord ++ tailWord_3242619).sum := by decide
  have hdescent : baseEnd_3242619 < baseStart_3242619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242711 : List Nat := [1, 1, 3, 2, 1, 4, 1, 5, 4]
def baseStart_3242711 : Nat := 118140960795 + 3242711 * 2 ^ 59
def prefixEnd_3242711 : Nat := 4983230072969 + 3 ^ 40 * 3242711 * 2
def baseEnd_3242711 : Nat := 370015414804837247111011

theorem tailTrace_3242711 : CollatzResearch.WordTrace tailWord_3242711 prefixEnd_3242711 370015414804837247111011 := by
  unfold tailWord_3242711
  simp only [CollatzResearch.WordTrace]
  refine ⟨118271386555219332792767987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78847591036812888528511991 118271386555219332792767987)
  ·
    refine ⟨177407079832828999189151981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118271386555219332792767987 177407079832828999189151981)
    ·
      refine ⟨66527654937310874695931993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177407079832828999189151981 66527654937310874695931993)
      ·
        refine ⟨49895741202983156021948995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66527654937310874695931993 49895741202983156021948995)
        ·
          refine ⟨74843611804474734032923493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49895741202983156021948995 74843611804474734032923493)
          ·
            refine ⟨14033177213339012631173155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74843611804474734032923493 14033177213339012631173155)
            ·
              refine ⟨21049765820008518946759733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14033177213339012631173155 21049765820008518946759733)
              ·
                refine ⟨1973415545625798651258725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21049765820008518946759733 1973415545625798651258725)
                ·
                  refine ⟨370015414804837247111011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973415545625798651258725 370015414804837247111011)
                  ·
                    rfl

theorem cell22_3242711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 5, 4].length) (baseStart_3242711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242711 prefixEnd_3242711 := by exact prefixLift 3242711
  have htrace : WordTrace (prefixWord ++ tailWord_3242711) baseStart_3242711 baseEnd_3242711 := by
    simpa [prefixWord, tailWord_3242711, baseEnd_3242711] using wordTrace_append hprefix tailTrace_3242711
  have hstable : (prefixWord ++ tailWord_3242711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242711).length < 2 ^ (prefixWord ++ tailWord_3242711).sum := by decide
  have hdescent : baseEnd_3242711 < baseStart_3242711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242794 : List Nat := [3, 1, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_3242794 : Nat := 118140960795 + 3242794 * 2 ^ 59
def prefixEnd_3242794 : Nat := 4983230072969 + 3 ^ 40 * 3242794 * 2
def baseEnd_3242794 : Nat := 1110074657010727191507779

theorem tailTrace_3242794 : CollatzResearch.WordTrace tailWord_3242794 prefixEnd_3242794 1110074657010727191507779 := by
  unfold tailWord_3242794
  simp only [CollatzResearch.WordTrace]
  refine ⟨29568603453479659492009859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78849609209279091978692957 29568603453479659492009859)
  ·
    refine ⟨44352905180219489238014789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29568603453479659492009859 44352905180219489238014789)
    ·
      refine ⟨8316169721291154232127773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44352905180219489238014789 8316169721291154232127773)
      ·
        refine ⟨3118563645484182837047915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8316169721291154232127773 3118563645484182837047915)
        ·
          refine ⟨4677845468226274255571873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118563645484182837047915 4677845468226274255571873)
          ·
            refine ⟨3508384101169705691678905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4677845468226274255571873 3508384101169705691678905)
            ·
              refine ⟨2631288075877279268759179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3508384101169705691678905 2631288075877279268759179)
              ·
                refine ⟨3946932113815918903138769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631288075877279268759179 3946932113815918903138769)
                ·
                  refine ⟨2960199085361939177354077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3946932113815918903138769 2960199085361939177354077)
                  ·
                    refine ⟨1110074657010727191507779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960199085361939177354077 1110074657010727191507779)
                    ·
                      rfl

theorem cell22_3242794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_3242794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242794 prefixEnd_3242794 := by exact prefixLift 3242794
  have htrace : WordTrace (prefixWord ++ tailWord_3242794) baseStart_3242794 baseEnd_3242794 := by
    simpa [prefixWord, tailWord_3242794, baseEnd_3242794] using wordTrace_append hprefix tailTrace_3242794
  have hstable : (prefixWord ++ tailWord_3242794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242794).length < 2 ^ (prefixWord ++ tailWord_3242794).sum := by decide
  have hdescent : baseEnd_3242794 < baseStart_3242794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242801 : List Nat := [1, 2, 2, 3, 2, 1, 3, 3, 5]
def baseStart_3242801 : Nat := 118140960795 + 3242801 * 2 ^ 59
def prefixEnd_3242801 : Nat := 4983230072969 + 3 ^ 40 * 3242801 * 2
def baseEnd_3242801 : Nat := 370025684417927168860919

theorem tailTrace_3242801 : CollatzResearch.WordTrace tailWord_3242801 prefixEnd_3242801 370025684417927168860919 := by
  unfold tailWord_3242801
  simp only [CollatzResearch.WordTrace]
  refine ⟨118274669124893278163544257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78849779416595518775696171 118274669124893278163544257)
  ·
    refine ⟨88706001843669958622658193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118274669124893278163544257 88706001843669958622658193)
    ·
      refine ⟨66529501382752468966993645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88706001843669958622658193 66529501382752468966993645)
      ·
        refine ⟨24948563018532175862622617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66529501382752468966993645 24948563018532175862622617)
        ·
          refine ⟨18711422263899131896966963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24948563018532175862622617 18711422263899131896966963)
          ·
            refine ⟨28067133395848697845450445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18711422263899131896966963 28067133395848697845450445)
            ·
              refine ⟨10525175023443261692043917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28067133395848697845450445 10525175023443261692043917)
              ·
                refine ⟨3946940633791223134516469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10525175023443261692043917 3946940633791223134516469)
                ·
                  refine ⟨370025684417927168860919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3946940633791223134516469 370025684417927168860919)
                  ·
                    rfl

theorem cell22_3242801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_3242801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242801 prefixEnd_3242801 := by exact prefixLift 3242801
  have htrace : WordTrace (prefixWord ++ tailWord_3242801) baseStart_3242801 baseEnd_3242801 := by
    simpa [prefixWord, tailWord_3242801, baseEnd_3242801] using wordTrace_append hprefix tailTrace_3242801
  have hstable : (prefixWord ++ tailWord_3242801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242801).length < 2 ^ (prefixWord ++ tailWord_3242801).sum := by decide
  have hdescent : baseEnd_3242801 < baseStart_3242801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242925 : List Nat := [1, 5, 2, 3, 1, 1, 1, 8]
def baseStart_3242925 : Nat := 118140960795 + 3242925 * 2 ^ 59
def prefixEnd_3242925 : Nat := 4983230072969 + 3 ^ 40 * 3242925 * 2
def baseEnd_3242925 : Nat := 123346611220876279609153

theorem tailTrace_3242925 : CollatzResearch.WordTrace tailWord_3242925 prefixEnd_3242925 123346611220876279609153 := by
  unfold tailWord_3242925
  simp only [CollatzResearch.WordTrace]
  refine ⟨118279191776444047341058229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78852794517629364894038819 118279191776444047341058229)
  ·
    refine ⟨11088674229041629438224209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118279191776444047341058229 11088674229041629438224209)
    ·
      refine ⟨8316505671781222078668157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11088674229041629438224209 8316505671781222078668157)
      ·
        refine ⟨3118689626917958279500559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8316505671781222078668157 3118689626917958279500559)
        ·
          refine ⟨4678034440376937419250839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118689626917958279500559 4678034440376937419250839)
          ·
            refine ⟨7017051660565406128876259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4678034440376937419250839 7017051660565406128876259)
            ·
              refine ⟨10525577490848109193314389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7017051660565406128876259 10525577490848109193314389)
              ·
                refine ⟨123346611220876279609153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10525577490848109193314389 123346611220876279609153)
                ·
                  rfl

theorem cell22_3242925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 8].length) (baseStart_3242925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242925 prefixEnd_3242925 := by exact prefixLift 3242925
  have htrace : WordTrace (prefixWord ++ tailWord_3242925) baseStart_3242925 baseEnd_3242925 := by
    simpa [prefixWord, tailWord_3242925, baseEnd_3242925] using wordTrace_append hprefix tailTrace_3242925
  have hstable : (prefixWord ++ tailWord_3242925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242925).length < 2 ^ (prefixWord ++ tailWord_3242925).sum := by decide
  have hdescent : baseEnd_3242925 < baseStart_3242925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242936 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_3242936 : Nat := 118140960795 + 3242936 * 2 ^ 59
def prefixEnd_3242936 : Nat := 4983230072969 + 3 ^ 40 * 3242936 * 2
def baseEnd_3242936 : Nat := 370041088837562051485781

theorem tailTrace_3242936 : CollatzResearch.WordTrace tailWord_3242936 prefixEnd_3242936 370041088837562051485781 := by
  unfold tailWord_3242936
  simp only [CollatzResearch.WordTrace]
  refine ⟨59139796489702098109854331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78853061986269464146472441 59139796489702098109854331)
  ·
    refine ⟨88709694734553147164781497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59139796489702098109854331 88709694734553147164781497)
    ·
      refine ⟨66532271050914860373586123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88709694734553147164781497 66532271050914860373586123)
      ·
        refine ⟨99798406576372290560379185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66532271050914860373586123 99798406576372290560379185)
        ·
          refine ⟨74848804932279217920284389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99798406576372290560379185 74848804932279217920284389)
          ·
            refine ⟨14034150924802353360053323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74848804932279217920284389 14034150924802353360053323)
            ·
              refine ⟨21051226387203530040079985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14034150924802353360053323 21051226387203530040079985)
              ·
                refine ⟨15788419790402647530059989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21051226387203530040079985 15788419790402647530059989)
                ·
                  refine ⟨370041088837562051485781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15788419790402647530059989 370041088837562051485781)
                  ·
                    rfl

theorem cell22_3242936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_3242936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242936 prefixEnd_3242936 := by exact prefixLift 3242936
  have htrace : WordTrace (prefixWord ++ tailWord_3242936) baseStart_3242936 baseEnd_3242936 := by
    simpa [prefixWord, tailWord_3242936, baseEnd_3242936] using wordTrace_append hprefix tailTrace_3242936
  have hstable : (prefixWord ++ tailWord_3242936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242936).length < 2 ^ (prefixWord ++ tailWord_3242936).sum := by decide
  have hdescent : baseEnd_3242936 < baseStart_3242936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242951 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_3242951 : Nat := 118140960795 + 3242951 * 2 ^ 59
def prefixEnd_3242951 : Nat := 4983230072969 + 3 ^ 40 * 3242951 * 2
def baseEnd_3242951 : Nat := 1110128401319231115332297

theorem tailTrace_3242951 : CollatzResearch.WordTrace tailWord_3242951 prefixEnd_3242951 1110128401319231115332297 := by
  unfold tailWord_3242951
  simp only [CollatzResearch.WordTrace]
  refine ⟨118280140074349853781504707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78853426716233235854336471 118280140074349853781504707)
  ·
    refine ⟨177420210111524780672257061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118280140074349853781504707 177420210111524780672257061)
    ·
      refine ⟨33266289395910896376048199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177420210111524780672257061 33266289395910896376048199)
      ·
        refine ⟨49899434093866344564072299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33266289395910896376048199 49899434093866344564072299)
        ·
          refine ⟨74849151140799516846108449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49899434093866344564072299 74849151140799516846108449)
          ·
            refine ⟨56136863355599637634581337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74849151140799516846108449 56136863355599637634581337)
            ·
              refine ⟨42102647516699728225936003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56136863355599637634581337 42102647516699728225936003)
              ·
                refine ⟨63153971275049592338904005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42102647516699728225936003 63153971275049592338904005)
                ·
                  refine ⟨11841369614071798563544501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63153971275049592338904005 11841369614071798563544501)
                  ·
                    refine ⟨1110128401319231115332297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11841369614071798563544501 1110128401319231115332297)
                    ·
                      rfl

theorem cell22_3242951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_3242951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242951 prefixEnd_3242951 := by exact prefixLift 3242951
  have htrace : WordTrace (prefixWord ++ tailWord_3242951) baseStart_3242951 baseEnd_3242951 := by
    simpa [prefixWord, tailWord_3242951, baseEnd_3242951] using wordTrace_append hprefix tailTrace_3242951
  have hstable : (prefixWord ++ tailWord_3242951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242951).length < 2 ^ (prefixWord ++ tailWord_3242951).sum := by decide
  have hdescent : baseEnd_3242951 < baseStart_3242951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3242970 : List Nat := [3, 1, 1, 2, 4, 1, 4, 1, 5]
def baseStart_3242970 : Nat := 118140960795 + 3242970 * 2 ^ 59
def prefixEnd_3242970 : Nat := 4983230072969 + 3 ^ 40 * 3242970 * 2
def baseEnd_3242970 : Nat := 370044968469173799702413

theorem tailTrace_3242970 : CollatzResearch.WordTrace tailWord_3242970 prefixEnd_3242970 370044968469173799702413 := by
  unfold tailWord_3242970
  simp only [CollatzResearch.WordTrace]
  refine ⟨29570208265320255006611591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78853888707520680017630909 29570208265320255006611591)
  ·
    refine ⟨44355312397980382509917387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29570208265320255006611591 44355312397980382509917387)
    ·
      refine ⟨66532968596970573764876081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44355312397980382509917387 66532968596970573764876081)
      ·
        refine ⟨49899726447727930323657061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66532968596970573764876081 49899726447727930323657061)
        ·
          refine ⟨9356198708948986935685699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49899726447727930323657061 9356198708948986935685699)
          ·
            refine ⟨14034298063423480403528549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9356198708948986935685699 14034298063423480403528549)
            ·
              refine ⟨2631430886891902575661603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14034298063423480403528549 2631430886891902575661603)
              ·
                refine ⟨3947146330337853863492405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631430886891902575661603 3947146330337853863492405)
                ·
                  refine ⟨370044968469173799702413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947146330337853863492405 370044968469173799702413)
                  ·
                    rfl

theorem cell22_3242970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_3242970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3242970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3242970 prefixEnd_3242970 := by exact prefixLift 3242970
  have htrace : WordTrace (prefixWord ++ tailWord_3242970) baseStart_3242970 baseEnd_3242970 := by
    simpa [prefixWord, tailWord_3242970, baseEnd_3242970] using wordTrace_append hprefix tailTrace_3242970
  have hstable : (prefixWord ++ tailWord_3242970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3242970).length < 2 ^ (prefixWord ++ tailWord_3242970).sum := by decide
  have hdescent : baseEnd_3242970 < baseStart_3242970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3242970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243011 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_3243011 : Nat := 118140960795 + 3243011 * 2 ^ 59
def prefixEnd_3243011 : Nat := 4983230072969 + 3 ^ 40 * 3243011 * 2
def baseEnd_3243011 : Nat := 1110148940545410958832113

theorem tailTrace_3243011 : CollatzResearch.WordTrace tailWord_3243011 prefixEnd_3243011 1110148940545410958832113 := by
  unfold tailWord_3243011
  simp only [CollatzResearch.WordTrace]
  refine ⟨118282328454132484028688887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78854885636088322685792591 118282328454132484028688887)
  ·
    refine ⟨177423492681198726043033331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118282328454132484028688887 177423492681198726043033331)
    ·
      refine ⟨266135239021798089064549997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177423492681198726043033331 266135239021798089064549997)
      ·
        refine ⟨99800714633174283399206249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266135239021798089064549997 99800714633174283399206249)
        ·
          refine ⟨74850535974880712549404687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99800714633174283399206249 74850535974880712549404687)
          ·
            refine ⟨112275803962321068824107031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74850535974880712549404687 112275803962321068824107031)
            ·
              refine ⟨168413705943481603236160547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112275803962321068824107031 168413705943481603236160547)
              ·
                refine ⟨252620558915222404854240821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168413705943481603236160547 252620558915222404854240821)
                ·
                  refine ⟨23683177398302100455085077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252620558915222404854240821 23683177398302100455085077)
                  ·
                    refine ⟨1110148940545410958832113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23683177398302100455085077 1110148940545410958832113)
                    ·
                      rfl

theorem cell22_3243011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_3243011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243011 prefixEnd_3243011 := by exact prefixLift 3243011
  have htrace : WordTrace (prefixWord ++ tailWord_3243011) baseStart_3243011 baseEnd_3243011 := by
    simpa [prefixWord, tailWord_3243011, baseEnd_3243011] using wordTrace_append hprefix tailTrace_3243011
  have hstable : (prefixWord ++ tailWord_3243011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243011).length < 2 ^ (prefixWord ++ tailWord_3243011).sum := by decide
  have hdescent : baseEnd_3243011 < baseStart_3243011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243015 : List Nat := [1, 1, 4, 3, 1, 1, 3, 4, 4]
def baseStart_3243015 : Nat := 118140960795 + 3243015 * 2 ^ 59
def prefixEnd_3243015 : Nat := 4983230072969 + 3 ^ 40 * 3243015 * 2
def baseEnd_3243015 : Nat := 370050103275718760577367

theorem tailTrace_3243015 : CollatzResearch.WordTrace tailWord_3243015 prefixEnd_3243015 370050103275718760577367 := by
  unfold tailWord_3243015
  simp only [CollatzResearch.WordTrace]
  refine ⟨118282474346117992711834499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78854982897411995141222999 118282474346117992711834499)
  ·
    refine ⟨177423711519176989067751749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118282474346117992711834499 177423711519176989067751749)
    ·
      refine ⟨33266945909845685450203453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177423711519176989067751749 33266945909845685450203453)
      ·
        refine ⟨12475104716192132043826295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33266945909845685450203453 12475104716192132043826295)
        ·
          refine ⟨18712657074288198065739443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475104716192132043826295 18712657074288198065739443)
          ·
            refine ⟨28068985611432297098609165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18712657074288198065739443 28068985611432297098609165)
            ·
              refine ⟨10525869604287111411978437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28068985611432297098609165 10525869604287111411978437)
              ·
                refine ⟨1973600550803833389745957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10525869604287111411978437 1973600550803833389745957)
                ·
                  refine ⟨370050103275718760577367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1973600550803833389745957 370050103275718760577367)
                  ·
                    rfl

theorem cell22_3243015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 4].length) (baseStart_3243015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243015 prefixEnd_3243015 := by exact prefixLift 3243015
  have htrace : WordTrace (prefixWord ++ tailWord_3243015) baseStart_3243015 baseEnd_3243015 := by
    simpa [prefixWord, tailWord_3243015, baseEnd_3243015] using wordTrace_append hprefix tailTrace_3243015
  have hstable : (prefixWord ++ tailWord_3243015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243015).length < 2 ^ (prefixWord ++ tailWord_3243015).sum := by decide
  have hdescent : baseEnd_3243015 < baseStart_3243015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243060 : List Nat := [2, 5, 1, 2, 1, 2, 9]
def baseStart_3243060 : Nat := 118140960795 + 3243060 * 2 ^ 59
def prefixEnd_3243060 : Nat := 4983230072969 + 3 ^ 40 * 3243060 * 2
def baseEnd_3243060 : Nat := 41117248675807080161369

theorem tailTrace_3243060 : CollatzResearch.WordTrace tailWord_3243060 prefixEnd_3243060 41117248675807080161369 := by
  unfold tailWord_3243060
  simp only [CollatzResearch.WordTrace]
  refine ⟨59142057815477482698611317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78856077087303310264815089 59142057815477482698611317)
  ·
    refine ⟨5544567920201014002994811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59142057815477482698611317 5544567920201014002994811)
    ·
      refine ⟨8316851880301521004492217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5544567920201014002994811 8316851880301521004492217)
      ·
        refine ⟨6237638910226140753369163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8316851880301521004492217 6237638910226140753369163)
        ·
          refine ⟨9356458365339211130053745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6237638910226140753369163 9356458365339211130053745)
          ·
            refine ⟨7017343774004408347540309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9356458365339211130053745 7017343774004408347540309)
            ·
              refine ⟨41117248675807080161369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7017343774004408347540309 41117248675807080161369)
              ·
                rfl

theorem cell22_3243060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 9].length) (baseStart_3243060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243060 prefixEnd_3243060 := by exact prefixLift 3243060
  have htrace : WordTrace (prefixWord ++ tailWord_3243060) baseStart_3243060 baseEnd_3243060 := by
    simpa [prefixWord, tailWord_3243060, baseEnd_3243060] using wordTrace_append hprefix tailTrace_3243060
  have hstable : (prefixWord ++ tailWord_3243060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243060).length < 2 ^ (prefixWord ++ tailWord_3243060).sum := by decide
  have hdescent : baseEnd_3243060 < baseStart_3243060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243075 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 3, 3]
def baseStart_3243075 : Nat := 118140960795 + 3243075 * 2 ^ 59
def prefixEnd_3243075 : Nat := 4983230072969 + 3 ^ 40 * 3243075 * 2
def baseEnd_3243075 : Nat := 1110170849053336125231917

theorem tailTrace_3243075 : CollatzResearch.WordTrace tailWord_3243075 prefixEnd_3243075 1110170849053336125231917 := by
  unfold tailWord_3243075
  simp only [CollatzResearch.WordTrace]
  refine ⟨118284662725900622959018679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78856441817267081972679119 118284662725900622959018679)
  ·
    refine ⟨177426994088850934438528019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118284662725900622959018679 177426994088850934438528019)
    ·
      refine ⟨266140491133276401657792029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177426994088850934438528019 266140491133276401657792029)
      ·
        refine ⟨99802684174978650621672011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266140491133276401657792029 99802684174978650621672011)
        ·
          refine ⟨149704026262467975932508017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99802684174978650621672011 149704026262467975932508017)
          ·
            refine ⟨112278019696850981949381013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149704026262467975932508017 112278019696850981949381013)
            ·
              refine ⟨5263032173289889778877235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112278019696850981949381013 5263032173289889778877235)
              ·
                refine ⟨7894548259934834668315853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263032173289889778877235 7894548259934834668315853)
                ·
                  refine ⟨2960455597475563000618445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7894548259934834668315853 2960455597475563000618445)
                  ·
                    refine ⟨1110170849053336125231917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960455597475563000618445 1110170849053336125231917)
                    ·
                      rfl

theorem cell22_3243075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 3].length) (baseStart_3243075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243075 prefixEnd_3243075 := by exact prefixLift 3243075
  have htrace : WordTrace (prefixWord ++ tailWord_3243075) baseStart_3243075 baseEnd_3243075 := by
    simpa [prefixWord, tailWord_3243075, baseEnd_3243075] using wordTrace_append hprefix tailTrace_3243075
  have hstable : (prefixWord ++ tailWord_3243075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243075).length < 2 ^ (prefixWord ++ tailWord_3243075).sum := by decide
  have hdescent : baseEnd_3243075 < baseStart_3243075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243088 : List Nat := [2, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_3243088 : Nat := 118140960795 + 3243088 * 2 ^ 59
def prefixEnd_3243088 : Nat := 4983230072969 + 3 ^ 40 * 3243088 * 2
def baseEnd_3243088 : Nat := 370058433073002808218959

theorem tailTrace_3243088 : CollatzResearch.WordTrace tailWord_3243088 prefixEnd_3243088 370058433073002808218959 := by
  unfold tailWord_3243088
  simp only [CollatzResearch.WordTrace]
  refine ⟨59142568437426763089620959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78856757916569017452827945 59142568437426763089620959)
  ·
    refine ⟨88713852656140144634431439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59142568437426763089620959 88713852656140144634431439)
    ·
      refine ⟨133070778984210216951647159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88713852656140144634431439 133070778984210216951647159)
      ·
        refine ⟨199606168476315325427470739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133070778984210216951647159 199606168476315325427470739)
        ·
          refine ⟨299409252714472988141206109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199606168476315325427470739 299409252714472988141206109)
          ·
            refine ⟨112278469767927370552952291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299409252714472988141206109 112278469767927370552952291)
            ·
              refine ⟨168417704651891055829428437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112278469767927370552952291 168417704651891055829428437)
              ·
                refine ⟨3947289952778696621002229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168417704651891055829428437 3947289952778696621002229)
                ·
                  refine ⟨370058433073002808218959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947289952778696621002229 370058433073002808218959)
                  ·
                    rfl

theorem cell22_3243088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_3243088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243088 prefixEnd_3243088 := by exact prefixLift 3243088
  have htrace : WordTrace (prefixWord ++ tailWord_3243088) baseStart_3243088 baseEnd_3243088 := by
    simpa [prefixWord, tailWord_3243088, baseEnd_3243088] using wordTrace_append hprefix tailTrace_3243088
  have hstable : (prefixWord ++ tailWord_3243088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243088).length < 2 ^ (prefixWord ++ tailWord_3243088).sum := by decide
  have hdescent : baseEnd_3243088 < baseStart_3243088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243126 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_3243126 : Nat := 118140960795 + 3243126 * 2 ^ 59
def prefixEnd_3243126 : Nat := 4983230072969 + 3 ^ 40 * 3243126 * 2
def baseEnd_3243126 : Nat := 1110188307395588992206761

theorem tailTrace_3243126 : CollatzResearch.WordTrace tailWord_3243126 prefixEnd_3243126 1110188307395588992206761 := by
  unfold tailWord_3243126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7392907678044741166820327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78857681899143905779416821 7392907678044741166820327)
  ·
    refine ⟨11089361517067111750230491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7392907678044741166820327 11089361517067111750230491)
    ·
      refine ⟨16634042275600667625345737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11089361517067111750230491 16634042275600667625345737)
      ·
        refine ⟨12475531706700500719009303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16634042275600667625345737 12475531706700500719009303)
        ·
          refine ⟨18713297560050751078513955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12475531706700500719009303 18713297560050751078513955)
          ·
            refine ⟨28069946340076126617770933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713297560050751078513955 28069946340076126617770933)
            ·
              refine ⟨2631557469382136870416025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28069946340076126617770933 2631557469382136870416025)
              ·
                refine ⟨1973668102036602652812019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2631557469382136870416025 1973668102036602652812019)
                ·
                  refine ⟨2960502153054903979218029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973668102036602652812019 2960502153054903979218029)
                  ·
                    refine ⟨1110188307395588992206761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960502153054903979218029 1110188307395588992206761)
                    ·
                      rfl

theorem cell22_3243126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_3243126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243126 prefixEnd_3243126 := by exact prefixLift 3243126
  have htrace : WordTrace (prefixWord ++ tailWord_3243126) baseStart_3243126 baseEnd_3243126 := by
    simpa [prefixWord, tailWord_3243126, baseEnd_3243126] using wordTrace_append hprefix tailTrace_3243126
  have hstable : (prefixWord ++ tailWord_3243126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243126).length < 2 ^ (prefixWord ++ tailWord_3243126).sum := by decide
  have hdescent : baseEnd_3243126 < baseStart_3243126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243148 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_3243148 : Nat := 118140960795 + 3243148 * 2 ^ 59
def prefixEnd_3243148 : Nat := 4983230072969 + 3 ^ 40 * 3243148 * 2
def baseEnd_3243148 : Nat := 1110195838445188268156693

theorem tailTrace_3243148 : CollatzResearch.WordTrace tailWord_3243148 prefixEnd_3243148 1110195838445188268156693 := by
  unfold tailWord_3243148
  simp only [CollatzResearch.WordTrace]
  refine ⟨59143662627318078213213049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78858216836424104284284065 59143662627318078213213049)
  ·
    refine ⟨44357746970488558659909787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59143662627318078213213049 44357746970488558659909787)
    ·
      refine ⟨66536620455732837989864681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44357746970488558659909787 66536620455732837989864681)
      ·
        refine ⟨49902465341799628492398511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66536620455732837989864681 49902465341799628492398511)
        ·
          refine ⟨74853698012699442738597767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49902465341799628492398511 74853698012699442738597767)
          ·
            refine ⟨112280547019049164107896651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74853698012699442738597767 112280547019049164107896651)
            ·
              refine ⟨168420820528573746161844977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112280547019049164107896651 168420820528573746161844977)
              ·
                refine ⟨126315615396430309621383733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168420820528573746161844977 126315615396430309621383733)
                ·
                  refine ⟨11842088943415341527004725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126315615396430309621383733 11842088943415341527004725)
                  ·
                    refine ⟨1110195838445188268156693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11842088943415341527004725 1110195838445188268156693)
                    ·
                      rfl

theorem cell22_3243148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_3243148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243148 prefixEnd_3243148 := by exact prefixLift 3243148
  have htrace : WordTrace (prefixWord ++ tailWord_3243148) baseStart_3243148 baseEnd_3243148 := by
    simpa [prefixWord, tailWord_3243148, baseEnd_3243148] using wordTrace_append hprefix tailTrace_3243148
  have hstable : (prefixWord ++ tailWord_3243148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243148).length < 2 ^ (prefixWord ++ tailWord_3243148).sum := by decide
  have hdescent : baseEnd_3243148 < baseStart_3243148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243165 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3243165 : Nat := 118140960795 + 3243165 * 2 ^ 59
def prefixEnd_3243165 : Nat := 4983230072969 + 3 ^ 40 * 3243165 * 2
def baseEnd_3243165 : Nat := 1110201657892605890481641

theorem tailTrace_3243165 : CollatzResearch.WordTrace tailWord_3243165 prefixEnd_3243165 1110201657892605890481641 := by
  unfold tailWord_3243165
  simp only [CollatzResearch.WordTrace]
  refine ⟨118287945295574568329794949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78858630197049712219863299 118287945295574568329794949)
  ·
    refine ⟨22178989742920231561836553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118287945295574568329794949 22178989742920231561836553)
    ·
      refine ⟨16634242307190173671377415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22178989742920231561836553 16634242307190173671377415)
      ·
        refine ⟨24951363460785260507066123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16634242307190173671377415 24951363460785260507066123)
        ·
          refine ⟨37427045191177890760599185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24951363460785260507066123 37427045191177890760599185)
          ·
            refine ⟨28070283893383418070449389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37427045191177890760599185 28070283893383418070449389)
            ·
              refine ⟨10526356460018781776418521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28070283893383418070449389 10526356460018781776418521)
              ·
                refine ⟨7894767345014086332313891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10526356460018781776418521 7894767345014086332313891)
                ·
                  refine ⟨11842151017521129498470837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7894767345014086332313891 11842151017521129498470837)
                  ·
                    refine ⟨1110201657892605890481641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11842151017521129498470837 1110201657892605890481641)
                    ·
                      rfl

theorem cell22_3243165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3243165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243165 prefixEnd_3243165 := by exact prefixLift 3243165
  have htrace : WordTrace (prefixWord ++ tailWord_3243165) baseStart_3243165 baseEnd_3243165 := by
    simpa [prefixWord, tailWord_3243165, baseEnd_3243165] using wordTrace_append hprefix tailTrace_3243165
  have hstable : (prefixWord ++ tailWord_3243165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243165).length < 2 ^ (prefixWord ++ tailWord_3243165).sum := by decide
  have hdescent : baseEnd_3243165 < baseStart_3243165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243214 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3243214 : Nat := 118140960795 + 3243214 * 2 ^ 59
def prefixEnd_3243214 : Nat := 4983230072969 + 3 ^ 40 * 3243214 * 2
def baseEnd_3243214 : Nat := 1110218431593986096006491

theorem tailTrace_3243214 : CollatzResearch.WordTrace tailWord_3243214 prefixEnd_3243214 1110218431593986096006491 := by
  unfold tailWord_3243214
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786216559049631212291087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78859821648264699798885797 14786216559049631212291087)
  ·
    refine ⟨22179324838574446818436631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14786216559049631212291087 22179324838574446818436631)
    ·
      refine ⟨33268987257861670227654947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22179324838574446818436631 33268987257861670227654947)
      ·
        refine ⟨49903480886792505341482421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33268987257861670227654947 49903480886792505341482421)
        ·
          refine ⟨4678451333136797375763977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49903480886792505341482421 4678451333136797375763977)
          ·
            refine ⟨3508838499852598031822983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4678451333136797375763977 3508838499852598031822983)
            ·
              refine ⟨5263257749778897047734475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508838499852598031822983 5263257749778897047734475)
              ·
                refine ⟨7894886624668345571601713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263257749778897047734475 7894886624668345571601713)
                ·
                  refine ⟨5921164968501259178701285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7894886624668345571601713 5921164968501259178701285)
                  ·
                    refine ⟨1110218431593986096006491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921164968501259178701285 1110218431593986096006491)
                    ·
                      rfl

theorem cell22_3243214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3243214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243214 prefixEnd_3243214 := by exact prefixLift 3243214
  have htrace : WordTrace (prefixWord ++ tailWord_3243214) baseStart_3243214 baseEnd_3243214 := by
    simpa [prefixWord, tailWord_3243214, baseEnd_3243214] using wordTrace_append hprefix tailTrace_3243214
  have hstable : (prefixWord ++ tailWord_3243214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243214).length < 2 ^ (prefixWord ++ tailWord_3243214).sum := by decide
  have hdescent : baseEnd_3243214 < baseStart_3243214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243240 : List Nat := [2, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_3243240 : Nat := 118140960795 + 3243240 * 2 ^ 59
def prefixEnd_3243240 : Nat := 4983230072969 + 3 ^ 40 * 3243240 * 2
def baseEnd_3243240 : Nat := 370075777308443564952137

theorem tailTrace_3243240 : CollatzResearch.WordTrace tailWord_3243240 prefixEnd_3243240 370075777308443564952137 := by
  unfold tailWord_3243240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145340385151428069387587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78860453846868570759183449 59145340385151428069387587)
  ·
    refine ⟨88718010577727142104081381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59145340385151428069387587 88718010577727142104081381)
    ·
      refine ⟨16634626983323839144515259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88718010577727142104081381 16634626983323839144515259)
      ·
        refine ⟨24951940474985758716772889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16634626983323839144515259 24951940474985758716772889)
        ·
          refine ⟨18713955356239319037579667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24951940474985758716772889 18713955356239319037579667)
          ·
            refine ⟨28070933034358978556369501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18713955356239319037579667 28070933034358978556369501)
            ·
              refine ⟨10526599887884616958638563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28070933034358978556369501 10526599887884616958638563)
              ·
                refine ⟨15789899831826925437957845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10526599887884616958638563 15789899831826925437957845)
                ·
                  refine ⟨370075777308443564952137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15789899831826925437957845 370075777308443564952137)
                  ·
                    rfl

theorem cell22_3243240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_3243240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243240 prefixEnd_3243240 := by exact prefixLift 3243240
  have htrace : WordTrace (prefixWord ++ tailWord_3243240) baseStart_3243240 baseEnd_3243240 := by
    simpa [prefixWord, tailWord_3243240, baseEnd_3243240] using wordTrace_append hprefix tailTrace_3243240
  have hstable : (prefixWord ++ tailWord_3243240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243240).length < 2 ^ (prefixWord ++ tailWord_3243240).sum := by decide
  have hdescent : baseEnd_3243240 < baseStart_3243240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243244 : List Nat := [2, 2, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_3243244 : Nat := 118140960795 + 3243244 * 2 ^ 59
def prefixEnd_3243244 : Nat := 4983230072969 + 3 ^ 40 * 3243244 * 2
def baseEnd_3243244 : Nat := 1110228701207076017756399

theorem tailTrace_3243244 : CollatzResearch.WordTrace tailWord_3243244 prefixEnd_3243244 1110228701207076017756399 := by
  unfold tailWord_3243244
  simp only [CollatzResearch.WordTrace]
  refine ⟨59145413331144182410960393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78860551108192243214613857 59145413331144182410960393)
  ·
    refine ⟨44359059998358136808220295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59145413331144182410960393 44359059998358136808220295)
    ·
      refine ⟨66538589997537205212330443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44359059998358136808220295 66538589997537205212330443)
      ·
        refine ⟨99807884996305807818495665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66538589997537205212330443 99807884996305807818495665)
        ·
          refine ⟨74855913747229355863871749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99807884996305807818495665 74855913747229355863871749)
          ·
            refine ⟨14035483827605504224475953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74855913747229355863871749 14035483827605504224475953)
            ·
              refine ⟨10526612870704128168356965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14035483827605504224475953 10526612870704128168356965)
              ·
                refine ⟨1973739913257024031566931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10526612870704128168356965 1973739913257024031566931)
                ·
                  refine ⟨2960609869885536047350397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973739913257024031566931 2960609869885536047350397)
                  ·
                    refine ⟨1110228701207076017756399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960609869885536047350397 1110228701207076017756399)
                    ·
                      rfl

theorem cell22_3243244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_3243244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243244 prefixEnd_3243244 := by exact prefixLift 3243244
  have htrace : WordTrace (prefixWord ++ tailWord_3243244) baseStart_3243244 baseEnd_3243244 := by
    simpa [prefixWord, tailWord_3243244, baseEnd_3243244] using wordTrace_append hprefix tailTrace_3243244
  have hstable : (prefixWord ++ tailWord_3243244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243244).length < 2 ^ (prefixWord ++ tailWord_3243244).sum := by decide
  have hdescent : baseEnd_3243244 < baseStart_3243244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243257 : List Nat := [1, 2, 1, 3, 1, 1, 7, 1, 5]
def baseStart_3243257 : Nat := 118140960795 + 3243257 * 2 ^ 59
def prefixEnd_3243257 : Nat := 4983230072969 + 3 ^ 40 * 3243257 * 2
def baseEnd_3243257 : Nat := 370077717124249439060453

theorem tailTrace_3243257 : CollatzResearch.WordTrace tailWord_3243257 prefixEnd_3243257 370077717124249439060453 := by
  unfold tailWord_3243257
  simp only [CollatzResearch.WordTrace]
  refine ⟨118291300811241268042144025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78860867207494178694762683 118291300811241268042144025)
  ·
    refine ⟨88718475608430951031608019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118291300811241268042144025 88718475608430951031608019)
    ·
      refine ⟨133077713412646426547412029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88718475608430951031608019 133077713412646426547412029)
      ·
        refine ⟨49904142529742409955279511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133077713412646426547412029 49904142529742409955279511)
        ·
          refine ⟨74856213794613614932919267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49904142529742409955279511 74856213794613614932919267)
          ·
            refine ⟨112284320691920422399378901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74856213794613614932919267 112284320691920422399378901)
            ·
              refine ⟨2631663766216884899985443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 112284320691920422399378901 2631663766216884899985443)
              ·
                refine ⟨3947495649325327349978165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631663766216884899985443 3947495649325327349978165)
                ·
                  refine ⟨370077717124249439060453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947495649325327349978165 370077717124249439060453)
                  ·
                    rfl

theorem cell22_3243257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_3243257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243257 prefixEnd_3243257 := by exact prefixLift 3243257
  have htrace : WordTrace (prefixWord ++ tailWord_3243257) baseStart_3243257 baseEnd_3243257 := by
    simpa [prefixWord, tailWord_3243257, baseEnd_3243257] using wordTrace_append hprefix tailTrace_3243257
  have hstable : (prefixWord ++ tailWord_3243257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243257).length < 2 ^ (prefixWord ++ tailWord_3243257).sum := by decide
  have hdescent : baseEnd_3243257 < baseStart_3243257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243287 : List Nat := [1, 1, 3, 4, 1, 1, 1, 5, 1, 4]
def baseStart_3243287 : Nat := 118140960795 + 3243287 * 2 ^ 59
def prefixEnd_3243287 : Nat := 4983230072969 + 3 ^ 40 * 3243287 * 2
def baseEnd_3243287 : Nat := 1110243420985838238931267

theorem tailTrace_3243287 : CollatzResearch.WordTrace tailWord_3243287 prefixEnd_3243287 1110243420985838238931267 := by
  unfold tailWord_3243287
  simp only [CollatzResearch.WordTrace]
  refine ⟨118292395001132583165736115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78861596667421722110490743 118292395001132583165736115)
  ·
    refine ⟨177438592501698874748604173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118292395001132583165736115 177438592501698874748604173)
    ·
      refine ⟨66539472188137078030726565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177438592501698874748604173 66539472188137078030726565)
      ·
        refine ⟨12476151035275702130761231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66539472188137078030726565 12476151035275702130761231)
        ·
          refine ⟨18714226552913553196141847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476151035275702130761231 18714226552913553196141847)
          ·
            refine ⟨28071339829370329794212771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18714226552913553196141847 28071339829370329794212771)
            ·
              refine ⟨42107009744055494691319157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28071339829370329794212771 42107009744055494691319157)
              ·
                refine ⟨3947532163505202627311171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42107009744055494691319157 3947532163505202627311171)
                ·
                  refine ⟨5921298245257803940966757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947532163505202627311171 5921298245257803940966757)
                  ·
                    refine ⟨1110243420985838238931267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921298245257803940966757 1110243420985838238931267)
                    ·
                      rfl

theorem cell22_3243287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_3243287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243287 prefixEnd_3243287 := by exact prefixLift 3243287
  have htrace : WordTrace (prefixWord ++ tailWord_3243287) baseStart_3243287 baseEnd_3243287 := by
    simpa [prefixWord, tailWord_3243287, baseEnd_3243287] using wordTrace_append hprefix tailTrace_3243287
  have hstable : (prefixWord ++ tailWord_3243287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243287).length < 2 ^ (prefixWord ++ tailWord_3243287).sum := by decide
  have hdescent : baseEnd_3243287 < baseStart_3243287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243321 : List Nat := [1, 2, 1, 6, 2, 2, 1, 2, 1, 4]
def baseStart_3243321 : Nat := 118140960795 + 3243321 * 2 ^ 59
def prefixEnd_3243321 : Nat := 4983230072969 + 3 ^ 40 * 3243321 * 2
def baseEnd_3243321 : Nat := 1110255059880673483581163

theorem tailTrace_3243321 : CollatzResearch.WordTrace tailWord_3243321 prefixEnd_3243321 1110255059880673483581163 := by
  unfold tailWord_3243321
  simp only [CollatzResearch.WordTrace]
  refine ⟨118293635083009406972473817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78862423388672937981649211 118293635083009406972473817)
  ·
    refine ⟨88720226312257055229355363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118293635083009406972473817 88720226312257055229355363)
    ·
      refine ⟨133080339468385582844033045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88720226312257055229355363 133080339468385582844033045)
      ·
        refine ⟨6238140912580574195814049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133080339468385582844033045 6238140912580574195814049)
        ·
          refine ⟨4678605684435430646860537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6238140912580574195814049 4678605684435430646860537)
          ·
            refine ⟨3508954263326572985145403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4678605684435430646860537 3508954263326572985145403)
            ·
              refine ⟨5263431394989859477718105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3508954263326572985145403 5263431394989859477718105)
              ·
                refine ⟨3947573546242394608288579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5263431394989859477718105 3947573546242394608288579)
                ·
                  refine ⟨5921360319363591912432869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3947573546242394608288579 5921360319363591912432869)
                  ·
                    refine ⟨1110255059880673483581163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921360319363591912432869 1110255059880673483581163)
                    ·
                      rfl

theorem cell22_3243321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_3243321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243321 prefixEnd_3243321 := by exact prefixLift 3243321
  have htrace : WordTrace (prefixWord ++ tailWord_3243321) baseStart_3243321 baseEnd_3243321 := by
    simpa [prefixWord, tailWord_3243321, baseEnd_3243321] using wordTrace_append hprefix tailTrace_3243321
  have hstable : (prefixWord ++ tailWord_3243321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243321).length < 2 ^ (prefixWord ++ tailWord_3243321).sum := by decide
  have hdescent : baseEnd_3243321 < baseStart_3243321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243396 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 1, 3]
def baseStart_3243396 : Nat := 118140960795 + 3243396 * 2 ^ 59
def prefixEnd_3243396 : Nat := 4983230072969 + 3 ^ 40 * 3243396 * 2
def baseEnd_3243396 : Nat := 1110280733913398287955933

theorem tailTrace_3243396 : CollatzResearch.WordTrace tailWord_3243396 prefixEnd_3243396 1110280733913398287955933 := by
  unfold tailWord_3243396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59148185278868847390727021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78864247038491796520969361 59148185278868847390727021)
  ·
    refine ⟨22180569479575817771522633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59148185278868847390727021 22180569479575817771522633)
    ·
      refine ⟨16635427109681863328641975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22180569479575817771522633 16635427109681863328641975)
      ·
        refine ⟨24953140664522794992962963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16635427109681863328641975 24953140664522794992962963)
        ·
          refine ⟨37429710996784192489444445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24953140664522794992962963 37429710996784192489444445)
          ·
            refine ⟨14036141623794072183541667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37429710996784192489444445 14036141623794072183541667)
            ·
              refine ⟨21054212435691108275312501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14036141623794072183541667 21054212435691108275312501)
              ·
                refine ⟨1973832415846041400810547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21054212435691108275312501 1973832415846041400810547)
                ·
                  refine ⟨2960748623769062101215821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1973832415846041400810547 2960748623769062101215821)
                  ·
                    refine ⟨1110280733913398287955933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960748623769062101215821 1110280733913398287955933)
                    ·
                      rfl

theorem cell22_3243396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_3243396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243396 prefixEnd_3243396 := by exact prefixLift 3243396
  have htrace : WordTrace (prefixWord ++ tailWord_3243396) baseStart_3243396 baseEnd_3243396 := by
    simpa [prefixWord, tailWord_3243396, baseEnd_3243396] using wordTrace_append hprefix tailTrace_3243396
  have hstable : (prefixWord ++ tailWord_3243396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243396).length < 2 ^ (prefixWord ++ tailWord_3243396).sum := by decide
  have hdescent : baseEnd_3243396 < baseStart_3243396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243426 : List Nat := [3, 3, 1, 2, 1, 3, 3, 1, 5]
def baseStart_3243426 : Nat := 118140960795 + 3243426 * 2 ^ 59
def prefixEnd_3243426 : Nat := 4983230072969 + 3 ^ 40 * 3243426 * 2
def baseEnd_3243426 : Nat := 370097001175496069901947

theorem tailTrace_3243426 : CollatzResearch.WordTrace tailWord_3243426 prefixEnd_3243426 370097001175496069901947 := by
  unfold tailWord_3243426
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574366186907252476261533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78864976498419339936697421 29574366186907252476261533)
  ·
    refine ⟨11090387320090219678598075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29574366186907252476261533 11090387320090219678598075)
    ·
      refine ⟨16635580980135329517897113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11090387320090219678598075 16635580980135329517897113)
      ·
        refine ⟨12476685735101497138422835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16635580980135329517897113 12476685735101497138422835)
        ·
          refine ⟨18715028602652245707634253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12476685735101497138422835 18715028602652245707634253)
          ·
            refine ⟨7018135725994592140362845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18715028602652245707634253 7018135725994592140362845)
            ·
              refine ⟨2631800897247972052636067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7018135725994592140362845 2631800897247972052636067)
              ·
                refine ⟨3947701345871958078954101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631800897247972052636067 3947701345871958078954101)
                ·
                  refine ⟨370097001175496069901947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3947701345871958078954101 370097001175496069901947)
                  ·
                    rfl

theorem cell22_3243426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_3243426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243426 prefixEnd_3243426 := by exact prefixLift 3243426
  have htrace : WordTrace (prefixWord ++ tailWord_3243426) baseStart_3243426 baseEnd_3243426 := by
    simpa [prefixWord, tailWord_3243426, baseEnd_3243426] using wordTrace_append hprefix tailTrace_3243426
  have hstable : (prefixWord ++ tailWord_3243426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243426).length < 2 ^ (prefixWord ++ tailWord_3243426).sum := by decide
  have hdescent : baseEnd_3243426 < baseStart_3243426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243467 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 4, 4]
def baseStart_3243467 : Nat := 118140960795 + 3243467 * 2 ^ 59
def prefixEnd_3243467 : Nat := 4983230072969 + 3 ^ 40 * 3243467 * 2
def baseEnd_3243467 : Nat := 1110305038664377769430715

theorem tailTrace_3243467 : CollatzResearch.WordTrace tailWord_3243467 prefixEnd_3243467 1110305038664377769430715 := by
  unfold tailWord_3243467
  simp only [CollatzResearch.WordTrace]
  refine ⟨118298960140480473907288655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78865973426986982604859103 118298960140480473907288655)
  ·
    refine ⟨177448440210720710860932983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118298960140480473907288655 177448440210720710860932983)
    ·
      refine ⟨266172660316081066291399475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177448440210720710860932983 266172660316081066291399475)
      ·
        refine ⟨399258990474121599437099213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266172660316081066291399475 399258990474121599437099213)
        ·
          refine ⟨149722121427795599788912205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399258990474121599437099213 149722121427795599788912205)
          ·
            refine ⟨56145795535423349920842077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149722121427795599788912205 56145795535423349920842077)
            ·
              refine ⟨21054673325783756220315779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56145795535423349920842077 21054673325783756220315779)
              ·
                refine ⟨31582009988675634330473669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21054673325783756220315779 31582009988675634330473669)
                ·
                  refine ⟨5921626872876681436963813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31582009988675634330473669 5921626872876681436963813)
                  ·
                    refine ⟨1110305038664377769430715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5921626872876681436963813 1110305038664377769430715)
                    ·
                      rfl

theorem cell22_3243467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 4].length) (baseStart_3243467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243467 prefixEnd_3243467 := by exact prefixLift 3243467
  have htrace : WordTrace (prefixWord ++ tailWord_3243467) baseStart_3243467 baseEnd_3243467 := by
    simpa [prefixWord, tailWord_3243467, baseEnd_3243467] using wordTrace_append hprefix tailTrace_3243467
  have hstable : (prefixWord ++ tailWord_3243467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243467).length < 2 ^ (prefixWord ++ tailWord_3243467).sum := by decide
  have hdescent : baseEnd_3243467 < baseStart_3243467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243482 : List Nat := [3, 1, 1, 2, 3, 2, 1, 9]
def baseStart_3243482 : Nat := 118140960795 + 3243482 * 2 ^ 59
def prefixEnd_3243482 : Nat := 4983230072969 + 3 ^ 40 * 3243482 * 2
def baseEnd_3243482 : Nat := 123367797052324747811741

theorem tailTrace_3243482 : CollatzResearch.WordTrace tailWord_3243482 prefixEnd_3243482 123367797052324747811741 := by
  unfold tailWord_3243482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29574876808856532867271175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78866338156950754312723133 29574876808856532867271175)
  ·
    refine ⟨44362315213284799300906763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29574876808856532867271175 44362315213284799300906763)
    ·
      refine ⟨66543472819927198951360145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44362315213284799300906763 66543472819927198951360145)
      ·
        refine ⟨49907604614945399213520109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66543472819927198951360145 49907604614945399213520109)
        ·
          refine ⟨18715351730604524705070041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49907604614945399213520109 18715351730604524705070041)
          ·
            refine ⟨14036513797953393528802531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18715351730604524705070041 14036513797953393528802531)
            ·
              refine ⟨21054770696930090293203797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14036513797953393528802531 21054770696930090293203797)
              ·
                refine ⟨123367797052324747811741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21054770696930090293203797 123367797052324747811741)
                ·
                  rfl

theorem cell22_3243482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 9].length) (baseStart_3243482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243482 prefixEnd_3243482 := by exact prefixLift 3243482
  have htrace : WordTrace (prefixWord ++ tailWord_3243482) baseStart_3243482 baseEnd_3243482 := by
    simpa [prefixWord, tailWord_3243482, baseEnd_3243482] using wordTrace_append hprefix tailTrace_3243482
  have hstable : (prefixWord ++ tailWord_3243482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243482).length < 2 ^ (prefixWord ++ tailWord_3243482).sum := by decide
  have hdescent : baseEnd_3243482 < baseStart_3243482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243587 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 2, 9]
def baseStart_3243587 : Nat := 118140960795 + 3243587 * 2 ^ 59
def prefixEnd_3243587 : Nat := 4983230072969 + 3 ^ 40 * 3243587 * 2
def baseEnd_3243587 : Nat := 1110346117116737456430347

theorem tailTrace_3243587 : CollatzResearch.WordTrace tailWord_3243587 prefixEnd_3243587 1110346117116737456430347 := by
  unfold tailWord_3243587
  simp only [CollatzResearch.WordTrace]
  refine ⟨118303336900045734401657015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78868891266697156267771343 118303336900045734401657015)
  ·
    refine ⟨177455005350068601602485523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118303336900045734401657015 177455005350068601602485523)
    ·
      refine ⟨266182508025102902403728285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177455005350068601602485523 266182508025102902403728285)
      ·
        refine ⟨99818440509413588401398107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266182508025102902403728285 99818440509413588401398107)
        ·
          refine ⟨149727660764120382602097161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99818440509413588401398107 149727660764120382602097161)
          ·
            refine ⟨112295745573090286951572871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149727660764120382602097161 112295745573090286951572871)
            ·
              refine ⟨168443618359635430427359307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112295745573090286951572871 168443618359635430427359307)
              ·
                refine ⟨252665427539453145641038961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168443618359635430427359307 252665427539453145641038961)
                ·
                  refine ⟨189499070654589859230779221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252665427539453145641038961 189499070654589859230779221)
                  ·
                    refine ⟨1110346117116737456430347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 189499070654589859230779221 1110346117116737456430347)
                    ·
                      rfl

theorem cell22_3243587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 9].length) (baseStart_3243587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243587 prefixEnd_3243587 := by exact prefixLift 3243587
  have htrace : WordTrace (prefixWord ++ tailWord_3243587) baseStart_3243587 baseEnd_3243587 := by
    simpa [prefixWord, tailWord_3243587, baseEnd_3243587] using wordTrace_append hprefix tailTrace_3243587
  have hstable : (prefixWord ++ tailWord_3243587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243587).length < 2 ^ (prefixWord ++ tailWord_3243587).sum := by decide
  have hdescent : baseEnd_3243587 < baseStart_3243587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243589 : List Nat := [1, 3, 1, 1, 1, 4, 4, 1, 6]
def baseStart_3243589 : Nat := 118140960795 + 3243589 * 2 ^ 59
def prefixEnd_3243589 : Nat := 4983230072969 + 3 ^ 40 * 3243589 * 2
def baseEnd_3243589 : Nat := 370115600585870039293447

theorem tailTrace_3243589 : CollatzResearch.WordTrace tailWord_3243589 prefixEnd_3243589 370115600585870039293447 := by
  unfold tailWord_3243589
  simp only [CollatzResearch.WordTrace]
  refine ⟨118303409846038488743229821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78868939897358992495486547 118303409846038488743229821)
  ·
    refine ⟨44363778692264433278711183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118303409846038488743229821 44363778692264433278711183)
    ·
      refine ⟨66545668038396649918066775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44363778692264433278711183 66545668038396649918066775)
      ·
        refine ⟨99818502057594974877100163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66545668038396649918066775 99818502057594974877100163)
        ·
          refine ⟨149727753086392462315650245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99818502057594974877100163 149727753086392462315650245)
          ·
            refine ⟨28073953703698586684184421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149727753086392462315650245 28073953703698586684184421)
            ·
              refine ⟨5263866319443485003284579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28073953703698586684184421 5263866319443485003284579)
              ·
                refine ⟨7895799479165227504926869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5263866319443485003284579 7895799479165227504926869)
                ·
                  refine ⟨370115600585870039293447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7895799479165227504926869 370115600585870039293447)
                  ·
                    rfl

theorem cell22_3243589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 1, 6].length) (baseStart_3243589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243589 prefixEnd_3243589 := by exact prefixLift 3243589
  have htrace : WordTrace (prefixWord ++ tailWord_3243589) baseStart_3243589 baseEnd_3243589 := by
    simpa [prefixWord, tailWord_3243589, baseEnd_3243589] using wordTrace_append hprefix tailTrace_3243589
  have hstable : (prefixWord ++ tailWord_3243589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243589).length < 2 ^ (prefixWord ++ tailWord_3243589).sum := by decide
  have hdescent : baseEnd_3243589 < baseStart_3243589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243619 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 6]
def baseStart_3243619 : Nat := 118140960795 + 3243619 * 2 ^ 59
def prefixEnd_3243619 : Nat := 4983230072969 + 3 ^ 40 * 3243619 * 2
def baseEnd_3243619 : Nat := 1110357071370700039630249

theorem tailTrace_3243619 : CollatzResearch.WordTrace tailWord_3243619 prefixEnd_3243619 1110357071370700039630249 := by
  unfold tailWord_3243619
  simp only [CollatzResearch.WordTrace]
  refine ⟨118304504035929803866821911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78869669357286535911214607 118304504035929803866821911)
  ·
    refine ⟨177456756053894705800232867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118304504035929803866821911 177456756053894705800232867)
    ·
      refine ⟨266185134080842058700349301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177456756053894705800232867 266185134080842058700349301)
      ·
        refine ⟨24954856320078943003157747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266185134080842058700349301 24954856320078943003157747)
        ·
          refine ⟨37432284480118414504736621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24954856320078943003157747 37432284480118414504736621)
          ·
            refine ⟨14037106680044405439276233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37432284480118414504736621 14037106680044405439276233)
            ·
              refine ⟨10527830010033304079457175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14037106680044405439276233 10527830010033304079457175)
              ·
                refine ⟨15791745015049956119185763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527830010033304079457175 15791745015049956119185763)
                ·
                  refine ⟨23687617522574934178778645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15791745015049956119185763 23687617522574934178778645)
                  ·
                    refine ⟨1110357071370700039630249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23687617522574934178778645 1110357071370700039630249)
                    ·
                      rfl

theorem cell22_3243619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 6].length) (baseStart_3243619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243619 prefixEnd_3243619 := by exact prefixLift 3243619
  have htrace : WordTrace (prefixWord ++ tailWord_3243619) baseStart_3243619 baseEnd_3243619 := by
    simpa [prefixWord, tailWord_3243619, baseEnd_3243619] using wordTrace_append hprefix tailTrace_3243619
  have hstable : (prefixWord ++ tailWord_3243619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243619).length < 2 ^ (prefixWord ++ tailWord_3243619).sum := by decide
  have hdescent : baseEnd_3243619 < baseStart_3243619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243621 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 4, 3]
def baseStart_3243621 : Nat := 118140960795 + 3243621 * 2 ^ 59
def prefixEnd_3243621 : Nat := 4983230072969 + 3 ^ 40 * 3243621 * 2
def baseEnd_3243621 : Nat := 1110357756011572701080243

theorem tailTrace_3243621 : CollatzResearch.WordTrace tailWord_3243621 prefixEnd_3243621 1110357756011572701080243 := by
  unfold tailWord_3243621
  simp only [CollatzResearch.WordTrace]
  refine ⟨118304576981922558208394717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78869717987948372138929811 118304576981922558208394717)
  ·
    refine ⟨44364216368220959328148019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118304576981922558208394717 44364216368220959328148019)
    ·
      refine ⟨66546324552331438992222029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44364216368220959328148019 66546324552331438992222029)
      ·
        refine ⟨24954871707124289622083261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66546324552331438992222029 24954871707124289622083261)
        ·
          refine ⟨9358076890171608608281223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24954871707124289622083261 9358076890171608608281223)
          ·
            refine ⟨14037115335257412912421835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358076890171608608281223 14037115335257412912421835)
            ·
              refine ⟨21055673002886119368632753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14037115335257412912421835 21055673002886119368632753)
              ·
                refine ⟨15791754752164589526474565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21055673002886119368632753 15791754752164589526474565)
                ·
                  refine ⟨2960954016030860536213981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15791754752164589526474565 2960954016030860536213981)
                  ·
                    refine ⟨1110357756011572701080243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960954016030860536213981 1110357756011572701080243)
                    ·
                      rfl

theorem cell22_3243621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_3243621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243621 prefixEnd_3243621 := by exact prefixLift 3243621
  have htrace : WordTrace (prefixWord ++ tailWord_3243621) baseStart_3243621 baseEnd_3243621 := by
    simpa [prefixWord, tailWord_3243621, baseEnd_3243621] using wordTrace_append hprefix tailTrace_3243621
  have hstable : (prefixWord ++ tailWord_3243621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243621).length < 2 ^ (prefixWord ++ tailWord_3243621).sum := by decide
  have hdescent : baseEnd_3243621 < baseStart_3243621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243634 : List Nat := [3, 2, 1, 2, 3, 1, 10]
def baseStart_3243634 : Nat := 118140960795 + 3243634 * 2 ^ 59
def prefixEnd_3243634 : Nat := 4983230072969 + 3 ^ 40 * 3243634 * 2
def baseEnd_3243634 : Nat := 41124526154712777796489

theorem tailTrace_3243634 : CollatzResearch.WordTrace tailWord_3243634 prefixEnd_3243634 41124526154712777796489 := by
  unfold tailWord_3243634
  simp only [CollatzResearch.WordTrace]
  refine ⟨29576262782718865357154489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78870034087250307619078637 29576262782718865357154489)
  ·
    refine ⟨22182197087039149017865867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29576262782718865357154489 22182197087039149017865867)
    ·
      refine ⟨33273295630558723526798801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22182197087039149017865867 33273295630558723526798801)
      ·
        refine ⟨24954971722919042645099101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33273295630558723526798801 24954971722919042645099101)
        ·
          refine ⟨9358114396094640991912163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24954971722919042645099101 9358114396094640991912163)
          ·
            refine ⟨14037171594141961487868245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358114396094640991912163 14037171594141961487868245)
            ·
              refine ⟨41124526154712777796489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14037171594141961487868245 41124526154712777796489)
              ·
                rfl

theorem cell22_3243634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 10].length) (baseStart_3243634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243634 prefixEnd_3243634 := by exact prefixLift 3243634
  have htrace : WordTrace (prefixWord ++ tailWord_3243634) baseStart_3243634 baseEnd_3243634 := by
    simpa [prefixWord, tailWord_3243634, baseEnd_3243634] using wordTrace_append hprefix tailTrace_3243634
  have hstable : (prefixWord ++ tailWord_3243634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243634).length < 2 ^ (prefixWord ++ tailWord_3243634).sum := by decide
  have hdescent : baseEnd_3243634 < baseStart_3243634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243638 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_3243638 : Nat := 118140960795 + 3243638 * 2 ^ 59
def prefixEnd_3243638 : Nat := 4983230072969 + 3 ^ 40 * 3243638 * 2
def baseEnd_3243638 : Nat := 1110363575458990323405191

theorem tailTrace_3243638 : CollatzResearch.WordTrace tailWord_3243638 prefixEnd_3243638 1110363575458990323405191 := by
  unfold tailWord_3243638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7394074813928810631985223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78870131348573980074509045 7394074813928810631985223)
  ·
    refine ⟨11091112220893215947977835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7394074813928810631985223 11091112220893215947977835)
    ·
      refine ⟨16636668331339823921966753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11091112220893215947977835 16636668331339823921966753)
      ·
        refine ⟨12477501248504867941475065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16636668331339823921966753 12477501248504867941475065)
        ·
          refine ⟨9358125936378650956106299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12477501248504867941475065 9358125936378650956106299)
          ·
            refine ⟨14037188904567976434159449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9358125936378650956106299 14037188904567976434159449)
            ·
              refine ⟨10527891678425982325619587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14037188904567976434159449 10527891678425982325619587)
              ·
                refine ⟨15791837517638973488429381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10527891678425982325619587 15791837517638973488429381)
                ·
                  refine ⟨2960969534557307529080509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15791837517638973488429381 2960969534557307529080509)
                  ·
                    refine ⟨1110363575458990323405191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960969534557307529080509 1110363575458990323405191)
                    ·
                      rfl

theorem cell22_3243638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_3243638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243638 prefixEnd_3243638 := by exact prefixLift 3243638
  have htrace : WordTrace (prefixWord ++ tailWord_3243638) baseStart_3243638 baseEnd_3243638 := by
    simpa [prefixWord, tailWord_3243638, baseEnd_3243638] using wordTrace_append hprefix tailTrace_3243638
  have hstable : (prefixWord ++ tailWord_3243638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243638).length < 2 ^ (prefixWord ++ tailWord_3243638).sum := by decide
  have hdescent : baseEnd_3243638 < baseStart_3243638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243655 : List Nat := [1, 1, 4, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3243655 : Nat := 118140960795 + 3243655 * 2 ^ 59
def prefixEnd_3243655 : Nat := 4983230072969 + 3 ^ 40 * 3243655 * 2
def baseEnd_3243655 : Nat := 1110369394906407945730139

theorem tailTrace_3243655 : CollatzResearch.WordTrace tailWord_3243655 prefixEnd_3243655 1110369394906407945730139 := by
  unfold tailWord_3243655
  simp only [CollatzResearch.WordTrace]
  refine ⟨118305817063799382015132419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78870544709199588010088279 118305817063799382015132419)
  ·
    refine ⟨177458725595699073022698629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118305817063799382015132419 177458725595699073022698629)
    ·
      refine ⟨33273511049193576191755993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177458725595699073022698629 33273511049193576191755993)
      ·
        refine ⟨24955133286895182143816995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33273511049193576191755993 24955133286895182143816995)
        ·
          refine ⟨37432699930342773215725493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24955133286895182143816995 37432699930342773215725493)
          ·
            refine ⟨3509315618469634988974265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37432699930342773215725493 3509315618469634988974265)
            ·
              refine ⟨2631986713852226241730699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3509315618469634988974265 2631986713852226241730699)
              ·
                refine ⟨3947980070778339362596049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2631986713852226241730699 3947980070778339362596049)
                ·
                  refine ⟨2960985053083754521947037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3947980070778339362596049 2960985053083754521947037)
                  ·
                    refine ⟨1110369394906407945730139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2960985053083754521947037 1110369394906407945730139)
                    ·
                      rfl

theorem cell22_3243655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3243655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243655 prefixEnd_3243655 := by exact prefixLift 3243655
  have htrace : WordTrace (prefixWord ++ tailWord_3243655) baseStart_3243655 baseEnd_3243655 := by
    simpa [prefixWord, tailWord_3243655, baseEnd_3243655] using wordTrace_append hprefix tailTrace_3243655
  have hstable : (prefixWord ++ tailWord_3243655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243655).length < 2 ^ (prefixWord ++ tailWord_3243655).sum := by decide
  have hdescent : baseEnd_3243655 < baseStart_3243655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243683 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 1, 3]
def baseStart_3243683 : Nat := 118140960795 + 3243683 * 2 ^ 59
def prefixEnd_3243683 : Nat := 4983230072969 + 3 ^ 40 * 3243683 * 2
def baseEnd_3243683 : Nat := 1110378979878625206030053

theorem tailTrace_3243683 : CollatzResearch.WordTrace tailWord_3243683 prefixEnd_3243683 1110378979878625206030053 := by
  unfold tailWord_3243683
  simp only [CollatzResearch.WordTrace]
  refine ⟨118306838307697942797151703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78871225538465295198101135 118306838307697942797151703)
  ·
    refine ⟨177460257461546914195727555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118306838307697942797151703 177460257461546914195727555)
    ·
      refine ⟨266190386192320371293591333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177460257461546914195727555 266190386192320371293591333)
      ·
        refine ⟨49910697411060069617548375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266190386192320371293591333 49910697411060069617548375)
        ·
          refine ⟨74866046116590104426322563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49910697411060069617548375 74866046116590104426322563)
          ·
            refine ⟨112299069174885156639483845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74866046116590104426322563 112299069174885156639483845)
            ·
              refine ⟨21056075470290966869903221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112299069174885156639483845 21056075470290966869903221)
              ·
                refine ⟨1974007075339778144053427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21056075470290966869903221 1974007075339778144053427)
                ·
                  refine ⟨2961010613009667216080141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974007075339778144053427 2961010613009667216080141)
                  ·
                    refine ⟨1110378979878625206030053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961010613009667216080141 1110378979878625206030053)
                    ·
                      rfl

theorem cell22_3243683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 3].length) (baseStart_3243683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243683 prefixEnd_3243683 := by exact prefixLift 3243683
  have htrace : WordTrace (prefixWord ++ tailWord_3243683) baseStart_3243683 baseEnd_3243683 := by
    simpa [prefixWord, tailWord_3243683, baseEnd_3243683] using wordTrace_append hprefix tailTrace_3243683
  have hstable : (prefixWord ++ tailWord_3243683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243683).length < 2 ^ (prefixWord ++ tailWord_3243683).sum := by decide
  have hdescent : baseEnd_3243683 < baseStart_3243683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243726 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3243726 : Nat := 118140960795 + 3243726 * 2 ^ 59
def prefixEnd_3243726 : Nat := 4983230072969 + 3 ^ 40 * 3243726 * 2
def baseEnd_3243726 : Nat := 1110393699657387427204921

theorem tailTrace_3243726 : CollatzResearch.WordTrace tailWord_3243726 prefixEnd_3243726 1110393699657387427204921 := by
  unfold tailWord_3243726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788550830817770142620879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78872271097694774093978021 14788550830817770142620879)
  ·
    refine ⟨22182826246226655213931319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788550830817770142620879 22182826246226655213931319)
    ·
      refine ⟨33274239369339982820896979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22182826246226655213931319 33274239369339982820896979)
      ·
        refine ⟨49911359054009974231345469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33274239369339982820896979 49911359054009974231345469)
        ·
          refine ⟨18716759645253740336754551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49911359054009974231345469 18716759645253740336754551)
          ·
            refine ⟨28075139467880610505131827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18716759645253740336754551 28075139467880610505131827)
            ·
              refine ⟨42112709201820915757697741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28075139467880610505131827 42112709201820915757697741)
              ·
                refine ⟨15792265950682843409136653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42112709201820915757697741 15792265950682843409136653)
                ·
                  refine ⟨5922099731506066278426245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15792265950682843409136653 5922099731506066278426245)
                  ·
                    refine ⟨1110393699657387427204921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5922099731506066278426245 1110393699657387427204921)
                    ·
                      rfl

theorem cell22_3243726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3243726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243726 prefixEnd_3243726 := by exact prefixLift 3243726
  have htrace : WordTrace (prefixWord ++ tailWord_3243726) baseStart_3243726 baseEnd_3243726 := by
    simpa [prefixWord, tailWord_3243726, baseEnd_3243726] using wordTrace_append hprefix tailTrace_3243726
  have hstable : (prefixWord ++ tailWord_3243726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243726).length < 2 ^ (prefixWord ++ tailWord_3243726).sum := by decide
  have hdescent : baseEnd_3243726 < baseStart_3243726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243758 : List Nat := [4, 1, 2, 1, 1, 2, 1, 6, 4]
def baseStart_3243758 : Nat := 118140960795 + 3243758 * 2 ^ 59
def prefixEnd_3243758 : Nat := 4983230072969 + 3 ^ 40 * 3243758 * 2
def baseEnd_3243758 : Nat := 370134884637116670134941

theorem tailTrace_3243758 : CollatzResearch.WordTrace tailWord_3243758 prefixEnd_3243758 370134884637116670134941 := by
  unfold tailWord_3243758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788696722803278825766491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78873049188284153737421285 14788696722803278825766491)
  ·
    refine ⟨22183045084204918238649737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788696722803278825766491 22183045084204918238649737)
    ·
      refine ⟨16637283813153688678987303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22183045084204918238649737 16637283813153688678987303)
      ·
        refine ⟨24955925719730533018480955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16637283813153688678987303 24955925719730533018480955)
        ·
          refine ⟨37433888579595799527721433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24955925719730533018480955 37433888579595799527721433)
          ·
            refine ⟨28075416434696849645791075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37433888579595799527721433 28075416434696849645791075)
            ·
              refine ⟨42113124652045274468686613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28075416434696849645791075 42113124652045274468686613)
              ·
                refine ⟨1974052718064622240719685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42113124652045274468686613 1974052718064622240719685)
                ·
                  refine ⟨370134884637116670134941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974052718064622240719685 370134884637116670134941)
                  ·
                    rfl

theorem cell22_3243758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_3243758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243758 prefixEnd_3243758 := by exact prefixLift 3243758
  have htrace : WordTrace (prefixWord ++ tailWord_3243758) baseStart_3243758 baseEnd_3243758 := by
    simpa [prefixWord, tailWord_3243758, baseEnd_3243758] using wordTrace_append hprefix tailTrace_3243758
  have hstable : (prefixWord ++ tailWord_3243758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243758).length < 2 ^ (prefixWord ++ tailWord_3243758).sum := by decide
  have hdescent : baseEnd_3243758 < baseStart_3243758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243786 : List Nat := [3, 1, 2, 2, 1, 4, 1, 8]
def baseStart_3243786 : Nat := 118140960795 + 3243786 * 2 ^ 59
def prefixEnd_3243786 : Nat := 4983230072969 + 3 ^ 40 * 3243786 * 2
def baseEnd_3243786 : Nat := 123379359875951918967193

theorem tailTrace_3243786 : CollatzResearch.WordTrace tailWord_3243786 prefixEnd_3243786 123379359875951918967193 := by
  unfold tailWord_3243786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29577648756581197847037803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78873730017549860925434141 29577648756581197847037803)
  ·
    refine ⟨44366473134871796770556705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29577648756581197847037803 44366473134871796770556705)
    ·
      refine ⟨33274854851153847577917529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44366473134871796770556705 33274854851153847577917529)
      ·
        refine ⟨24956141138365385683438147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33274854851153847577917529 24956141138365385683438147)
        ·
          refine ⟨37434211707548078525157221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24956141138365385683438147 37434211707548078525157221)
          ·
            refine ⟨7018914695165264723466979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37434211707548078525157221 7018914695165264723466979)
            ·
              refine ⟨10528372042747897085200469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018914695165264723466979 10528372042747897085200469)
              ·
                refine ⟨123379359875951918967193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10528372042747897085200469 123379359875951918967193)
                ·
                  rfl

theorem cell22_3243786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 8].length) (baseStart_3243786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243786 prefixEnd_3243786 := by exact prefixLift 3243786
  have htrace : WordTrace (prefixWord ++ tailWord_3243786) baseStart_3243786 baseEnd_3243786 := by
    simpa [prefixWord, tailWord_3243786, baseEnd_3243786] using wordTrace_append hprefix tailTrace_3243786
  have hstable : (prefixWord ++ tailWord_3243786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243786).length < 2 ^ (prefixWord ++ tailWord_3243786).sum := by decide
  have hdescent : baseEnd_3243786 < baseStart_3243786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243893 : List Nat := [1, 3, 4, 1, 1, 1, 3, 2, 6]
def baseStart_3243893 : Nat := 118140960795 + 3243893 * 2 ^ 59
def prefixEnd_3243893 : Nat := 4983230072969 + 3 ^ 40 * 3243893 * 2
def baseEnd_3243893 : Nat := 370150289056751552759803

theorem tailTrace_3243893 : CollatzResearch.WordTrace tailWord_3243893 prefixEnd_3243893 370150289056751552759803 := by
  unfold tailWord_3243893
  simp only [CollatzResearch.WordTrace]
  refine ⟨118314497636937148662296333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78876331757958099108197555 118314497636937148662296333)
  ·
    refine ⟨44367936613851430748361125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118314497636937148662296333 44367936613851430748361125)
    ·
      refine ⟨8318988115097143265317711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44367936613851430748361125 8318988115097143265317711)
      ·
        refine ⟨12478482172645714897976567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8318988115097143265317711 12478482172645714897976567)
        ·
          refine ⟨18717723258968572346964851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12478482172645714897976567 18717723258968572346964851)
          ·
            refine ⟨28076584888452858520447277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18717723258968572346964851 28076584888452858520447277)
            ·
              refine ⟨10528719333169821945167729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28076584888452858520447277 10528719333169821945167729)
              ·
                refine ⟨7896539499877366458875797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10528719333169821945167729 7896539499877366458875797)
                ·
                  refine ⟨370150289056751552759803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7896539499877366458875797 370150289056751552759803)
                  ·
                    rfl

theorem cell22_3243893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_3243893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243893 prefixEnd_3243893 := by exact prefixLift 3243893
  have htrace : WordTrace (prefixWord ++ tailWord_3243893) baseStart_3243893 baseEnd_3243893 := by
    simpa [prefixWord, tailWord_3243893, baseEnd_3243893] using wordTrace_append hprefix tailTrace_3243893
  have hstable : (prefixWord ++ tailWord_3243893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243893).length < 2 ^ (prefixWord ++ tailWord_3243893).sum := by decide
  have hdescent : baseEnd_3243893 < baseStart_3243893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243908 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 1, 5]
def baseStart_3243908 : Nat := 118140960795 + 3243908 * 2 ^ 59
def prefixEnd_3243908 : Nat := 4983230072969 + 3 ^ 40 * 3243908 * 2
def baseEnd_3243908 : Nat := 1110456001976799619154363

theorem tailTrace_3243908 : CollatzResearch.WordTrace tailWord_3243908 prefixEnd_3243908 1110456001976799619154363 := by
  unfold tailWord_3243908
  simp only [CollatzResearch.WordTrace]
  refine ⟨59157522365941403112046189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78876696487921870816061585 59157522365941403112046189)
  ·
    refine ⟨22184070887228026167017321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59157522365941403112046189 22184070887228026167017321)
    ·
      refine ⟨16638053165421019625262991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22184070887228026167017321 16638053165421019625262991)
      ·
        refine ⟨24957079748131529437894487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16638053165421019625262991 24957079748131529437894487)
        ·
          refine ⟨37435619622197294156841731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24957079748131529437894487 37435619622197294156841731)
          ·
            refine ⟨56153429433295941235262597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37435619622197294156841731 56153429433295941235262597)
            ·
              refine ⟨10528768018742988981611737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56153429433295941235262597 10528768018742988981611737)
              ·
                refine ⟨7896576014057241736208803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10528768018742988981611737 7896576014057241736208803)
                ·
                  refine ⟨11844864021085862604313205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7896576014057241736208803 11844864021085862604313205)
                  ·
                    refine ⟨1110456001976799619154363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11844864021085862604313205 1110456001976799619154363)
                    ·
                      rfl

theorem cell22_3243908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_3243908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243908 prefixEnd_3243908 := by exact prefixLift 3243908
  have htrace : WordTrace (prefixWord ++ tailWord_3243908) baseStart_3243908 baseEnd_3243908 := by
    simpa [prefixWord, tailWord_3243908, baseEnd_3243908] using wordTrace_append hprefix tailTrace_3243908
  have hstable : (prefixWord ++ tailWord_3243908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243908).length < 2 ^ (prefixWord ++ tailWord_3243908).sum := by decide
  have hdescent : baseEnd_3243908 < baseStart_3243908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3243983 : List Nat := [1, 1, 2, 1, 1, 5, 2, 4, 5]
def baseStart_3243983 : Nat := 118140960795 + 3243983 * 2 ^ 59
def prefixEnd_3243983 : Nat := 4983230072969 + 3 ^ 40 * 3243983 * 2
def baseEnd_3243983 : Nat := 370160558669841474509711

theorem tailTrace_3243983 : CollatzResearch.WordTrace tailWord_3243983 prefixEnd_3243983 370160558669841474509711 := by
  unfold tailWord_3243983
  simp only [CollatzResearch.WordTrace]
  refine ⟨118317780206611094033072603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78878520137740729355381735 118317780206611094033072603)
  ·
    refine ⟨177476670309916641049608905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118317780206611094033072603 177476670309916641049608905)
    ·
      refine ⟨133107502732437480787206679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177476670309916641049608905 133107502732437480787206679)
      ·
        refine ⟨199661254098656221180810019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133107502732437480787206679 199661254098656221180810019)
        ·
          refine ⟨299491881147984331771215029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199661254098656221180810019 299491881147984331771215029)
          ·
            refine ⟨28077363857623531103551409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299491881147984331771215029 28077363857623531103551409)
            ·
              refine ⟨21058022893217648327663557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28077363857623531103551409 21058022893217648327663557)
              ·
                refine ⟨3948379292478309061436917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21058022893217648327663557 3948379292478309061436917)
                ·
                  refine ⟨370160558669841474509711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3948379292478309061436917 370160558669841474509711)
                  ·
                    rfl

theorem cell22_3243983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 4, 5].length) (baseStart_3243983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3243983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3243983 prefixEnd_3243983 := by exact prefixLift 3243983
  have htrace : WordTrace (prefixWord ++ tailWord_3243983) baseStart_3243983 baseEnd_3243983 := by
    simpa [prefixWord, tailWord_3243983, baseEnd_3243983] using wordTrace_append hprefix tailTrace_3243983
  have hstable : (prefixWord ++ tailWord_3243983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3243983).length < 2 ^ (prefixWord ++ tailWord_3243983).sum := by decide
  have hdescent : baseEnd_3243983 < baseStart_3243983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3243983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244043 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 3, 5]
def baseStart_3244043 : Nat := 118140960795 + 3244043 * 2 ^ 59
def prefixEnd_3244043 : Nat := 4983230072969 + 3 ^ 40 * 3244043 * 2
def baseEnd_3244043 : Nat := 1110502215235704267028949

theorem tailTrace_3244043 : CollatzResearch.WordTrace tailWord_3244043 prefixEnd_3244043 1110502215235704267028949 := by
  unfold tailWord_3244043
  simp only [CollatzResearch.WordTrace]
  refine ⟨118319968586393724280256783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78879979057595816186837855 118319968586393724280256783)
  ·
    refine ⟨177479952879590586420385175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118319968586393724280256783 177479952879590586420385175)
    ·
      refine ⟨266219929319385879630577763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177479952879590586420385175 266219929319385879630577763)
      ·
        refine ⟨399329893979078819445866645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266219929319385879630577763 399329893979078819445866645)
        ·
          refine ⟨18718588780269319661524999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 399329893979078819445866645 18718588780269319661524999)
          ·
            refine ⟨28077883170403979492287499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18718588780269319661524999 28077883170403979492287499)
            ·
              refine ⟨42116824755605969238431249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28077883170403979492287499 42116824755605969238431249)
              ·
                refine ⟨31587618566704476928823437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42116824755605969238431249 31587618566704476928823437)
                ·
                  refine ⟨11845356962514178848308789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31587618566704476928823437 11845356962514178848308789)
                  ·
                    refine ⟨1110502215235704267028949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11845356962514178848308789 1110502215235704267028949)
                    ·
                      rfl

theorem cell22_3244043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_3244043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244043 prefixEnd_3244043 := by exact prefixLift 3244043
  have htrace : WordTrace (prefixWord ++ tailWord_3244043) baseStart_3244043 baseEnd_3244043 := by
    simpa [prefixWord, tailWord_3244043, baseEnd_3244043] using wordTrace_append hprefix tailTrace_3244043
  have hstable : (prefixWord ++ tailWord_3244043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244043).length < 2 ^ (prefixWord ++ tailWord_3244043).sum := by decide
  have hdescent : baseEnd_3244043 < baseStart_3244043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244060 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3244060 : Nat := 118140960795 + 3244060 * 2 ^ 59
def prefixEnd_3244060 : Nat := 4983230072969 + 3 ^ 40 * 3244060 * 2
def baseEnd_3244060 : Nat := 1110508034683121889353897

theorem tailTrace_3244060 : CollatzResearch.WordTrace tailWord_3244060 prefixEnd_3244060 1110508034683121889353897 := by
  unfold tailWord_3244060
  simp only [CollatzResearch.WordTrace]
  refine ⟨59160294313666068091812817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78880392418221424122417089 59160294313666068091812817)
  ·
    refine ⟨44370220735249551068859613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59160294313666068091812817 44370220735249551068859613)
    ·
      refine ⟨16638832775718581650822355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44370220735249551068859613 16638832775718581650822355)
      ·
        refine ⟨24958249163577872476233533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16638832775718581650822355 24958249163577872476233533)
        ·
          refine ⟨9359343436341702178587575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24958249163577872476233533 9359343436341702178587575)
          ·
            refine ⟨14039015154512553267881363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359343436341702178587575 14039015154512553267881363)
            ·
              refine ⟨21058522731768829901822045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14039015154512553267881363 21058522731768829901822045)
              ·
                refine ⟨7896946024413311213183267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21058522731768829901822045 7896946024413311213183267)
                ·
                  refine ⟨11845419036619966819774901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7896946024413311213183267 11845419036619966819774901)
                  ·
                    refine ⟨1110508034683121889353897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11845419036619966819774901 1110508034683121889353897)
                    ·
                      rfl

theorem cell22_3244060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3244060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244060 prefixEnd_3244060 := by exact prefixLift 3244060
  have htrace : WordTrace (prefixWord ++ tailWord_3244060) baseStart_3244060 baseEnd_3244060 := by
    simpa [prefixWord, tailWord_3244060, baseEnd_3244060] using wordTrace_append hprefix tailTrace_3244060
  have hstable : (prefixWord ++ tailWord_3244060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244060).length < 2 ^ (prefixWord ++ tailWord_3244060).sum := by decide
  have hdescent : baseEnd_3244060 < baseStart_3244060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244094 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3244094 : Nat := 118140960795 + 3244094 * 2 ^ 59
def prefixEnd_3244094 : Nat := 4983230072969 + 3 ^ 40 * 3244094 * 2
def baseEnd_3244094 : Nat := 1110519673577957134003793

theorem tailTrace_3244094 : CollatzResearch.WordTrace tailWord_3244094 prefixEnd_3244094 1110519673577957134003793 := by
  unfold tailWord_3244094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790228588651119998795417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78881219139472639993575557 14790228588651119998795417)
  ·
    refine ⟨11092671441488339999096563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14790228588651119998795417 11092671441488339999096563)
    ·
      refine ⟨16639007162232509998644845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11092671441488339999096563 16639007162232509998644845)
      ·
        refine ⟨6239627685837191249491817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16639007162232509998644845 6239627685837191249491817)
        ·
          refine ⟨4679720764377893437118863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6239627685837191249491817 4679720764377893437118863)
          ·
            refine ⟨7019581146566840155678295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4679720764377893437118863 7019581146566840155678295)
            ·
              refine ⟨10529371719850260233517443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7019581146566840155678295 10529371719850260233517443)
              ·
                refine ⟨15794057579775390350276165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10529371719850260233517443 15794057579775390350276165)
                ·
                  refine ⟨2961385796207885690676781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15794057579775390350276165 2961385796207885690676781)
                  ·
                    refine ⟨1110519673577957134003793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961385796207885690676781 1110519673577957134003793)
                    ·
                      rfl

theorem cell22_3244094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3244094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244094 prefixEnd_3244094 := by exact prefixLift 3244094
  have htrace : WordTrace (prefixWord ++ tailWord_3244094) baseStart_3244094 baseEnd_3244094 := by
    simpa [prefixWord, tailWord_3244094, baseEnd_3244094] using wordTrace_append hprefix tailTrace_3244094
  have hstable : (prefixWord ++ tailWord_3244094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244094).length < 2 ^ (prefixWord ++ tailWord_3244094).sum := by decide
  have hdescent : baseEnd_3244094 < baseStart_3244094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244156 : List Nat := [2, 2, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_3244156 : Nat := 118140960795 + 3244156 * 2 ^ 59
def prefixEnd_3244156 : Nat := 4983230072969 + 3 ^ 40 * 3244156 * 2
def baseEnd_3244156 : Nat := 1110540897445009638953603

theorem tailTrace_3244156 : CollatzResearch.WordTrace tailWord_3244156 prefixEnd_3244156 1110540897445009638953603 := by
  unfold tailWord_3244156
  simp only [CollatzResearch.WordTrace]
  refine ⟨59162045017492172289560161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78882726689989563052746881 59162045017492172289560161)
  ·
    refine ⟨44371533763119129217170121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59162045017492172289560161 44371533763119129217170121)
    ·
      refine ⟨33278650322339346912877591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44371533763119129217170121 33278650322339346912877591)
      ·
        refine ⟨49917975483509020369316387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33278650322339346912877591 49917975483509020369316387)
        ·
          refine ⟨74876963225263530553974581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49917975483509020369316387 74876963225263530553974581)
          ·
            refine ⟨7019715302368455989435117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74876963225263530553974581 7019715302368455989435117)
            ·
              refine ⟨2632393238388170996038169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7019715302368455989435117 2632393238388170996038169)
              ·
                refine ⟨1974294928791128247028627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632393238388170996038169 1974294928791128247028627)
                ·
                  refine ⟨2961442393186692370542941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974294928791128247028627 2961442393186692370542941)
                  ·
                    refine ⟨1110540897445009638953603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961442393186692370542941 1110540897445009638953603)
                    ·
                      rfl

theorem cell22_3244156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_3244156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244156 prefixEnd_3244156 := by exact prefixLift 3244156
  have htrace : WordTrace (prefixWord ++ tailWord_3244156) baseStart_3244156 baseEnd_3244156 := by
    simpa [prefixWord, tailWord_3244156, baseEnd_3244156] using wordTrace_append hprefix tailTrace_3244156
  have hstable : (prefixWord ++ tailWord_3244156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244156).length < 2 ^ (prefixWord ++ tailWord_3244156).sum := by decide
  have hdescent : baseEnd_3244156 < baseStart_3244156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244197 : List Nat := [1, 3, 1, 2, 1, 3, 2, 5, 4]
def baseStart_3244197 : Nat := 118140960795 + 3244197 * 2 ^ 59
def prefixEnd_3244197 : Nat := 4983230072969 + 3 ^ 40 * 3244197 * 2
def baseEnd_3244197 : Nat := 370184977527633066226159

theorem tailTrace_3244197 : CollatzResearch.WordTrace tailWord_3244197 prefixEnd_3244197 370184977527633066226159 := by
  unfold tailWord_3244197
  simp only [CollatzResearch.WordTrace]
  refine ⟨118325585427835808581362845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78883723618557205720908563 118325585427835808581362845)
  ·
    refine ⟨44372094535438428218011067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118325585427835808581362845 44372094535438428218011067)
    ·
      refine ⟨66558141803157642327016601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44372094535438428218011067 66558141803157642327016601)
      ·
        refine ⟨49918606352368231745262451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66558141803157642327016601 49918606352368231745262451)
        ·
          refine ⟨74877909528552347617893677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49918606352368231745262451 74877909528552347617893677)
          ·
            refine ⟨28079216073207130356710129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74877909528552347617893677 28079216073207130356710129)
            ·
              refine ⟨21059412054905347767532597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28079216073207130356710129 21059412054905347767532597)
              ·
                refine ⟨1974319880147376353206181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21059412054905347767532597 1974319880147376353206181)
                ·
                  refine ⟨370184977527633066226159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974319880147376353206181 370184977527633066226159)
                  ·
                    rfl

theorem cell22_3244197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 4].length) (baseStart_3244197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244197 prefixEnd_3244197 := by exact prefixLift 3244197
  have htrace : WordTrace (prefixWord ++ tailWord_3244197) baseStart_3244197 baseEnd_3244197 := by
    simpa [prefixWord, tailWord_3244197, baseEnd_3244197] using wordTrace_append hprefix tailTrace_3244197
  have hstable : (prefixWord ++ tailWord_3244197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244197).length < 2 ^ (prefixWord ++ tailWord_3244197).sum := by decide
  have hdescent : baseEnd_3244197 < baseStart_3244197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244257 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3244257 : Nat := 118140960795 + 3244257 * 2 ^ 59
def prefixEnd_3244257 : Nat := 4983230072969 + 3 ^ 40 * 3244257 * 2
def baseEnd_3244257 : Nat := 1110575471809079042178293

theorem tailTrace_3244257 : CollatzResearch.WordTrace tailWord_3244257 prefixEnd_3244257 1110575471809079042178293 := by
  unfold tailWord_3244257
  simp only [CollatzResearch.WordTrace]
  refine ⟨118327773807618438828547025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78885182538412292552364683 118327773807618438828547025)
  ·
    refine ⟨88745830355713829121410269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118327773807618438828547025 88745830355713829121410269)
    ·
      refine ⟨33279686383392685920528851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88745830355713829121410269 33279686383392685920528851)
      ·
        refine ⟨49919529575089028880793277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33279686383392685920528851 49919529575089028880793277)
        ·
          refine ⟨18719823590658385830297479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49919529575089028880793277 18719823590658385830297479)
          ·
            refine ⟨28079735385987578745446219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18719823590658385830297479 28079735385987578745446219)
            ·
              refine ⟨42119603078981368118169329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28079735385987578745446219 42119603078981368118169329)
              ·
                refine ⟨31589702309236026088626997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42119603078981368118169329 31589702309236026088626997)
                ·
                  refine ⟨2961534591490877445808781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31589702309236026088626997 2961534591490877445808781)
                  ·
                    refine ⟨1110575471809079042178293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961534591490877445808781 1110575471809079042178293)
                    ·
                      rfl

theorem cell22_3244257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3244257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244257 prefixEnd_3244257 := by exact prefixLift 3244257
  have htrace : WordTrace (prefixWord ++ tailWord_3244257) baseStart_3244257 baseEnd_3244257 := by
    simpa [prefixWord, tailWord_3244257, baseEnd_3244257] using wordTrace_append hprefix tailTrace_3244257
  have hstable : (prefixWord ++ tailWord_3244257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244257).length < 2 ^ (prefixWord ++ tailWord_3244257).sum := by decide
  have hdescent : baseEnd_3244257 < baseStart_3244257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244274 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 3, 3]
def baseStart_3244274 : Nat := 118140960795 + 3244274 * 2 ^ 59
def prefixEnd_3244274 : Nat := 4983230072969 + 3 ^ 40 * 3244274 * 2
def baseEnd_3244274 : Nat := 1110581291256496664503241

theorem tailTrace_3244274 : CollatzResearch.WordTrace tailWord_3244274 prefixEnd_3244274 1110581291256496664503241 := by
  unfold tailWord_3244274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582098462139212682978969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78885595899037900487943917 29582098462139212682978969)
  ·
    refine ⟨22186573846604409512234227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29582098462139212682978969 22186573846604409512234227)
    ·
      refine ⟨33279860769906614268351341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22186573846604409512234227 33279860769906614268351341)
      ·
        refine ⟨12479947788714980350631753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33279860769906614268351341 12479947788714980350631753)
        ·
          refine ⟨9359960841536235262973815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12479947788714980350631753 9359960841536235262973815)
          ·
            refine ⟨14039941262304352894460723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9359960841536235262973815 14039941262304352894460723)
            ·
              refine ⟨21059911893456529341691085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14039941262304352894460723 21059911893456529341691085)
              ·
                refine ⟨7897466960046198503134157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21059911893456529341691085 7897466960046198503134157)
                ·
                  refine ⟨2961550110017324438675309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7897466960046198503134157 2961550110017324438675309)
                  ·
                    refine ⟨1110581291256496664503241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961550110017324438675309 1110581291256496664503241)
                    ·
                      rfl

theorem cell22_3244274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_3244274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244274 prefixEnd_3244274 := by exact prefixLift 3244274
  have htrace : WordTrace (prefixWord ++ tailWord_3244274) baseStart_3244274 baseEnd_3244274 := by
    simpa [prefixWord, tailWord_3244274, baseEnd_3244274] using wordTrace_append hprefix tailTrace_3244274
  have hstable : (prefixWord ++ tailWord_3244274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244274).length < 2 ^ (prefixWord ++ tailWord_3244274).sum := by decide
  have hdescent : baseEnd_3244274 < baseStart_3244274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244315 : List Nat := [1, 1, 1, 1, 1, 1, 6, 2, 8]
def baseStart_3244315 : Nat := 118140960795 + 3244315 * 2 ^ 59
def prefixEnd_3244315 : Nat := 4983230072969 + 3 ^ 40 * 3244315 * 2
def baseEnd_3244315 : Nat := 370198442131462074742705

theorem tailTrace_3244315 : CollatzResearch.WordTrace tailWord_3244315 prefixEnd_3244315 370198442131462074742705 := by
  unfold tailWord_3244315
  simp only [CollatzResearch.WordTrace]
  refine ⟨118329889241408314734158399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78886592827605543156105599 118329889241408314734158399)
  ·
    refine ⟨177494833862112472101237599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118329889241408314734158399 177494833862112472101237599)
    ·
      refine ⟨266242250793168708151856399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177494833862112472101237599 266242250793168708151856399)
      ·
        refine ⟨399363376189753062227784599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266242250793168708151856399 399363376189753062227784599)
        ·
          refine ⟨599045064284629593341676899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399363376189753062227784599 599045064284629593341676899)
          ·
            refine ⟨898567596426944390012515349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599045064284629593341676899 898567596426944390012515349)
            ·
              refine ⟨42120356082513018281836657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 898567596426944390012515349 42120356082513018281836657)
              ·
                refine ⟨31590267061884763711377493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42120356082513018281836657 31590267061884763711377493)
                ·
                  refine ⟨370198442131462074742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31590267061884763711377493 370198442131462074742705)
                  ·
                    rfl

theorem cell22_3244315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 2, 8].length) (baseStart_3244315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244315 prefixEnd_3244315 := by exact prefixLift 3244315
  have htrace : WordTrace (prefixWord ++ tailWord_3244315) baseStart_3244315 baseEnd_3244315 := by
    simpa [prefixWord, tailWord_3244315, baseEnd_3244315] using wordTrace_append hprefix tailTrace_3244315
  have hstable : (prefixWord ++ tailWord_3244315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244315).length < 2 ^ (prefixWord ++ tailWord_3244315).sum := by decide
  have hdescent : baseEnd_3244315 < baseStart_3244315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244332 : List Nat := [2, 2, 1, 1, 1, 3, 5, 1, 6]
def baseStart_3244332 : Nat := 118140960795 + 3244332 * 2 ^ 59
def prefixEnd_3244332 : Nat := 4983230072969 + 3 ^ 40 * 3244332 * 2
def baseEnd_3244332 : Nat := 370200381947267948851021

theorem tailTrace_3244332 : CollatzResearch.WordTrace tailWord_3244332 prefixEnd_3244332 370200381947267948851021 := by
  unfold tailWord_3244332
  simp only [CollatzResearch.WordTrace]
  refine ⟨59165254641173363318763625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78887006188231151091684833 59165254641173363318763625)
  ·
    refine ⟨44373940980880022489072719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59165254641173363318763625 44373940980880022489072719)
    ·
      refine ⟨66560911471320033733609079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44373940980880022489072719 66560911471320033733609079)
      ·
        refine ⟨99841367206980050600413619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66560911471320033733609079 99841367206980050600413619)
        ·
          refine ⟨149762050810470075900620429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99841367206980050600413619 149762050810470075900620429)
          ·
            refine ⟨56160769053926278462732661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149762050810470075900620429 56160769053926278462732661)
            ·
              refine ⟨5265072098805588605881187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56160769053926278462732661 5265072098805588605881187)
              ·
                refine ⟨7897608148208382908821781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265072098805588605881187 7897608148208382908821781)
                ·
                  refine ⟨370200381947267948851021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7897608148208382908821781 370200381947267948851021)
                  ·
                    rfl

theorem cell22_3244332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 6].length) (baseStart_3244332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244332 prefixEnd_3244332 := by exact prefixLift 3244332
  have htrace : WordTrace (prefixWord ++ tailWord_3244332) baseStart_3244332 baseEnd_3244332 := by
    simpa [prefixWord, tailWord_3244332, baseEnd_3244332] using wordTrace_append hprefix tailTrace_3244332
  have hstable : (prefixWord ++ tailWord_3244332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244332).length < 2 ^ (prefixWord ++ tailWord_3244332).sum := by decide
  have hdescent : baseEnd_3244332 < baseStart_3244332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244338 : List Nat := [3, 2, 1, 1, 6, 1, 2, 1, 5]
def baseStart_3244338 : Nat := 118140960795 + 3244338 * 2 ^ 59
def prefixEnd_3244338 : Nat := 4983230072969 + 3 ^ 40 * 3244338 * 2
def baseEnd_3244338 : Nat := 370201066588140610301015

theorem tailTrace_3244338 : CollatzResearch.WordTrace tailWord_3244338 prefixEnd_3244338 370201066588140610301015 := by
  unfold tailWord_3244338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29582682030081247415561417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78887152080216659774830445 29582682030081247415561417)
  ·
    refine ⟨22187011522560935561671063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29582682030081247415561417 22187011522560935561671063)
    ·
      refine ⟨33280517283841403342506595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22187011522560935561671063 33280517283841403342506595)
      ·
        refine ⟨49920775925762105013759893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33280517283841403342506595 49920775925762105013759893)
        ·
          refine ⟨2340036371520098672519995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49920775925762105013759893 2340036371520098672519995)
          ·
            refine ⟨3510054557280148008779993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340036371520098672519995 3510054557280148008779993)
            ·
              refine ⟨2632540917960111006584995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510054557280148008779993 2632540917960111006584995)
              ·
                refine ⟨3948811376940166509877493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2632540917960111006584995 3948811376940166509877493)
                ·
                  refine ⟨370201066588140610301015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3948811376940166509877493 370201066588140610301015)
                  ·
                    rfl

theorem cell22_3244338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_3244338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244338 prefixEnd_3244338 := by exact prefixLift 3244338
  have htrace : WordTrace (prefixWord ++ tailWord_3244338) baseStart_3244338 baseEnd_3244338 := by
    simpa [prefixWord, tailWord_3244338, baseEnd_3244338] using wordTrace_append hprefix tailTrace_3244338
  have hstable : (prefixWord ++ tailWord_3244338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244338).length < 2 ^ (prefixWord ++ tailWord_3244338).sum := by decide
  have hdescent : baseEnd_3244338 < baseStart_3244338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244394 : List Nat := [3, 1, 3, 3, 1, 1, 3, 7]
def baseStart_3244394 : Nat := 118140960795 + 3244394 * 2 ^ 59
def prefixEnd_3244394 : Nat := 4983230072969 + 3 ^ 40 * 3244394 * 2
def baseEnd_3244394 : Nat := 123402485523206261278097

theorem tailTrace_3244394 : CollatzResearch.WordTrace tailWord_3244394 prefixEnd_3244394 123402485523206261278097 := by
  unfold tailWord_3244394
  simp only [CollatzResearch.WordTrace]
  refine ⟨29583192652030527806571059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78888513738748074150856157 29583192652030527806571059)
  ·
    refine ⟨44374788978045791709856589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29583192652030527806571059 44374788978045791709856589)
    ·
      refine ⟨16640545866767171891196221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44374788978045791709856589 16640545866767171891196221)
      ·
        refine ⟨6240204700037689459198583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16640545866767171891196221 6240204700037689459198583)
        ·
          refine ⟨9360307050056534188797875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240204700037689459198583 9360307050056534188797875)
          ·
            refine ⟨14040460575084801283196813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9360307050056534188797875 14040460575084801283196813)
            ·
              refine ⟨5265172715656800481198805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14040460575084801283196813 5265172715656800481198805)
              ·
                refine ⟨123402485523206261278097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5265172715656800481198805 123402485523206261278097)
                ·
                  rfl

theorem cell22_3244394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 7].length) (baseStart_3244394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244394 prefixEnd_3244394 := by exact prefixLift 3244394
  have htrace : WordTrace (prefixWord ++ tailWord_3244394) baseStart_3244394 baseEnd_3244394 := by
    simpa [prefixWord, tailWord_3244394, baseEnd_3244394] using wordTrace_append hprefix tailTrace_3244394
  have hstable : (prefixWord ++ tailWord_3244394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244394).length < 2 ^ (prefixWord ++ tailWord_3244394).sum := by decide
  have hdescent : baseEnd_3244394 < baseStart_3244394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244439 : List Nat := [1, 1, 3, 3, 1, 1, 5, 2, 5]
def baseStart_3244439 : Nat := 118140960795 + 3244439 * 2 ^ 59
def prefixEnd_3244439 : Nat := 4983230072969 + 3 ^ 40 * 3244439 * 2
def baseEnd_3244439 : Nat := 370212591376163744709245

theorem tailTrace_3244439 : CollatzResearch.WordTrace tailWord_3244439 prefixEnd_3244439 370212591376163744709245 := by
  unfold tailWord_3244439
  simp only [CollatzResearch.WordTrace]
  refine ⟨118334411892959083911672371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78889607928639389274448247 118334411892959083911672371)
  ·
    refine ⟨177501617839438625867508557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118334411892959083911672371 177501617839438625867508557)
    ·
      refine ⟨66563106689789484700315709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177501617839438625867508557 66563106689789484700315709)
      ·
        refine ⟨24961165008671056762618391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66563106689789484700315709 24961165008671056762618391)
        ·
          refine ⟨37441747513006585143927587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24961165008671056762618391 37441747513006585143927587)
          ·
            refine ⟨56162621269509877715891381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37441747513006585143927587 56162621269509877715891381)
            ·
              refine ⟨5265245744016551035864817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56162621269509877715891381 5265245744016551035864817)
              ·
                refine ⟨3948934308012413276898613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265245744016551035864817 3948934308012413276898613)
                ·
                  refine ⟨370212591376163744709245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3948934308012413276898613 370212591376163744709245)
                  ·
                    rfl

theorem cell22_3244439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 5, 2, 5].length) (baseStart_3244439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244439 prefixEnd_3244439 := by exact prefixLift 3244439
  have htrace : WordTrace (prefixWord ++ tailWord_3244439) baseStart_3244439 baseEnd_3244439 := by
    simpa [prefixWord, tailWord_3244439, baseEnd_3244439] using wordTrace_append hprefix tailTrace_3244439
  have hstable : (prefixWord ++ tailWord_3244439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244439).length < 2 ^ (prefixWord ++ tailWord_3244439).sum := by decide
  have hdescent : baseEnd_3244439 < baseStart_3244439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244501 : List Nat := [1, 3, 2, 3, 1, 4, 1, 1, 6]
def baseStart_3244501 : Nat := 118140960795 + 3244501 * 2 ^ 59
def prefixEnd_3244501 : Nat := 4983230072969 + 3 ^ 40 * 3244501 * 2
def baseEnd_3244501 : Nat := 370219665998514579692515

theorem tailTrace_3244501 : CollatzResearch.WordTrace tailWord_3244501 prefixEnd_3244501 370219665998514579692515 := by
  unfold tailWord_3244501
  simp only [CollatzResearch.WordTrace]
  refine ⟨118336673218734468500429357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78891115479156312333619571 118336673218734468500429357)
  ·
    refine ⟨44376252457025425687661009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118336673218734468500429357 44376252457025425687661009)
    ·
      refine ⟨33282189342769069265745757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44376252457025425687661009 33282189342769069265745757)
      ·
        refine ⟨12480821003538400974654659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33282189342769069265745757 12480821003538400974654659)
        ·
          refine ⟨18721231505307601461981989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12480821003538400974654659 18721231505307601461981989)
          ·
            refine ⟨3510230907245175274121623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18721231505307601461981989 3510230907245175274121623)
            ·
              refine ⟨5265346360867762911182435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3510230907245175274121623 5265346360867762911182435)
              ·
                refine ⟨7898019541301644366773653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265346360867762911182435 7898019541301644366773653)
                ·
                  refine ⟨370219665998514579692515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7898019541301644366773653 370219665998514579692515)
                  ·
                    rfl

theorem cell22_3244501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_3244501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244501 prefixEnd_3244501 := by exact prefixLift 3244501
  have htrace : WordTrace (prefixWord ++ tailWord_3244501) baseStart_3244501 baseEnd_3244501 := by
    simpa [prefixWord, tailWord_3244501, baseEnd_3244501] using wordTrace_append hprefix tailTrace_3244501
  have hstable : (prefixWord ++ tailWord_3244501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244501).length < 2 ^ (prefixWord ++ tailWord_3244501).sum := by decide
  have hdescent : baseEnd_3244501 < baseStart_3244501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244533 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 1, 5]
def baseStart_3244533 : Nat := 118140960795 + 3244533 * 2 ^ 59
def prefixEnd_3244533 : Nat := 4983230072969 + 3 ^ 40 * 3244533 * 2
def baseEnd_3244533 : Nat := 1110669952249506322277447

theorem tailTrace_3244533 : CollatzResearch.WordTrace tailWord_3244533 prefixEnd_3244533 1110669952249506322277447 := by
  unfold tailWord_3244533
  simp only [CollatzResearch.WordTrace]
  refine ⟨118337840354618537965594253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78891893569745691977062835 118337840354618537965594253)
  ·
    refine ⟨44376690132981951737097845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118337840354618537965594253 44376690132981951737097845)
    ·
      refine ⟨4160314699967057975352923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44376690132981951737097845 4160314699967057975352923)
      ·
        refine ⟨6240472049950586963029385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160314699967057975352923 6240472049950586963029385)
        ·
          refine ⟨4680354037462940222272039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6240472049950586963029385 4680354037462940222272039)
          ·
            refine ⟨7020531056194410333408059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680354037462940222272039 7020531056194410333408059)
            ·
              refine ⟨10530796584291615500112089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020531056194410333408059 10530796584291615500112089)
              ·
                refine ⟨7898097438218711625084067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10530796584291615500112089 7898097438218711625084067)
                ·
                  refine ⟨11847146157328067437626101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898097438218711625084067 11847146157328067437626101)
                  ·
                    refine ⟨1110669952249506322277447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11847146157328067437626101 1110669952249506322277447)
                    ·
                      rfl

theorem cell22_3244533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_3244533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244533 prefixEnd_3244533 := by exact prefixLift 3244533
  have htrace : WordTrace (prefixWord ++ tailWord_3244533) baseStart_3244533 baseEnd_3244533 := by
    simpa [prefixWord, tailWord_3244533, baseEnd_3244533] using wordTrace_append hprefix tailTrace_3244533
  have hstable : (prefixWord ++ tailWord_3244533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244533).length < 2 ^ (prefixWord ++ tailWord_3244533).sum := by decide
  have hdescent : baseEnd_3244533 < baseStart_3244533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244546 : List Nat := [3, 4, 1, 2, 2, 10]
def baseStart_3244546 : Nat := 118140960795 + 3244546 * 2 ^ 59
def prefixEnd_3244546 : Nat := 4983230072969 + 3 ^ 40 * 3244546 * 2
def baseEnd_3244546 : Nat := 13712029659446649650647

theorem tailTrace_3244546 : CollatzResearch.WordTrace tailWord_3244546 prefixEnd_3244546 13712029659446649650647 := by
  unfold tailWord_3244546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29584578625892860296454373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78892209669047627457211661 29584578625892860296454373)
  ·
    refine ⟨5547108492354911305585195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29584578625892860296454373 5547108492354911305585195)
    ·
      refine ⟨8320662738532366958377793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547108492354911305585195 8320662738532366958377793)
      ·
        refine ⟨6240497053899275218783345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8320662738532366958377793 6240497053899275218783345)
        ·
          refine ⟨4680372790424456414087509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6240497053899275218783345 4680372790424456414087509)
          ·
            refine ⟨13712029659446649650647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4680372790424456414087509 13712029659446649650647)
            ·
              rfl

theorem cell22_3244546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 10].length) (baseStart_3244546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244546 prefixEnd_3244546 := by exact prefixLift 3244546
  have htrace : WordTrace (prefixWord ++ tailWord_3244546) baseStart_3244546 baseEnd_3244546 := by
    simpa [prefixWord, tailWord_3244546, baseEnd_3244546] using wordTrace_append hprefix tailTrace_3244546
  have hstable : (prefixWord ++ tailWord_3244546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244546).length < 2 ^ (prefixWord ++ tailWord_3244546).sum := by decide
  have hdescent : baseEnd_3244546 < baseStart_3244546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244619 : List Nat := [1, 1, 1, 1, 3, 1, 5, 3, 6]
def baseStart_3244619 : Nat := 118140960795 + 3244619 * 2 ^ 59
def prefixEnd_3244619 : Nat := 4983230072969 + 3 ^ 40 * 3244619 * 2
def baseEnd_3244619 : Nat := 370233130602343588209061

theorem tailTrace_3244619 : CollatzResearch.WordTrace tailWord_3244619 prefixEnd_3244619 370233130602343588209061 := by
  unfold tailWord_3244619
  simp only [CollatzResearch.WordTrace]
  refine ⟨118340977032306974653224911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78893984688204649768816607 118340977032306974653224911)
  ·
    refine ⟨177511465548460461979837367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118340977032306974653224911 177511465548460461979837367)
    ·
      refine ⟨266267198322690692969756051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177511465548460461979837367 266267198322690692969756051)
      ·
        refine ⟨399400797484036039454634077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266267198322690692969756051 399400797484036039454634077)
        ·
          refine ⟨149775299056513514795487779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399400797484036039454634077 149775299056513514795487779)
          ·
            refine ⟨224662948584770272193231669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149775299056513514795487779 224662948584770272193231669)
            ·
              refine ⟨21062151429822213018115469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224662948584770272193231669 21062151429822213018115469)
              ·
                refine ⟨7898306786183329881793301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21062151429822213018115469 7898306786183329881793301)
                ·
                  refine ⟨370233130602343588209061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7898306786183329881793301 370233130602343588209061)
                  ·
                    rfl

theorem cell22_3244619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 3, 6].length) (baseStart_3244619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244619 prefixEnd_3244619 := by exact prefixLift 3244619
  have htrace : WordTrace (prefixWord ++ tailWord_3244619) baseStart_3244619 baseEnd_3244619 := by
    simpa [prefixWord, tailWord_3244619, baseEnd_3244619] using wordTrace_append hprefix tailTrace_3244619
  have hstable : (prefixWord ++ tailWord_3244619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244619).length < 2 ^ (prefixWord ++ tailWord_3244619).sum := by decide
  have hdescent : baseEnd_3244619 < baseStart_3244619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244730 : List Nat := [3, 1, 1, 1, 2, 3, 3, 4, 1, 3]
def baseStart_3244730 : Nat := 118140960795 + 3244730 * 2 ^ 59
def prefixEnd_3244730 : Nat := 4983230072969 + 3 ^ 40 * 3244730 * 2
def baseEnd_3244730 : Nat := 1110737389375463475101843

theorem tailTrace_3244730 : CollatzResearch.WordTrace tailWord_3244730 prefixEnd_3244730 1110737389375463475101843 := by
  unfold tailWord_3244730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29586256383726210152628911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78896683689936560407010429 29586256383726210152628911)
  ·
    refine ⟨44379384575589315228943367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29586256383726210152628911 44379384575589315228943367)
    ·
      refine ⟨66569076863383972843415051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44379384575589315228943367 66569076863383972843415051)
      ·
        refine ⟨99853615295075959265122577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66569076863383972843415051 99853615295075959265122577)
        ·
          refine ⟨74890211471306969448841933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99853615295075959265122577 74890211471306969448841933)
          ·
            refine ⟨28083829301740113543315725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74890211471306969448841933 28083829301740113543315725)
            ·
              refine ⟨10531435988152542578743397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28083829301740113543315725 10531435988152542578743397)
              ·
                refine ⟨1974644247778601733514387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10531435988152542578743397 1974644247778601733514387)
                ·
                  refine ⟨2961966371667902600271581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974644247778601733514387 2961966371667902600271581)
                  ·
                    refine ⟨1110737389375463475101843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961966371667902600271581 1110737389375463475101843)
                    ·
                      rfl

theorem cell22_3244730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 1, 3].length) (baseStart_3244730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244730 prefixEnd_3244730 := by exact prefixLift 3244730
  have htrace : WordTrace (prefixWord ++ tailWord_3244730) baseStart_3244730 baseEnd_3244730 := by
    simpa [prefixWord, tailWord_3244730, baseEnd_3244730] using wordTrace_append hprefix tailTrace_3244730
  have hstable : (prefixWord ++ tailWord_3244730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244730).length < 2 ^ (prefixWord ++ tailWord_3244730).sum := by decide
  have hdescent : baseEnd_3244730 < baseStart_3244730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244764 : List Nat := [2, 2, 5, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3244764 : Nat := 118140960795 + 3244764 * 2 ^ 59
def prefixEnd_3244764 : Nat := 4983230072969 + 3 ^ 40 * 3244764 * 2
def baseEnd_3244764 : Nat := 1110749028270298719751739

theorem tailTrace_3244764 : CollatzResearch.WordTrace tailWord_3244764 prefixEnd_3244764 1110749028270298719751739 := by
  unfold tailWord_3244764
  simp only [CollatzResearch.WordTrace]
  refine ⟨59173132808390832208626673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78897510411187776278168897 59173132808390832208626673)
  ·
    refine ⟨44379849606293124156470005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59173132808390832208626673 44379849606293124156470005)
    ·
      refine ⟨4160610900589980389669063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44379849606293124156470005 4160610900589980389669063)
      ·
        refine ⟨6240916350884970584503595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4160610900589980389669063 6240916350884970584503595)
        ·
          refine ⟨9361374526327455876755393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6240916350884970584503595 9361374526327455876755393)
          ·
            refine ⟨7021030894745591907566545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9361374526327455876755393 7021030894745591907566545)
            ·
              refine ⟨5265773171059193930674909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7021030894745591907566545 5265773171059193930674909)
              ·
                refine ⟨1974664939147197724003091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5265773171059193930674909 1974664939147197724003091)
                ·
                  refine ⟨2961997408720796586004637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974664939147197724003091 2961997408720796586004637)
                  ·
                    refine ⟨1110749028270298719751739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2961997408720796586004637 1110749028270298719751739)
                    ·
                      rfl

theorem cell22_3244764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3244764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244764 prefixEnd_3244764 := by exact prefixLift 3244764
  have htrace : WordTrace (prefixWord ++ tailWord_3244764) baseStart_3244764 baseEnd_3244764 := by
    simpa [prefixWord, tailWord_3244764, baseEnd_3244764] using wordTrace_append hprefix tailTrace_3244764
  have hstable : (prefixWord ++ tailWord_3244764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244764).length < 2 ^ (prefixWord ++ tailWord_3244764).sum := by decide
  have hdescent : baseEnd_3244764 < baseStart_3244764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244854 : List Nat := [5, 1, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3244854 : Nat := 118140960795 + 3244854 * 2 ^ 59
def prefixEnd_3244854 : Nat := 4983230072969 + 3 ^ 40 * 3244854 * 2
def baseEnd_3244854 : Nat := 1110779837109568485001463

theorem tailTrace_3244854 : CollatzResearch.WordTrace tailWord_3244854 prefixEnd_3244854 1110779837109568485001463 := by
  unfold tailWord_3244854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396846761653475611751851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78899698790970406525353077 7396846761653475611751851)
  ·
    refine ⟨11095270142480213417627777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7396846761653475611751851 11095270142480213417627777)
    ·
      refine ⟨8321452606860160063220833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11095270142480213417627777 8321452606860160063220833)
      ·
        refine ⟨6241089455145120047415625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8321452606860160063220833 6241089455145120047415625)
        ·
          refine ⟨4680817091358840035561719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6241089455145120047415625 4680817091358840035561719)
          ·
            refine ⟨7021225637038260053342579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680817091358840035561719 7021225637038260053342579)
            ·
              refine ⟨10531838455557390080013869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021225637038260053342579 10531838455557390080013869)
              ·
                refine ⟨3949439420834021280005201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10531838455557390080013869 3949439420834021280005201)
                ·
                  refine ⟨2962079565625515960003901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3949439420834021280005201 2962079565625515960003901)
                  ·
                    refine ⟨1110779837109568485001463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962079565625515960003901 1110779837109568485001463)
                    ·
                      rfl

theorem cell22_3244854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3244854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244854 prefixEnd_3244854 := by exact prefixLift 3244854
  have htrace : WordTrace (prefixWord ++ tailWord_3244854) baseStart_3244854 baseEnd_3244854 := by
    simpa [prefixWord, tailWord_3244854, baseEnd_3244854] using wordTrace_append hprefix tailTrace_3244854
  have hstable : (prefixWord ++ tailWord_3244854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244854).length < 2 ^ (prefixWord ++ tailWord_3244854).sum := by decide
  have hdescent : baseEnd_3244854 < baseStart_3244854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244882 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3244882 : Nat := 118140960795 + 3244882 * 2 ^ 59
def prefixEnd_3244882 : Nat := 4983230072969 + 3 ^ 40 * 3244882 * 2
def baseEnd_3244882 : Nat := 1110789422081785745301377

theorem tailTrace_3244882 : CollatzResearch.WordTrace tailWord_3244882 prefixEnd_3244882 1110789422081785745301377 := by
  unfold tailWord_3244882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29587642357588542642512225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78900379620236113713365933 29587642357588542642512225)
  ·
    refine ⟨22190731768191406981884169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29587642357588542642512225 22190731768191406981884169)
    ·
      refine ⟨16643048826143555236413127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22190731768191406981884169 16643048826143555236413127)
      ·
        refine ⟨24964573239215332854619691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16643048826143555236413127 24964573239215332854619691)
        ·
          refine ⟨37446859858822999281929537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24964573239215332854619691 37446859858822999281929537)
          ·
            refine ⟨28085144894117249461447153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37446859858822999281929537 28085144894117249461447153)
            ·
              refine ⟨21063858670587937096085365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28085144894117249461447153 21063858670587937096085365)
              ·
                refine ⟨1974736750367619102758003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21063858670587937096085365 1974736750367619102758003)
                ·
                  refine ⟨2962105125551428654137005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974736750367619102758003 2962105125551428654137005)
                  ·
                    refine ⟨1110789422081785745301377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962105125551428654137005 1110789422081785745301377)
                    ·
                      rfl

theorem cell22_3244882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3244882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244882 prefixEnd_3244882 := by exact prefixLift 3244882
  have htrace : WordTrace (prefixWord ++ tailWord_3244882) baseStart_3244882 baseEnd_3244882 := by
    simpa [prefixWord, tailWord_3244882, baseEnd_3244882] using wordTrace_append hprefix tailTrace_3244882
  have hstable : (prefixWord ++ tailWord_3244882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244882).length < 2 ^ (prefixWord ++ tailWord_3244882).sum := by decide
  have hdescent : baseEnd_3244882 < baseStart_3244882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244891 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 8]
def baseStart_3244891 : Nat := 118140960795 + 3244891 * 2 ^ 59
def prefixEnd_3244891 : Nat := 4983230072969 + 3 ^ 40 * 3244891 * 2
def baseEnd_3244891 : Nat := 1110792502965712721826349

theorem tailTrace_3244891 : CollatzResearch.WordTrace tailWord_3244891 prefixEnd_3244891 1110792502965712721826349 := by
  unfold tailWord_3244891
  simp only [CollatzResearch.WordTrace]
  refine ⟨118350897687321565107126527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78900598458214376738084351 118350897687321565107126527)
  ·
    refine ⟨177526346530982347660689791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118350897687321565107126527 177526346530982347660689791)
    ·
      refine ⟨266289519796473521491034687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177526346530982347660689791 266289519796473521491034687)
      ·
        refine ⟨399434279694710282236552031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266289519796473521491034687 399434279694710282236552031)
        ·
          refine ⟨599151419542065423354828047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399434279694710282236552031 599151419542065423354828047)
          ·
            refine ⟨898727129313098135032242071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599151419542065423354828047 898727129313098135032242071)
            ·
              refine ⟨1348090693969647202548363107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898727129313098135032242071 1348090693969647202548363107)
              ·
                refine ⟨2022136040954470803822544661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1348090693969647202548363107 2022136040954470803822544661)
                ·
                  refine ⟨94787626919740818929181781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2022136040954470803822544661 94787626919740818929181781)
                  ·
                    refine ⟨1110792502965712721826349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94787626919740818929181781 1110792502965712721826349)
                    ·
                      rfl

theorem cell22_3244891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_3244891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244891 prefixEnd_3244891 := by exact prefixLift 3244891
  have htrace : WordTrace (prefixWord ++ tailWord_3244891) baseStart_3244891 baseEnd_3244891 := by
    simpa [prefixWord, tailWord_3244891, baseEnd_3244891] using wordTrace_append hprefix tailTrace_3244891
  have hstable : (prefixWord ++ tailWord_3244891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244891).length < 2 ^ (prefixWord ++ tailWord_3244891).sum := by decide
  have hdescent : baseEnd_3244891 < baseStart_3244891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244899 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 1, 3]
def baseStart_3244899 : Nat := 118140960795 + 3244899 * 2 ^ 59
def prefixEnd_3244899 : Nat := 4983230072969 + 3 ^ 40 * 3244899 * 2
def baseEnd_3244899 : Nat := 1110795241529203367626325

theorem tailTrace_3244899 : CollatzResearch.WordTrace tailWord_3244899 prefixEnd_3244899 1110795241529203367626325 := by
  unfold tailWord_3244899
  simp only [CollatzResearch.WordTrace]
  refine ⟨118351189471292582473417751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78900792980861721648945167 118351189471292582473417751)
  ·
    refine ⟨177526784206938873710126627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118351189471292582473417751 177526784206938873710126627)
    ·
      refine ⟨266290176310408310565189941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177526784206938873710126627 266290176310408310565189941)
      ·
        refine ⟨24964704029100779115486557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266290176310408310565189941 24964704029100779115486557)
        ·
          refine ⟨9361764010912792168307459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24964704029100779115486557 9361764010912792168307459)
          ·
            refine ⟨14042646016369188252461189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361764010912792168307459 14042646016369188252461189)
            ·
              refine ⟨2632996128069222797336473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14042646016369188252461189 2632996128069222797336473)
              ·
                refine ⟨1974747096051917098002355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632996128069222797336473 1974747096051917098002355)
                ·
                  refine ⟨2962120644077875647003533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974747096051917098002355 2962120644077875647003533)
                  ·
                    refine ⟨1110795241529203367626325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962120644077875647003533 1110795241529203367626325)
                    ·
                      rfl

theorem cell22_3244899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 3].length) (baseStart_3244899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244899 prefixEnd_3244899 := by exact prefixLift 3244899
  have htrace : WordTrace (prefixWord ++ tailWord_3244899) baseStart_3244899 baseEnd_3244899 := by
    simpa [prefixWord, tailWord_3244899, baseEnd_3244899] using wordTrace_append hprefix tailTrace_3244899
  have hstable : (prefixWord ++ tailWord_3244899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244899).length < 2 ^ (prefixWord ++ tailWord_3244899).sum := by decide
  have hdescent : baseEnd_3244899 < baseStart_3244899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244908 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 5, 4]
def baseStart_3244908 : Nat := 118140960795 + 3244908 * 2 ^ 59
def prefixEnd_3244908 : Nat := 4983230072969 + 3 ^ 40 * 3244908 * 2
def baseEnd_3244908 : Nat := 1110798322413130344151297

theorem tailTrace_3244908 : CollatzResearch.WordTrace tailWord_3244908 prefixEnd_3244908 1110798322413130344151297 := by
  unfold tailWord_3244908
  simp only [CollatzResearch.WordTrace]
  refine ⟨59175758864129988505247689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78901011818839984673663585 59175758864129988505247689)
  ·
    refine ⟨44381819148097491378935767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59175758864129988505247689 44381819148097491378935767)
    ·
      refine ⟨66572728722146237068403651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44381819148097491378935767 66572728722146237068403651)
      ·
        refine ⟨99859093083219355602605477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66572728722146237068403651 99859093083219355602605477)
        ·
          refine ⟨18723579953103629175488527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99859093083219355602605477 18723579953103629175488527)
          ·
            refine ⟨28085369929655443763232791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18723579953103629175488527 28085369929655443763232791)
            ·
              refine ⟨42128054894483165644849187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28085369929655443763232791 42128054894483165644849187)
              ·
                refine ⟨63192082341724748467273781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42128054894483165644849187 63192082341724748467273781)
                ·
                  refine ⟨5924257719536695168806917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63192082341724748467273781 5924257719536695168806917)
                  ·
                    refine ⟨1110798322413130344151297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5924257719536695168806917 1110798322413130344151297)
                    ·
                      rfl

theorem cell22_3244908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 4].length) (baseStart_3244908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244908 prefixEnd_3244908 := by exact prefixLift 3244908
  have htrace : WordTrace (prefixWord ++ tailWord_3244908) baseStart_3244908 baseEnd_3244908 := by
    simpa [prefixWord, tailWord_3244908, baseEnd_3244908] using wordTrace_append hprefix tailTrace_3244908
  have hstable : (prefixWord ++ tailWord_3244908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244908).length < 2 ^ (prefixWord ++ tailWord_3244908).sum := by decide
  have hdescent : baseEnd_3244908 < baseStart_3244908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244940 : List Nat := [2, 2, 1, 2, 1, 2, 3, 5, 4]
def baseStart_3244940 : Nat := 118140960795 + 3244940 * 2 ^ 59
def prefixEnd_3244940 : Nat := 4983230072969 + 3 ^ 40 * 3244940 * 2
def baseEnd_3244940 : Nat := 370269758889030975783733

theorem tailTrace_3244940 : CollatzResearch.WordTrace tailWord_3244940 prefixEnd_3244940 370269758889030975783733 := by
  unfold tailWord_3244940
  simp only [CollatzResearch.WordTrace]
  refine ⟨59176342432072023237830137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78901789909429364317106849 59176342432072023237830137)
  ·
    refine ⟨44382256824054017428372603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59176342432072023237830137 44382256824054017428372603)
    ·
      refine ⟨66573385236081026142558905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44382256824054017428372603 66573385236081026142558905)
      ·
        refine ⟨49930038927060769606919179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66573385236081026142558905 49930038927060769606919179)
        ·
          refine ⟨74895058390591154410378769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49930038927060769606919179 74895058390591154410378769)
          ·
            refine ⟨56171293792943365807784077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74895058390591154410378769 56171293792943365807784077)
            ·
              refine ⟨21064235172353762177919029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56171293792943365807784077 21064235172353762177919029)
              ·
                refine ⟨1974772047408165204179909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21064235172353762177919029 1974772047408165204179909)
                ·
                  refine ⟨370269758889030975783733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974772047408165204179909 370269758889030975783733)
                  ·
                    rfl

theorem cell22_3244940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_3244940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244940 prefixEnd_3244940 := by exact prefixLift 3244940
  have htrace : WordTrace (prefixWord ++ tailWord_3244940) baseStart_3244940 baseEnd_3244940 := by
    simpa [prefixWord, tailWord_3244940, baseEnd_3244940] using wordTrace_append hprefix tailTrace_3244940
  have hstable : (prefixWord ++ tailWord_3244940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244940).length < 2 ^ (prefixWord ++ tailWord_3244940).sum := by decide
  have hdescent : baseEnd_3244940 < baseStart_3244940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244953 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 4, 4]
def baseStart_3244953 : Nat := 118140960795 + 3244953 * 2 ^ 59
def prefixEnd_3244953 : Nat := 4983230072969 + 3 ^ 40 * 3244953 * 2
def baseEnd_3244953 : Nat := 1110813726832765226776159

theorem tailTrace_3244953 : CollatzResearch.WordTrace tailWord_3244953 prefixEnd_3244953 1110813726832765226776159 := by
  unfold tailWord_3244953
  simp only [CollatzResearch.WordTrace]
  refine ⟨118353159013096949695883513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78902106008731299797255675 118353159013096949695883513)
  ·
    refine ⟨88764869259822712271912635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118353159013096949695883513 88764869259822712271912635)
    ·
      refine ⟨133147303889734068407868953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88764869259822712271912635 133147303889734068407868953)
      ·
        refine ⟨99860477917300551305901715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133147303889734068407868953 99860477917300551305901715)
        ·
          refine ⟨149790716875950826958852573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99860477917300551305901715 149790716875950826958852573)
          ·
            refine ⟨56171518828481560109569715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149790716875950826958852573 56171518828481560109569715)
            ·
              refine ⟨84257278242722340164354573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56171518828481560109569715 84257278242722340164354573)
              ·
                refine ⟨31596479341020877561632965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84257278242722340164354573 31596479341020877561632965)
                ·
                  refine ⟨5924339876441414542806181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31596479341020877561632965 5924339876441414542806181)
                  ·
                    refine ⟨1110813726832765226776159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5924339876441414542806181 1110813726832765226776159)
                    ·
                      rfl

theorem cell22_3244953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 4].length) (baseStart_3244953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244953 prefixEnd_3244953 := by exact prefixLift 3244953
  have htrace : WordTrace (prefixWord ++ tailWord_3244953) baseStart_3244953 baseEnd_3244953 := by
    simpa [prefixWord, tailWord_3244953, baseEnd_3244953] using wordTrace_append hprefix tailTrace_3244953
  have hstable : (prefixWord ++ tailWord_3244953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244953).length < 2 ^ (prefixWord ++ tailWord_3244953).sum := by decide
  have hdescent : baseEnd_3244953 < baseStart_3244953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3244985 : List Nat := [1, 2, 1, 4, 2, 2, 4, 6]
def baseStart_3244985 : Nat := 118140960795 + 3244985 * 2 ^ 59
def prefixEnd_3244985 : Nat := 4983230072969 + 3 ^ 40 * 3244985 * 2
def baseEnd_3244985 : Nat := 123424964565191978886229

theorem tailTrace_3244985 : CollatzResearch.WordTrace tailWord_3244985 prefixEnd_3244985 123424964565191978886229 := by
  unfold tailWord_3244985
  simp only [CollatzResearch.WordTrace]
  refine ⟨118354326148981019161048409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78902884099320679440698939 118354326148981019161048409)
  ·
    refine ⟨88765744611735764370786307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118354326148981019161048409 88765744611735764370786307)
    ·
      refine ⟨133148616917603646556179461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88765744611735764370786307 133148616917603646556179461)
      ·
        refine ⟨24965365672050683729283649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133148616917603646556179461 24965365672050683729283649)
        ·
          refine ⟨18724024254038012796962737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24965365672050683729283649 18724024254038012796962737)
          ·
            refine ⟨14043018190528509597722053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18724024254038012796962737 14043018190528509597722053)
            ·
              refine ⟨2633065910724095549572885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14043018190528509597722053 2633065910724095549572885)
              ·
                refine ⟨123424964565191978886229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2633065910724095549572885 123424964565191978886229)
                ·
                  rfl

theorem cell22_3244985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 4, 6].length) (baseStart_3244985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3244985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3244985 prefixEnd_3244985 := by exact prefixLift 3244985
  have htrace : WordTrace (prefixWord ++ tailWord_3244985) baseStart_3244985 baseEnd_3244985 := by
    simpa [prefixWord, tailWord_3244985, baseEnd_3244985] using wordTrace_append hprefix tailTrace_3244985
  have hstable : (prefixWord ++ tailWord_3244985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3244985).length < 2 ^ (prefixWord ++ tailWord_3244985).sum := by decide
  have hdescent : baseEnd_3244985 < baseStart_3244985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3244985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245017 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 3, 3]
def baseStart_3245017 : Nat := 118140960795 + 3245017 * 2 ^ 59
def prefixEnd_3245017 : Nat := 4983230072969 + 3 ^ 40 * 3245017 * 2
def baseEnd_3245017 : Nat := 1110835635340690393175963

theorem tailTrace_3245017 : CollatzResearch.WordTrace tailWord_3245017 prefixEnd_3245017 1110835635340690393175963 := by
  unfold tailWord_3245017
  simp only [CollatzResearch.WordTrace]
  refine ⟨118355493284865088626213305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78903662189910059084142203 118355493284865088626213305)
  ·
    refine ⟨88766619963648816469659979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118355493284865088626213305 88766619963648816469659979)
    ·
      refine ⟨133149929945473224704489969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88766619963648816469659979 133149929945473224704489969)
      ·
        refine ⟨99862447459104918528367477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133149929945473224704489969 99862447459104918528367477)
        ·
          refine ⟨9362104449291086112034451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99862447459104918528367477 9362104449291086112034451)
          ·
            refine ⟨14043156673936629168051677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9362104449291086112034451 14043156673936629168051677)
            ·
              refine ⟨5266183752726235938019379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14043156673936629168051677 5266183752726235938019379)
              ·
                refine ⟨7899275629089353907029069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266183752726235938019379 7899275629089353907029069)
                ·
                  refine ⟨2962228360908507715135901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7899275629089353907029069 2962228360908507715135901)
                  ·
                    refine ⟨1110835635340690393175963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962228360908507715135901 1110835635340690393175963)
                    ·
                      rfl

theorem cell22_3245017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 3, 3].length) (baseStart_3245017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245017 prefixEnd_3245017 := by exact prefixLift 3245017
  have htrace : WordTrace (prefixWord ++ tailWord_3245017) baseStart_3245017 baseEnd_3245017 := by
    simpa [prefixWord, tailWord_3245017, baseEnd_3245017] using wordTrace_append hprefix tailTrace_3245017
  have hstable : (prefixWord ++ tailWord_3245017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245017).length < 2 ^ (prefixWord ++ tailWord_3245017).sum := by decide
  have hdescent : baseEnd_3245017 < baseStart_3245017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245092 : List Nat := [2, 3, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3245092 : Nat := 118140960795 + 3245092 * 2 ^ 59
def prefixEnd_3245092 : Nat := 4983230072969 + 3 ^ 40 * 3245092 * 2
def baseEnd_3245092 : Nat := 370287103124471732516911

theorem tailTrace_3245092 : CollatzResearch.WordTrace tailWord_3245092 prefixEnd_3245092 370287103124471732516911 := by
  unfold tailWord_3245092
  simp only [CollatzResearch.WordTrace]
  refine ⟨59179114379796688217596765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78905485839728917623462353 59179114379796688217596765)
  ·
    refine ⟨22192167892423758081598787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59179114379796688217596765 22192167892423758081598787)
    ·
      refine ⟨33288251838635637122398181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22192167892423758081598787 33288251838635637122398181)
      ·
        refine ⟨6241547219744181960449659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33288251838635637122398181 6241547219744181960449659)
        ·
          refine ⟨9362320829616272940674489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241547219744181960449659 9362320829616272940674489)
          ·
            refine ⟨7021740622212204705505867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9362320829616272940674489 7021740622212204705505867)
            ·
              refine ⟨10532610933318307058258801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021740622212204705505867 10532610933318307058258801)
              ·
                refine ⟨7899458199988730293694101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10532610933318307058258801 7899458199988730293694101)
                ·
                  refine ⟨370287103124471732516911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7899458199988730293694101 370287103124471732516911)
                  ·
                    rfl

theorem cell22_3245092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3245092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245092 prefixEnd_3245092 := by exact prefixLift 3245092
  have htrace : WordTrace (prefixWord ++ tailWord_3245092) baseStart_3245092 baseEnd_3245092 := by
    simpa [prefixWord, tailWord_3245092, baseEnd_3245092] using wordTrace_append hprefix tailTrace_3245092
  have hstable : (prefixWord ++ tailWord_3245092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245092).length < 2 ^ (prefixWord ++ tailWord_3245092).sum := by decide
  have hdescent : baseEnd_3245092 < baseStart_3245092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245105 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 6]
def baseStart_3245105 : Nat := 118140960795 + 3245105 * 2 ^ 59
def prefixEnd_3245105 : Nat := 4983230072969 + 3 ^ 40 * 3245105 * 2
def baseEnd_3245105 : Nat := 1110865759539087496975693

theorem tailTrace_3245105 : CollatzResearch.WordTrace tailWord_3245105 prefixEnd_3245105 1110865759539087496975693 := by
  unfold tailWord_3245105
  simp only [CollatzResearch.WordTrace]
  refine ⟨118358702908546279655416769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78905801939030853103611179 118358702908546279655416769)
  ·
    refine ⟨88769027181409709741562577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118358702908546279655416769 88769027181409709741562577)
    ·
      refine ⟨66576770386057282306171933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88769027181409709741562577 66576770386057282306171933)
      ·
        refine ⟨24966288894771480864814475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66576770386057282306171933 24966288894771480864814475)
        ·
          refine ⟨37449433342157221297221713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24966288894771480864814475 37449433342157221297221713)
          ·
            refine ⟨28087075006617915972916285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37449433342157221297221713 28087075006617915972916285)
            ·
              refine ⟨10532653127481718489843607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28087075006617915972916285 10532653127481718489843607)
              ·
                refine ⟨15798979691222577734765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10532653127481718489843607 15798979691222577734765411)
                ·
                  refine ⟨23698469536833866602148117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15798979691222577734765411 23698469536833866602148117)
                  ·
                    refine ⟨1110865759539087496975693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23698469536833866602148117 1110865759539087496975693)
                    ·
                      rfl

theorem cell22_3245105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_3245105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245105 prefixEnd_3245105 := by exact prefixLift 3245105
  have htrace : WordTrace (prefixWord ++ tailWord_3245105) baseStart_3245105 baseEnd_3245105 := by
    simpa [prefixWord, tailWord_3245105, baseEnd_3245105] using wordTrace_append hprefix tailTrace_3245105
  have hstable : (prefixWord ++ tailWord_3245105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245105).length < 2 ^ (prefixWord ++ tailWord_3245105).sum := by decide
  have hdescent : baseEnd_3245105 < baseStart_3245105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245126 : List Nat := [6, 1, 1, 1, 1, 2, 2, 4, 4]
def baseStart_3245126 : Nat := 118140960795 + 3245126 * 2 ^ 59
def prefixEnd_3245126 : Nat := 4983230072969 + 3 ^ 40 * 3245126 * 2
def baseEnd_3245126 : Nat := 370290982756083480733543

theorem tailTrace_3245126 : CollatzResearch.WordTrace tailWord_3245126 prefixEnd_3245126 370290982756083480733543 := by
  unfold tailWord_3245126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3698733401295943757560351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78906312560980133494620821 3698733401295943757560351)
  ·
    refine ⟨5548100101943915636340527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3698733401295943757560351 5548100101943915636340527)
    ·
      refine ⟨8322150152915873454510791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5548100101943915636340527 8322150152915873454510791)
      ·
        refine ⟨12483225229373810181766187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8322150152915873454510791 12483225229373810181766187)
        ·
          refine ⟨18724837844060715272649281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12483225229373810181766187 18724837844060715272649281)
          ·
            refine ⟨14043628383045536454486961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18724837844060715272649281 14043628383045536454486961)
            ·
              refine ⟨10532721287284152340865221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14043628383045536454486961 10532721287284152340865221)
              ·
                refine ⟨1974885241365778563912229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10532721287284152340865221 1974885241365778563912229)
                ·
                  refine ⟨370290982756083480733543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974885241365778563912229 370290982756083480733543)
                  ·
                    rfl

theorem cell22_3245126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_3245126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245126 prefixEnd_3245126 := by exact prefixLift 3245126
  have htrace : WordTrace (prefixWord ++ tailWord_3245126) baseStart_3245126 baseEnd_3245126 := by
    simpa [prefixWord, tailWord_3245126, baseEnd_3245126] using wordTrace_append hprefix tailTrace_3245126
  have hstable : (prefixWord ++ tailWord_3245126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245126).length < 2 ^ (prefixWord ++ tailWord_3245126).sum := by decide
  have hdescent : baseEnd_3245126 < baseStart_3245126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245152 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 3, 3]
def baseStart_3245152 : Nat := 118140960795 + 3245152 * 2 ^ 59
def prefixEnd_3245152 : Nat := 4983230072969 + 3 ^ 40 * 3245152 * 2
def baseEnd_3245152 : Nat := 1110881848599595041050549

theorem tailTrace_3245152 : CollatzResearch.WordTrace tailWord_3245152 prefixEnd_3245152 1110881848599595041050549 := by
  unfold tailWord_3245152
  simp only [CollatzResearch.WordTrace]
  refine ⟨59180208569688003341188855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78906944759584004454918473 59180208569688003341188855)
  ·
    refine ⟨88770312854532005011783283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59180208569688003341188855 88770312854532005011783283)
    ·
      refine ⟨133155469281798007517674925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88770312854532005011783283 133155469281798007517674925)
      ·
        refine ⟨49933300980674252819128097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133155469281798007517674925 49933300980674252819128097)
        ·
          refine ⟨37449975735505689614346073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49933300980674252819128097 37449975735505689614346073)
          ·
            refine ⟨28087481801629267210759555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37449975735505689614346073 28087481801629267210759555)
            ·
              refine ⟨42131222702443900816139333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28087481801629267210759555 42131222702443900816139333)
              ·
                refine ⟨7899604256708231403026125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42131222702443900816139333 7899604256708231403026125)
                ·
                  refine ⟨2962351596265586776134797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7899604256708231403026125 2962351596265586776134797)
                  ·
                    refine ⟨1110881848599595041050549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962351596265586776134797 1110881848599595041050549)
                    ·
                      rfl

theorem cell22_3245152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 3].length) (baseStart_3245152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245152 prefixEnd_3245152 := by exact prefixLift 3245152
  have htrace : WordTrace (prefixWord ++ tailWord_3245152) baseStart_3245152 baseEnd_3245152 := by
    simpa [prefixWord, tailWord_3245152, baseEnd_3245152] using wordTrace_append hprefix tailTrace_3245152
  have hstable : (prefixWord ++ tailWord_3245152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245152).length < 2 ^ (prefixWord ++ tailWord_3245152).sum := by decide
  have hdescent : baseEnd_3245152 < baseStart_3245152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245154 : List Nat := [3, 3, 2, 2, 1, 1, 4, 6]
def baseStart_3245154 : Nat := 118140960795 + 3245154 * 2 ^ 59
def prefixEnd_3245154 : Nat := 4983230072969 + 3 ^ 40 * 3245154 * 2
def baseEnd_3245154 : Nat := 123431392582274189166727

theorem tailTrace_3245154 : CollatzResearch.WordTrace tailWord_3245154 prefixEnd_3245154 123431392582274189166727 := by
  unfold tailWord_3245154
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590122521342190255987629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78906993390245840682633677 29590122521342190255987629)
  ·
    refine ⟨11096295945503321345995361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29590122521342190255987629 11096295945503321345995361)
    ·
      refine ⟨8322221959127491009496521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11096295945503321345995361 8322221959127491009496521)
      ·
        refine ⟨6241666469345618257122391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8322221959127491009496521 6241666469345618257122391)
        ·
          refine ⟨9362499704018427385683587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6241666469345618257122391 9362499704018427385683587)
          ·
            refine ⟨14043749556027641078525381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9362499704018427385683587 14043749556027641078525381)
            ·
              refine ⟨2633203041755182702223509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14043749556027641078525381 2633203041755182702223509)
              ·
                refine ⟨123431392582274189166727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2633203041755182702223509 123431392582274189166727)
                ·
                  rfl

theorem cell22_3245154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_3245154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245154 prefixEnd_3245154 := by exact prefixLift 3245154
  have htrace : WordTrace (prefixWord ++ tailWord_3245154) baseStart_3245154 baseEnd_3245154 := by
    simpa [prefixWord, tailWord_3245154, baseEnd_3245154] using wordTrace_append hprefix tailTrace_3245154
  have hstable : (prefixWord ++ tailWord_3245154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245154).length < 2 ^ (prefixWord ++ tailWord_3245154).sum := by decide
  have hdescent : baseEnd_3245154 < baseStart_3245154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245169 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 1, 3]
def baseStart_3245169 : Nat := 118140960795 + 3245169 * 2 ^ 59
def prefixEnd_3245169 : Nat := 4983230072969 + 3 ^ 40 * 3245169 * 2
def baseEnd_3245169 : Nat := 1110887668047012663375497

theorem tailTrace_3245169 : CollatzResearch.WordTrace tailWord_3245169 prefixEnd_3245169 1110887668047012663375497 := by
  unfold tailWord_3245169
  simp only [CollatzResearch.WordTrace]
  refine ⟨118361037180314418585746561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78907358120209612390497707 118361037180314418585746561)
  ·
    refine ⟨88770777885235813939309921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118361037180314418585746561 88770777885235813939309921)
    ·
      refine ⟨66578083413926860454482441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88770777885235813939309921 66578083413926860454482441)
      ·
        refine ⟨49933562560445145340861831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66578083413926860454482441 49933562560445145340861831)
        ·
          refine ⟨74900343840667718011292747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49933562560445145340861831 74900343840667718011292747)
          ·
            refine ⟨112350515761001577016939121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74900343840667718011292747 112350515761001577016939121)
            ·
              refine ⟨84262886820751182762704341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112350515761001577016939121 84262886820751182762704341)
              ·
                refine ⟨1974911409861355846000883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84262886820751182762704341 1974911409861355846000883)
                ·
                  refine ⟨2962367114792033769001325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974911409861355846000883 2962367114792033769001325)
                  ·
                    refine ⟨1110887668047012663375497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962367114792033769001325 1110887668047012663375497)
                    ·
                      rfl

theorem cell22_3245169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_3245169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245169 prefixEnd_3245169 := by exact prefixLift 3245169
  have htrace : WordTrace (prefixWord ++ tailWord_3245169) baseStart_3245169 baseEnd_3245169 := by
    simpa [prefixWord, tailWord_3245169, baseEnd_3245169] using wordTrace_append hprefix tailTrace_3245169
  have hstable : (prefixWord ++ tailWord_3245169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245169).length < 2 ^ (prefixWord ++ tailWord_3245169).sum := by decide
  have hdescent : baseEnd_3245169 < baseStart_3245169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245293 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3245293 : Nat := 118140960795 + 3245293 * 2 ^ 59
def prefixEnd_3245293 : Nat := 4983230072969 + 3 ^ 40 * 3245293 * 2
def baseEnd_3245293 : Nat := 1110930115781117673275117

theorem tailTrace_3245293 : CollatzResearch.WordTrace tailWord_3245293 prefixEnd_3245293 1110930115781117673275117 := by
  unfold tailWord_3245293
  simp only [CollatzResearch.WordTrace]
  refine ⟨118365559831865187763260533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78910373221243458508840355 118365559831865187763260533)
  ·
    refine ⟨11096771234237361352805675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118365559831865187763260533 11096771234237361352805675)
    ·
      refine ⟨16645156851356042029208513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096771234237361352805675 16645156851356042029208513)
      ·
        refine ⟨12483867638517031521906385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16645156851356042029208513 12483867638517031521906385)
        ·
          refine ⟨9362900728887773641429789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12483867638517031521906385 9362900728887773641429789)
          ·
            refine ⟨3511087773332915115536171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9362900728887773641429789 3511087773332915115536171)
            ·
              refine ⟨5266631659999372673304257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511087773332915115536171 5266631659999372673304257)
              ·
                refine ⟨3949973744999529504978193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5266631659999372673304257 3949973744999529504978193)
                ·
                  refine ⟨2962480308749647128733645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3949973744999529504978193 2962480308749647128733645)
                  ·
                    refine ⟨1110930115781117673275117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962480308749647128733645 1110930115781117673275117)
                    ·
                      rfl

theorem cell22_3245293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3245293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245293 prefixEnd_3245293 := by exact prefixLift 3245293
  have htrace : WordTrace (prefixWord ++ tailWord_3245293) baseStart_3245293 baseEnd_3245293 := by
    simpa [prefixWord, tailWord_3245293, baseEnd_3245293] using wordTrace_append hprefix tailTrace_3245293
  have hstable : (prefixWord ++ tailWord_3245293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245293).length < 2 ^ (prefixWord ++ tailWord_3245293).sum := by decide
  have hdescent : baseEnd_3245293 < baseStart_3245293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245338 : List Nat := [3, 1, 1, 3, 3, 1, 3, 3, 1, 3]
def baseStart_3245338 : Nat := 118140960795 + 3245338 * 2 ^ 59
def prefixEnd_3245338 : Nat := 4983230072969 + 3 ^ 40 * 3245338 * 2
def baseEnd_3245338 : Nat := 1110945520200752555899979

theorem tailTrace_3245338 : CollatzResearch.WordTrace tailWord_3245338 prefixEnd_3245338 1110945520200752555899979 := by
  unfold tailWord_3245338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591800279175540112162167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78911467411134773632432445 29591800279175540112162167)
  ·
    refine ⟨44387700418763310168243251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29591800279175540112162167 44387700418763310168243251)
    ·
      refine ⟨66581550628144965252364877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44387700418763310168243251 66581550628144965252364877)
      ·
        refine ⟨24968081485554361969636829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66581550628144965252364877 24968081485554361969636829)
        ·
          refine ⟨9363030557082885738613811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24968081485554361969636829 9363030557082885738613811)
          ·
            refine ⟨14044545835624328607920717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9363030557082885738613811 14044545835624328607920717)
            ·
              refine ⟨5266704688359123227970269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14044545835624328607920717 5266704688359123227970269)
              ·
                refine ⟨1975014258134671210488851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5266704688359123227970269 1975014258134671210488851)
                ·
                  refine ⟨2962521387202006815733277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975014258134671210488851 2962521387202006815733277)
                  ·
                    refine ⟨1110945520200752555899979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962521387202006815733277 1110945520200752555899979)
                    ·
                      rfl

theorem cell22_3245338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 3, 1, 3].length) (baseStart_3245338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245338 prefixEnd_3245338 := by exact prefixLift 3245338
  have htrace : WordTrace (prefixWord ++ tailWord_3245338) baseStart_3245338 baseEnd_3245338 := by
    simpa [prefixWord, tailWord_3245338, baseEnd_3245338] using wordTrace_append hprefix tailTrace_3245338
  have hstable : (prefixWord ++ tailWord_3245338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245338).length < 2 ^ (prefixWord ++ tailWord_3245338).sum := by decide
  have hdescent : baseEnd_3245338 < baseStart_3245338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245396 : List Nat := [2, 4, 1, 1, 2, 1, 2, 5, 4]
def baseStart_3245396 : Nat := 118140960795 + 3245396 * 2 ^ 59
def prefixEnd_3245396 : Nat := 4983230072969 + 3 ^ 40 * 3245396 * 2
def baseEnd_3245396 : Nat := 370321791595353245983267

theorem tailTrace_3245396 : CollatzResearch.WordTrace tailWord_3245396 prefixEnd_3245396 370321791595353245983267 := by
  unfold tailWord_3245396
  simp only [CollatzResearch.WordTrace]
  refine ⟨59184658275246018177130021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78912877700328024236173361 59184658275246018177130021)
  ·
    refine ⟨11097123426608628408211879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59184658275246018177130021 11097123426608628408211879)
    ·
      refine ⟨16645685139912942612317819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11097123426608628408211879 16645685139912942612317819)
      ·
        refine ⟨24968527709869413918476729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16645685139912942612317819 24968527709869413918476729)
        ·
          refine ⟨18726395782402060438857547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24968527709869413918476729 18726395782402060438857547)
          ·
            refine ⟨28089593673603090658286321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18726395782402060438857547 28089593673603090658286321)
            ·
              refine ⟨21067195255202317993714741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28089593673603090658286321 21067195255202317993714741)
              ·
                refine ⟨1975049555175217311910757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21067195255202317993714741 1975049555175217311910757)
                ·
                  refine ⟨370321791595353245983267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975049555175217311910757 370321791595353245983267)
                  ·
                    rfl

theorem cell22_3245396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5, 4].length) (baseStart_3245396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245396 prefixEnd_3245396 := by exact prefixLift 3245396
  have htrace : WordTrace (prefixWord ++ tailWord_3245396) baseStart_3245396 baseEnd_3245396 := by
    simpa [prefixWord, tailWord_3245396, baseEnd_3245396] using wordTrace_append hprefix tailTrace_3245396
  have hstable : (prefixWord ++ tailWord_3245396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245396).length < 2 ^ (prefixWord ++ tailWord_3245396).sum := by decide
  have hdescent : baseEnd_3245396 < baseStart_3245396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245411 : List Nat := [1, 1, 1, 5, 2, 2, 1, 4, 2, 3]
def baseStart_3245411 : Nat := 118140960795 + 3245411 * 2 ^ 59
def prefixEnd_3245411 : Nat := 4983230072969 + 3 ^ 40 * 3245411 * 2
def baseEnd_3245411 : Nat := 1110970509592604698824755

theorem tailTrace_3245411 : CollatzResearch.WordTrace tailWord_3245411 prefixEnd_3245411 1110970509592604698824755 := by
  unfold tailWord_3245411
  simp only [CollatzResearch.WordTrace]
  refine ⟨118369863645437693916056087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78913242430291795944037391 118369863645437693916056087)
  ·
    refine ⟨177554795468156540874084131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118369863645437693916056087 177554795468156540874084131)
    ·
      refine ⟨266332193202234811311126197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177554795468156540874084131 266332193202234811311126197)
      ·
        refine ⟨24968643112709513560418081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266332193202234811311126197 24968643112709513560418081)
        ·
          refine ⟨18726482334532135170313561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24968643112709513560418081 18726482334532135170313561)
          ·
            refine ⟨14044861750899101377735171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18726482334532135170313561 14044861750899101377735171)
            ·
              refine ⟨21067292626348652066602757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14044861750899101377735171 21067292626348652066602757)
              ·
                refine ⟨3950117367440372262488017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21067292626348652066602757 3950117367440372262488017)
                ·
                  refine ⟨2962588025580279196866013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950117367440372262488017 2962588025580279196866013)
                  ·
                    refine ⟨1110970509592604698824755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962588025580279196866013 1110970509592604698824755)
                    ·
                      rfl

theorem cell22_3245411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 4, 2, 3].length) (baseStart_3245411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245411 prefixEnd_3245411 := by exact prefixLift 3245411
  have htrace : WordTrace (prefixWord ++ tailWord_3245411) baseStart_3245411 baseEnd_3245411 := by
    simpa [prefixWord, tailWord_3245411, baseEnd_3245411] using wordTrace_append hprefix tailTrace_3245411
  have hstable : (prefixWord ++ tailWord_3245411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245411).length < 2 ^ (prefixWord ++ tailWord_3245411).sum := by decide
  have hdescent : baseEnd_3245411 < baseStart_3245411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245484 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 2, 5]
def baseStart_3245484 : Nat := 118140960795 + 3245484 * 2 ^ 59
def prefixEnd_3245484 : Nat := 4983230072969 + 3 ^ 40 * 3245484 * 2
def baseEnd_3245484 : Nat := 1110995498984456841749531

theorem tailTrace_3245484 : CollatzResearch.WordTrace tailWord_3245484 prefixEnd_3245484 1110995498984456841749531 := by
  unfold tailWord_3245484
  simp only [CollatzResearch.WordTrace]
  refine ⟨59186263087086613691731753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78915017449448818255642337 59186263087086613691731753)
  ·
    refine ⟨44389697315314960268798815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59186263087086613691731753 44389697315314960268798815)
    ·
      refine ⟨66584545972972440403198223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44389697315314960268798815 66584545972972440403198223)
      ·
        refine ⟨99876818959458660604797335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66584545972972440403198223 99876818959458660604797335)
        ·
          refine ⟨149815228439187990907196003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99876818959458660604797335 149815228439187990907196003)
          ·
            refine ⟨224722842658781986360794005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149815228439187990907196003 224722842658781986360794005)
            ·
              refine ⟨10533883249630405610662219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224722842658781986360794005 10533883249630405610662219)
              ·
                refine ⟨15800824874445608415993329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10533883249630405610662219 15800824874445608415993329)
                ·
                  refine ⟨11850618655834206311994997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15800824874445608415993329 11850618655834206311994997)
                  ·
                    refine ⟨1110995498984456841749531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11850618655834206311994997 1110995498984456841749531)
                    ·
                      rfl

theorem cell22_3245484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_3245484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245484 prefixEnd_3245484 := by exact prefixLift 3245484
  have htrace : WordTrace (prefixWord ++ tailWord_3245484) baseStart_3245484 baseEnd_3245484 := by
    simpa [prefixWord, tailWord_3245484, baseEnd_3245484] using wordTrace_append hprefix tailTrace_3245484
  have hstable : (prefixWord ++ tailWord_3245484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245484).length < 2 ^ (prefixWord ++ tailWord_3245484).sum := by decide
  have hdescent : baseEnd_3245484 < baseStart_3245484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245580 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 2, 3]
def baseStart_3245580 : Nat := 118140960795 + 3245580 * 2 ^ 59
def prefixEnd_3245580 : Nat := 4983230072969 + 3 ^ 40 * 3245580 * 2
def baseEnd_3245580 : Nat := 1111028361746344591349237

theorem tailTrace_3245580 : CollatzResearch.WordTrace tailWord_3245580 prefixEnd_3245580 1111028361746344591349237 := by
  unfold tailWord_3245580
  simp only [CollatzResearch.WordTrace]
  refine ⟨59188013790912717889479097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78917351721216957185972129 59188013790912717889479097)
  ·
    refine ⟨44391010343184538417109323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59188013790912717889479097 44391010343184538417109323)
    ·
      refine ⟨66586515514776807625663985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44391010343184538417109323 66586515514776807625663985)
      ·
        refine ⟨49939886636082605719247989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66586515514776807625663985 49939886636082605719247989)
        ·
          refine ⟨4681864372132744286179499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49939886636082605719247989 4681864372132744286179499)
          ·
            refine ⟨7022796558199116429269249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681864372132744286179499 7022796558199116429269249)
            ·
              refine ⟨5267097418649337321951937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7022796558199116429269249 5267097418649337321951937)
              ·
                refine ⟨3950323063987002991463953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267097418649337321951937 3950323063987002991463953)
                ·
                  refine ⟨2962742297990252243597965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950323063987002991463953 2962742297990252243597965)
                  ·
                    refine ⟨1111028361746344591349237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962742297990252243597965 1111028361746344591349237)
                    ·
                      rfl

theorem cell22_3245580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 3].length) (baseStart_3245580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245580 prefixEnd_3245580 := by exact prefixLift 3245580
  have htrace : WordTrace (prefixWord ++ tailWord_3245580) baseStart_3245580 baseEnd_3245580 := by
    simpa [prefixWord, tailWord_3245580, baseEnd_3245580] using wordTrace_append hprefix tailTrace_3245580
  have hstable : (prefixWord ++ tailWord_3245580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245580).length < 2 ^ (prefixWord ++ tailWord_3245580).sum := by decide
  have hdescent : baseEnd_3245580 < baseStart_3245580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245582 : List Nat := [4, 1, 1, 2, 4, 2, 2, 2, 4]
def baseStart_3245582 : Nat := 118140960795 + 3245582 * 2 ^ 59
def prefixEnd_3245582 : Nat := 4983230072969 + 3 ^ 40 * 3245582 * 2
def baseEnd_3245582 : Nat := 370343015462405750933077

theorem tailTrace_3245582 : CollatzResearch.WordTrace tailWord_3245582 prefixEnd_3245582 370343015462405750933077 := by
  unfold tailWord_3245582
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797012565977273765066375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78917400351878793413687333 14797012565977273765066375)
  ·
    refine ⟨22195518848965910647599563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14797012565977273765066375 22195518848965910647599563)
    ·
      refine ⟨33293278273448865971399345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22195518848965910647599563 33293278273448865971399345)
      ·
        refine ⟨24969958705086649478549509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33293278273448865971399345 24969958705086649478549509)
        ·
          refine ⟨4681867257203746777228033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24969958705086649478549509 4681867257203746777228033)
          ·
            refine ⟨3511400442902810082921025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4681867257203746777228033 3511400442902810082921025)
            ·
              refine ⟨2633550332177107562190769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511400442902810082921025 2633550332177107562190769)
              ·
                refine ⟨1975162749132830671643077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633550332177107562190769 1975162749132830671643077)
                ·
                  refine ⟨370343015462405750933077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975162749132830671643077 370343015462405750933077)
                  ·
                    rfl

theorem cell22_3245582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_3245582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245582 prefixEnd_3245582 := by exact prefixLift 3245582
  have htrace : WordTrace (prefixWord ++ tailWord_3245582) baseStart_3245582 baseEnd_3245582 := by
    simpa [prefixWord, tailWord_3245582, baseEnd_3245582] using wordTrace_append hprefix tailTrace_3245582
  have hstable : (prefixWord ++ tailWord_3245582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245582).length < 2 ^ (prefixWord ++ tailWord_3245582).sum := by decide
  have hdescent : baseEnd_3245582 < baseStart_3245582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245625 : List Nat := [1, 2, 1, 5, 1, 2, 1, 5, 1, 3]
def baseStart_3245625 : Nat := 118140960795 + 3245625 * 2 ^ 59
def prefixEnd_3245625 : Nat := 4983230072969 + 3 ^ 40 * 3245625 * 2
def baseEnd_3245625 : Nat := 1111043766165979473974099

theorem tailTrace_3245625 : CollatzResearch.WordTrace tailWord_3245625 prefixEnd_3245625 1111043766165979473974099 := by
  unfold tailWord_3245625
  simp only [CollatzResearch.WordTrace]
  refine ⟨118377668866662408464346329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78918445911108272309564219 118377668866662408464346329)
  ·
    refine ⟨88783251649996806348259747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118377668866662408464346329 88783251649996806348259747)
    ·
      refine ⟨133174877474995209522389621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88783251649996806348259747 133174877474995209522389621)
      ·
        refine ⟨12485144763280800892724027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133174877474995209522389621 12485144763280800892724027)
        ·
          refine ⟨18727717144921201339086041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485144763280800892724027 18727717144921201339086041)
          ·
            refine ⟨14045787858690901004314531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18727717144921201339086041 14045787858690901004314531)
            ·
              refine ⟨21068681788036351506471797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14045787858690901004314531 21068681788036351506471797)
              ·
                refine ⟨1975188917628407953731731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21068681788036351506471797 1975188917628407953731731)
                ·
                  refine ⟨2962783376442611930597597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1975188917628407953731731 2962783376442611930597597)
                  ·
                    refine ⟨1111043766165979473974099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962783376442611930597597 1111043766165979473974099)
                    ·
                      rfl

theorem cell22_3245625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 5, 1, 3].length) (baseStart_3245625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245625 prefixEnd_3245625 := by exact prefixLift 3245625
  have htrace : WordTrace (prefixWord ++ tailWord_3245625) baseStart_3245625 baseEnd_3245625 := by
    simpa [prefixWord, tailWord_3245625, baseEnd_3245625] using wordTrace_append hprefix tailTrace_3245625
  have hstable : (prefixWord ++ tailWord_3245625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245625).length < 2 ^ (prefixWord ++ tailWord_3245625).sum := by decide
  have hdescent : baseEnd_3245625 < baseStart_3245625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245668 : List Nat := [2, 3, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3245668 : Nat := 118140960795 + 3245668 * 2 ^ 59
def prefixEnd_3245668 : Nat := 4983230072969 + 3 ^ 40 * 3245668 * 2
def baseEnd_3245668 : Nat := 1111058485944741695148967

theorem tailTrace_3245668 : CollatzResearch.WordTrace tailWord_3245668 prefixEnd_3245668 1111058485944741695148967 := by
  unfold tailWord_3245668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59189618602753313404080829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78919491470337751205441105 59189618602753313404080829)
  ·
    refine ⟨22196106976032492526530311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59189618602753313404080829 22196106976032492526530311)
    ·
      refine ⟨33294160464048738789795467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22196106976032492526530311 33294160464048738789795467)
      ·
        refine ⟨49941240696073108184693201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33294160464048738789795467 49941240696073108184693201)
        ·
          refine ⟨37455930522054831138519901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49941240696073108184693201 37455930522054831138519901)
          ·
            refine ⟨14045973945770561676944963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37455930522054831138519901 14045973945770561676944963)
            ·
              refine ⟨21068960918655842515417445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14045973945770561676944963 21068960918655842515417445)
              ·
                refine ⟨3950430172247970471640771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21068960918655842515417445 3950430172247970471640771)
                ·
                  refine ⟨5925645258371955707461157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950430172247970471640771 5925645258371955707461157)
                  ·
                    refine ⟨1111058485944741695148967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5925645258371955707461157 1111058485944741695148967)
                    ·
                      rfl

theorem cell22_3245668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3245668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245668 prefixEnd_3245668 := by exact prefixLift 3245668
  have htrace : WordTrace (prefixWord ++ tailWord_3245668) baseStart_3245668 baseEnd_3245668 := by
    simpa [prefixWord, tailWord_3245668, baseEnd_3245668] using wordTrace_append hprefix tailTrace_3245668
  have hstable : (prefixWord ++ tailWord_3245668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245668).length < 2 ^ (prefixWord ++ tailWord_3245668).sum := by decide
  have hdescent : baseEnd_3245668 < baseStart_3245668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245681 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 1, 5]
def baseStart_3245681 : Nat := 118140960795 + 3245681 * 2 ^ 59
def prefixEnd_3245681 : Nat := 4983230072969 + 3 ^ 40 * 3245681 * 2
def baseEnd_3245681 : Nat := 1111062936110413994573927

theorem tailTrace_3245681 : CollatzResearch.WordTrace tailWord_3245681 prefixEnd_3245681 1111062936110413994573927 := by
  unfold tailWord_3245681
  simp only [CollatzResearch.WordTrace]
  refine ⟨118379711354459530028384897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78919807569639686685589931 118379711354459530028384897)
  ·
    refine ⟨88784783515844647521288673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118379711354459530028384897 88784783515844647521288673)
    ·
      refine ⟨66588587636883485640966505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88784783515844647521288673 66588587636883485640966505)
      ·
        refine ⟨49941440727662614230724879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66588587636883485640966505 49941440727662614230724879)
        ·
          refine ⟨74912161091493921346087319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49941440727662614230724879 74912161091493921346087319)
          ·
            refine ⟨112368241637240882019130979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74912161091493921346087319 112368241637240882019130979)
            ·
              refine ⟨168552362455861323028696469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112368241637240882019130979 168552362455861323028696469)
              ·
                refine ⟨7900891990118499516970147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 168552362455861323028696469 7900891990118499516970147)
                ·
                  refine ⟨11851337985177749275455221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7900891990118499516970147 11851337985177749275455221)
                  ·
                    refine ⟨1111062936110413994573927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11851337985177749275455221 1111062936110413994573927)
                    ·
                      rfl

theorem cell22_3245681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_3245681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245681 prefixEnd_3245681 := by exact prefixLift 3245681
  have htrace : WordTrace (prefixWord ++ tailWord_3245681) baseStart_3245681 baseEnd_3245681 := by
    simpa [prefixWord, tailWord_3245681, baseEnd_3245681] using wordTrace_append hprefix tailTrace_3245681
  have hstable : (prefixWord ++ tailWord_3245681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245681).length < 2 ^ (prefixWord ++ tailWord_3245681).sum := by decide
  have hdescent : baseEnd_3245681 < baseStart_3245681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245685 : List Nat := [1, 3, 4, 2, 1, 1, 2, 3, 1, 4]
def baseStart_3245685 : Nat := 118140960795 + 3245685 * 2 ^ 59
def prefixEnd_3245685 : Nat := 4983230072969 + 3 ^ 40 * 3245685 * 2
def baseEnd_3245685 : Nat := 1111064305392159317473915

theorem tailTrace_3245685 : CollatzResearch.WordTrace tailWord_3245685 prefixEnd_3245685 1111064305392159317473915 := by
  unfold tailWord_3245685
  simp only [CollatzResearch.WordTrace]
  refine ⟨118379857246445038711530509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78919904830963359141020339 118379857246445038711530509)
  ·
    refine ⟨44392446467416889516823941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118379857246445038711530509 44392446467416889516823941)
    ·
      refine ⟨8323583712640666784404489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44392446467416889516823941 8323583712640666784404489)
      ·
        refine ⟨6242687784480500088303367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8323583712640666784404489 6242687784480500088303367)
        ·
          refine ⟨9364031676720750132455051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242687784480500088303367 9364031676720750132455051)
          ·
            refine ⟨14046047515081125198682577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364031676720750132455051 14046047515081125198682577)
            ·
              refine ⟨10534535636310843899011933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14046047515081125198682577 10534535636310843899011933)
              ·
                refine ⟨3950450863616566462129475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10534535636310843899011933 3950450863616566462129475)
                ·
                  refine ⟨5925676295424849693194213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950450863616566462129475 5925676295424849693194213)
                  ·
                    refine ⟨1111064305392159317473915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5925676295424849693194213 1111064305392159317473915)
                    ·
                      rfl

theorem cell22_3245685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_3245685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245685 prefixEnd_3245685 := by exact prefixLift 3245685
  have htrace : WordTrace (prefixWord ++ tailWord_3245685) baseStart_3245685 baseEnd_3245685 := by
    simpa [prefixWord, tailWord_3245685, baseEnd_3245685] using wordTrace_append hprefix tailTrace_3245685
  have hstable : (prefixWord ++ tailWord_3245685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245685).length < 2 ^ (prefixWord ++ tailWord_3245685).sum := by decide
  have hdescent : baseEnd_3245685 < baseStart_3245685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245700 : List Nat := [2, 3, 2, 1, 4, 2, 1, 1, 6]
def baseStart_3245700 : Nat := 118140960795 + 3245700 * 2 ^ 59
def prefixEnd_3245700 : Nat := 4983230072969 + 3 ^ 40 * 3245700 * 2
def baseEnd_3245700 : Nat := 370356480066234759449623

theorem tailTrace_3245700 : CollatzResearch.WordTrace tailWord_3245700 prefixEnd_3245700 370356480066234759449623 := by
  unfold tailWord_3245700
  simp only [CollatzResearch.WordTrace]
  refine ⟨59190202170695348136663277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78920269560927130848884369 59190202170695348136663277)
  ·
    refine ⟨22196325814010755551248729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59190202170695348136663277 22196325814010755551248729)
    ·
      refine ⟨16647244360508066663436547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22196325814010755551248729 16647244360508066663436547)
      ·
        refine ⟨24970866540762099995154821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16647244360508066663436547 24970866540762099995154821)
        ·
          refine ⟨4682037476392893749091529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24970866540762099995154821 4682037476392893749091529)
          ·
            refine ⟨3511528107294670311818647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4682037476392893749091529 3511528107294670311818647)
            ·
              refine ⟨5267292160942005467727971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511528107294670311818647 5267292160942005467727971)
              ·
                refine ⟨7900938241413008201591957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267292160942005467727971 7900938241413008201591957)
                ·
                  refine ⟨370356480066234759449623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7900938241413008201591957 370356480066234759449623)
                  ·
                    rfl

theorem cell22_3245700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 6].length) (baseStart_3245700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245700 prefixEnd_3245700 := by exact prefixLift 3245700
  have htrace : WordTrace (prefixWord ++ tailWord_3245700) baseStart_3245700 baseEnd_3245700 := by
    simpa [prefixWord, tailWord_3245700, baseEnd_3245700] using wordTrace_append hprefix tailTrace_3245700
  have hstable : (prefixWord ++ tailWord_3245700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245700).length < 2 ^ (prefixWord ++ tailWord_3245700).sum := by decide
  have hdescent : baseEnd_3245700 < baseStart_3245700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245736 : List Nat := [2, 1, 7, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3245736 : Nat := 118140960795 + 3245736 * 2 ^ 59
def prefixEnd_3245736 : Nat := 4983230072969 + 3 ^ 40 * 3245736 * 2
def baseEnd_3245736 : Nat := 1111081763734412184448759

theorem tailTrace_3245736 : CollatzResearch.WordTrace tailWord_3245736 prefixEnd_3245736 1111081763734412184448759 := by
  unfold tailWord_3245736
  simp only [CollatzResearch.WordTrace]
  refine ⟨59190858684630137210818531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78921144912840182947758041 59190858684630137210818531)
  ·
    refine ⟨88786288026945205816227797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59190858684630137210818531 88786288026945205816227797)
    ·
      refine ⟨2080928625631528261317839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 88786288026945205816227797 2080928625631528261317839)
      ·
        refine ⟨3121392938447292391976759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080928625631528261317839 3121392938447292391976759)
        ·
          refine ⟨4682089407670938587965139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3121392938447292391976759 4682089407670938587965139)
          ·
            refine ⟨7023134111506407881947709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682089407670938587965139 7023134111506407881947709)
            ·
              refine ⟨2633675291814902955730391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7023134111506407881947709 2633675291814902955730391)
              ·
                refine ⟨3950512937722354433595587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2633675291814902955730391 3950512937722354433595587)
                ·
                  refine ⟨5925769406583531650393381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950512937722354433595587 5925769406583531650393381)
                  ·
                    refine ⟨1111081763734412184448759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5925769406583531650393381 1111081763734412184448759)
                    ·
                      rfl

theorem cell22_3245736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3245736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245736 prefixEnd_3245736 := by exact prefixLift 3245736
  have htrace : WordTrace (prefixWord ++ tailWord_3245736) baseStart_3245736 baseEnd_3245736 := by
    simpa [prefixWord, tailWord_3245736, baseEnd_3245736] using wordTrace_append hprefix tailTrace_3245736
  have hstable : (prefixWord ++ tailWord_3245736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245736).length < 2 ^ (prefixWord ++ tailWord_3245736).sum := by decide
  have hdescent : baseEnd_3245736 < baseStart_3245736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245758 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3245758 : Nat := 118140960795 + 3245758 * 2 ^ 59
def prefixEnd_3245758 : Nat := 4983230072969 + 3 ^ 40 * 3245758 * 2
def baseEnd_3245758 : Nat := 1111089294784011460398691

theorem tailTrace_3245758 : CollatzResearch.WordTrace tailWord_3245758 prefixEnd_3245758 1111089294784011460398691 := by
  unfold tailWord_3245758
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797814971897571522367241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78921679850120381452625285 14797814971897571522367241)
  ·
    refine ⟨11098361228923178641775431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14797814971897571522367241 11098361228923178641775431)
    ·
      refine ⟨16647541843384767962663147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11098361228923178641775431 16647541843384767962663147)
      ·
        refine ⟨24971312765077151943994721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16647541843384767962663147 24971312765077151943994721)
        ·
          refine ⟨18728484573807863957996041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24971312765077151943994721 18728484573807863957996041)
          ·
            refine ⟨14046363430355897968497031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18728484573807863957996041 14046363430355897968497031)
            ·
              refine ⟨21069545145533846952745547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14046363430355897968497031 21069545145533846952745547)
              ·
                refine ⟨31604317718300770429118321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21069545145533846952745547 31604317718300770429118321)
                ·
                  refine ⟨23703238288725577821838741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31604317718300770429118321 23703238288725577821838741)
                  ·
                    refine ⟨1111089294784011460398691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23703238288725577821838741 1111089294784011460398691)
                    ·
                      rfl

theorem cell22_3245758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3245758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245758 prefixEnd_3245758 := by exact prefixLift 3245758
  have htrace : WordTrace (prefixWord ++ tailWord_3245758) baseStart_3245758 baseEnd_3245758 := by
    simpa [prefixWord, tailWord_3245758, baseEnd_3245758] using wordTrace_append hprefix tailTrace_3245758
  have hstable : (prefixWord ++ tailWord_3245758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245758).length < 2 ^ (prefixWord ++ tailWord_3245758).sum := by decide
  have hdescent : baseEnd_3245758 < baseStart_3245758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245801 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 10]
def baseStart_3245801 : Nat := 118140960795 + 3245801 * 2 ^ 59
def prefixEnd_3245801 : Nat := 4983230072969 + 3 ^ 40 * 3245801 * 2
def baseEnd_3245801 : Nat := 370368004854257893857853

theorem tailTrace_3245801 : CollatzResearch.WordTrace tailWord_3245801 prefixEnd_3245801 370368004854257893857853 := by
  unfold tailWord_3245801
  simp only [CollatzResearch.WordTrace]
  refine ⟨118384088114024790522753257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78922725409349860348502171 118384088114024790522753257)
  ·
    refine ⟨88788066085518592892064943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118384088114024790522753257 88788066085518592892064943)
    ·
      refine ⟨133182099128277889338097415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88788066085518592892064943 133182099128277889338097415)
      ·
        refine ⟨199773148692416834007146123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133182099128277889338097415 199773148692416834007146123)
        ·
          refine ⟨299659723038625251010719185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199773148692416834007146123 299659723038625251010719185)
          ·
            refine ⟨224744792278968938258039389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299659723038625251010719185 224744792278968938258039389)
            ·
              refine ⟨84279297104613351846764771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224744792278968938258039389 84279297104613351846764771)
              ·
                refine ⟨126418945656920027770147157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84279297104613351846764771 126418945656920027770147157)
                ·
                  refine ⟨370368004854257893857853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126418945656920027770147157 370368004854257893857853)
                  ·
                    rfl

theorem cell22_3245801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_3245801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245801 prefixEnd_3245801 := by exact prefixLift 3245801
  have htrace : WordTrace (prefixWord ++ tailWord_3245801) baseStart_3245801 baseEnd_3245801 := by
    simpa [prefixWord, tailWord_3245801, baseEnd_3245801] using wordTrace_append hprefix tailTrace_3245801
  have hstable : (prefixWord ++ tailWord_3245801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245801).length < 2 ^ (prefixWord ++ tailWord_3245801).sum := by decide
  have hdescent : baseEnd_3245801 < baseStart_3245801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245830 : List Nat := [6, 2, 2, 1, 2, 1, 2, 6]
def baseStart_3245830 : Nat := 118140960795 + 3245830 * 2 ^ 59
def prefixEnd_3245830 : Nat := 4983230072969 + 3 ^ 40 * 3245830 * 2
def baseEnd_3245830 : Nat := 123457104650603030288719

theorem tailTrace_3245830 : CollatzResearch.WordTrace tailWord_3245830 prefixEnd_3245830 123457104650603030288719 := by
  unfold tailWord_3245830
  simp only [CollatzResearch.WordTrace]
  refine ⟨3699535807216241514861217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 78923430553946485650372629 3699535807216241514861217)
  ·
    refine ⟨2774651855412181136145913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3699535807216241514861217 2774651855412181136145913)
    ·
      refine ⟨2080988891559135852109435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2774651855412181136145913 2080988891559135852109435)
      ·
        refine ⟨3121483337338703778164153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080988891559135852109435 3121483337338703778164153)
        ·
          refine ⟨2341112503004027833623115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121483337338703778164153 2341112503004027833623115)
          ·
            refine ⟨3511668754506041750434673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341112503004027833623115 3511668754506041750434673)
            ·
              refine ⟨2633751565879531312826005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3511668754506041750434673 2633751565879531312826005)
              ·
                refine ⟨123457104650603030288719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2633751565879531312826005 123457104650603030288719)
                ·
                  rfl

theorem cell22_3245830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_3245830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245830 prefixEnd_3245830 := by exact prefixLift 3245830
  have htrace : WordTrace (prefixWord ++ tailWord_3245830) baseStart_3245830 baseEnd_3245830 := by
    simpa [prefixWord, tailWord_3245830, baseEnd_3245830] using wordTrace_append hprefix tailTrace_3245830
  have hstable : (prefixWord ++ tailWord_3245830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245830).length < 2 ^ (prefixWord ++ tailWord_3245830).sum := by decide
  have hdescent : baseEnd_3245830 < baseStart_3245830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245848 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 1, 6]
def baseStart_3245848 : Nat := 118140960795 + 3245848 * 2 ^ 59
def prefixEnd_3245848 : Nat := 4983230072969 + 3 ^ 40 * 3245848 * 2
def baseEnd_3245848 : Nat := 1111120103623281225648415

theorem tailTrace_3245848 : CollatzResearch.WordTrace tailWord_3245848 prefixEnd_3245848 1111120103623281225648415 := by
  unfold tailWord_3245848
  simp only [CollatzResearch.WordTrace]
  refine ⟨59192901172427258774857099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78923868229903011699809465 59192901172427258774857099)
  ·
    refine ⟨88789351758640888162285649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59192901172427258774857099 88789351758640888162285649)
    ·
      refine ⟨66592013818980666121714237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88789351758640888162285649 66592013818980666121714237)
      ·
        refine ⟨24972005182117749795642839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66592013818980666121714237 24972005182117749795642839)
        ·
          refine ⟨37458007773176624693464259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24972005182117749795642839 37458007773176624693464259)
          ·
            refine ⟨56187011659764937040196389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37458007773176624693464259 56187011659764937040196389)
            ·
              refine ⟨10535064686205925695036823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56187011659764937040196389 10535064686205925695036823)
              ·
                refine ⟨15802597029308888542555235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10535064686205925695036823 15802597029308888542555235)
                ·
                  refine ⟨23703895543963332813832853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15802597029308888542555235 23703895543963332813832853)
                  ·
                    refine ⟨1111120103623281225648415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23703895543963332813832853 1111120103623281225648415)
                    ·
                      rfl

theorem cell22_3245848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_3245848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245848 prefixEnd_3245848 := by exact prefixLift 3245848
  have htrace : WordTrace (prefixWord ++ tailWord_3245848) baseStart_3245848 baseEnd_3245848 := by
    simpa [prefixWord, tailWord_3245848, baseEnd_3245848] using wordTrace_append hprefix tailTrace_3245848
  have hstable : (prefixWord ++ tailWord_3245848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245848).length < 2 ^ (prefixWord ++ tailWord_3245848).sum := by decide
  have hdescent : baseEnd_3245848 < baseStart_3245848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245850 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_3245850 : Nat := 118140960795 + 3245850 * 2 ^ 59
def prefixEnd_3245850 : Nat := 4983230072969 + 3 ^ 40 * 3245850 * 2
def baseEnd_3245850 : Nat := 1111120788264153887098409

theorem tailTrace_3245850 : CollatzResearch.WordTrace tailWord_3245850 prefixEnd_3245850 1111120788264153887098409 := by
  unfold tailWord_3245850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29596468822711817972821751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78923916860564847927524669 29596468822711817972821751)
  ·
    refine ⟨44394703234067726959232627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29596468822711817972821751 44394703234067726959232627)
    ·
      refine ⟨66592054851101590438848941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44394703234067726959232627 66592054851101590438848941)
      ·
        refine ⟨24972020569163096414568353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66592054851101590438848941 24972020569163096414568353)
        ·
          refine ⟨18729015426872322310926265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24972020569163096414568353 18729015426872322310926265)
          ·
            refine ⟨14046761570154241733194699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18729015426872322310926265 14046761570154241733194699)
            ·
              refine ⟨21070142355231362599792049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14046761570154241733194699 21070142355231362599792049)
              ·
                refine ⟨15802606766423521949844037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21070142355231362599792049 15802606766423521949844037)
                ·
                  refine ⟨2962988768704410365595757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15802606766423521949844037 2962988768704410365595757)
                  ·
                    refine ⟨1111120788264153887098409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2962988768704410365595757 1111120788264153887098409)
                    ·
                      rfl

theorem cell22_3245850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_3245850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245850 prefixEnd_3245850 := by exact prefixLift 3245850
  have htrace : WordTrace (prefixWord ++ tailWord_3245850) baseStart_3245850 baseEnd_3245850 := by
    simpa [prefixWord, tailWord_3245850, baseEnd_3245850] using wordTrace_append hprefix tailTrace_3245850
  have hstable : (prefixWord ++ tailWord_3245850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245850).length < 2 ^ (prefixWord ++ tailWord_3245850).sum := by decide
  have hdescent : baseEnd_3245850 < baseStart_3245850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245895 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 3, 3]
def baseStart_3245895 : Nat := 118140960795 + 3245895 * 2 ^ 59
def prefixEnd_3245895 : Nat := 4983230072969 + 3 ^ 40 * 3245895 * 2
def baseEnd_3245895 : Nat := 1111136192683788769723271

theorem tailTrace_3245895 : CollatzResearch.WordTrace tailWord_3245895 prefixEnd_3245895 1111136192683788769723271 := by
  unfold tailWord_3245895
  simp only [CollatzResearch.WordTrace]
  refine ⟨118387516575684244576675139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78925011050456163051116759 118387516575684244576675139)
  ·
    refine ⟨177581274863526366865012709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118387516575684244576675139 177581274863526366865012709)
    ·
      refine ⟨33296489036911193787189883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177581274863526366865012709 33296489036911193787189883)
      ·
        refine ⟨49944733555366790680784825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33296489036911193787189883 49944733555366790680784825)
        ·
          refine ⟨37458550166525093010588619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49944733555366790680784825 37458550166525093010588619)
          ·
            refine ⟨56187825249787639515882929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37458550166525093010588619 56187825249787639515882929)
            ·
              refine ⟨42140868937340729636912197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56187825249787639515882929 42140868937340729636912197)
              ·
                refine ⟨7901412925751386806921037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42140868937340729636912197 7901412925751386806921037)
                ·
                  refine ⟨2963029847156770052595389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7901412925751386806921037 2963029847156770052595389)
                  ·
                    refine ⟨1111136192683788769723271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963029847156770052595389 1111136192683788769723271)
                    ·
                      rfl

theorem cell22_3245895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_3245895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245895 prefixEnd_3245895 := by exact prefixLift 3245895
  have htrace : WordTrace (prefixWord ++ tailWord_3245895) baseStart_3245895 baseEnd_3245895 := by
    simpa [prefixWord, tailWord_3245895, baseEnd_3245895] using wordTrace_append hprefix tailTrace_3245895
  have hstable : (prefixWord ++ tailWord_3245895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245895).length < 2 ^ (prefixWord ++ tailWord_3245895).sum := by decide
  have hdescent : baseEnd_3245895 < baseStart_3245895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245955 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_3245955 : Nat := 118140960795 + 3245955 * 2 ^ 59
def prefixEnd_3245955 : Nat := 4983230072969 + 3 ^ 40 * 3245955 * 2
def baseEnd_3245955 : Nat := 1111156731909968613223087

theorem tailTrace_3245955 : CollatzResearch.WordTrace tailWord_3245955 prefixEnd_3245955 1111156731909968613223087 := by
  unfold tailWord_3245955
  simp only [CollatzResearch.WordTrace]
  refine ⟨118389704955466874823859319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78926469970311249882572879 118389704955466874823859319)
  ·
    refine ⟨177584557433200312235788979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118389704955466874823859319 177584557433200312235788979)
    ·
      refine ⟨266376836149800468353683469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177584557433200312235788979 266376836149800468353683469)
      ·
        refine ⟨99891313556175175632631301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266376836149800468353683469 99891313556175175632631301)
        ·
          refine ⟨18729621291782845431118369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99891313556175175632631301 18729621291782845431118369)
          ·
            refine ⟨14047215968837134073338777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18729621291782845431118369 14047215968837134073338777)
            ·
              refine ⟨10535411976627850555004083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14047215968837134073338777 10535411976627850555004083)
              ·
                refine ⟨15803117964941775832506125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10535411976627850555004083 15803117964941775832506125)
                ·
                  refine ⟨5926169236853165937189797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15803117964941775832506125 5926169236853165937189797)
                  ·
                    refine ⟨1111156731909968613223087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926169236853165937189797 1111156731909968613223087)
                    ·
                      rfl

theorem cell22_3245955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_3245955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245955 prefixEnd_3245955 := by exact prefixLift 3245955
  have htrace : WordTrace (prefixWord ++ tailWord_3245955) baseStart_3245955 baseEnd_3245955 := by
    simpa [prefixWord, tailWord_3245955, baseEnd_3245955] using wordTrace_append hprefix tailTrace_3245955
  have hstable : (prefixWord ++ tailWord_3245955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245955).length < 2 ^ (prefixWord ++ tailWord_3245955).sum := by decide
  have hdescent : baseEnd_3245955 < baseStart_3245955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3245976 : List Nat := [2, 1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_3245976 : Nat := 118140960795 + 3245976 * 2 ^ 59
def prefixEnd_3245976 : Nat := 4983230072969 + 3 ^ 40 * 3245976 * 2
def baseEnd_3245976 : Nat := 370387973546377186149341

theorem tailTrace_3245976 : CollatzResearch.WordTrace tailWord_3245976 prefixEnd_3245976 370387973546377186149341 := by
  unfold tailWord_3245976
  simp only [CollatzResearch.WordTrace]
  refine ⟨59195235444195397705186891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78926980592260530273582521 59195235444195397705186891)
  ·
    refine ⟨88792853166293096557780337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59195235444195397705186891 88792853166293096557780337)
    ·
      refine ⟨66594639874719822418335253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88792853166293096557780337 66594639874719822418335253)
      ·
        refine ⟨3121623744127491675859465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 66594639874719822418335253 3121623744127491675859465)
        ·
          refine ⟨2341217808095618756894599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3121623744127491675859465 2341217808095618756894599)
          ·
            refine ⟨3511826712143428135341899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341217808095618756894599 3511826712143428135341899)
            ·
              refine ⟨5267740068215142203012849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3511826712143428135341899 5267740068215142203012849)
              ·
                refine ⟨3950805051161356652259637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267740068215142203012849 3950805051161356652259637)
                ·
                  refine ⟨370387973546377186149341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3950805051161356652259637 370387973546377186149341)
                  ·
                    rfl

theorem cell22_3245976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_3245976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3245976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3245976 prefixEnd_3245976 := by exact prefixLift 3245976
  have htrace : WordTrace (prefixWord ++ tailWord_3245976) baseStart_3245976 baseEnd_3245976 := by
    simpa [prefixWord, tailWord_3245976, baseEnd_3245976] using wordTrace_append hprefix tailTrace_3245976
  have hstable : (prefixWord ++ tailWord_3245976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3245976).length < 2 ^ (prefixWord ++ tailWord_3245976).sum := by decide
  have hdescent : baseEnd_3245976 < baseStart_3245976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3245976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246002 : List Nat := [3, 2, 1, 1, 1, 1, 1, 7, 2, 3]
def baseStart_3246002 : Nat := 118140960795 + 3246002 * 2 ^ 59
def prefixEnd_3246002 : Nat := 4983230072969 + 3 ^ 40 * 3246002 * 2
def baseEnd_3246002 : Nat := 1111172820970476157297943

theorem tailTrace_3246002 : CollatzResearch.WordTrace tailWord_3246002 prefixEnd_3246002 1111172820970476157297943 := by
  unfold tailWord_3246002
  simp only [CollatzResearch.WordTrace]
  refine ⟨29597854796574150462705065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78927612790864401233880173 29597854796574150462705065)
  ·
    refine ⟨22198391097430612847028799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29597854796574150462705065 22198391097430612847028799)
    ·
      refine ⟨33297586646145919270543199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22198391097430612847028799 33297586646145919270543199)
      ·
        refine ⟨49946379969218878905814799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33297586646145919270543199 49946379969218878905814799)
        ·
          refine ⟨74919569953828318358722199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49946379969218878905814799 74919569953828318358722199)
          ·
            refine ⟨112379354930742477538083299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74919569953828318358722199 112379354930742477538083299)
            ·
              refine ⟨168569032396113716307124949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112379354930742477538083299 168569032396113716307124949)
              ·
                refine ⟨3950836696783915225948241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 168569032396113716307124949 3950836696783915225948241)
                ·
                  refine ⟨2963127522587936419461181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3950836696783915225948241 2963127522587936419461181)
                  ·
                    refine ⟨1111172820970476157297943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2963127522587936419461181 1111172820970476157297943)
                    ·
                      rfl

theorem cell22_3246002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_3246002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246002 prefixEnd_3246002 := by exact prefixLift 3246002
  have htrace : WordTrace (prefixWord ++ tailWord_3246002) baseStart_3246002 baseEnd_3246002 := by
    simpa [prefixWord, tailWord_3246002, baseEnd_3246002] using wordTrace_append hprefix tailTrace_3246002
  have hstable : (prefixWord ++ tailWord_3246002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246002).length < 2 ^ (prefixWord ++ tailWord_3246002).sum := by decide
  have hdescent : baseEnd_3246002 < baseStart_3246002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246034 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3246034 : Nat := 118140960795 + 3246034 * 2 ^ 59
def prefixEnd_3246034 : Nat := 4983230072969 + 3 ^ 40 * 3246034 * 2
def baseEnd_3246034 : Nat := 1111183775224438740497845

theorem tailTrace_3246034 : CollatzResearch.WordTrace tailWord_3246034 prefixEnd_3246034 1111183775224438740497845 := by
  unfold tailWord_3246034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598146580545167828996289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78928390881453780877323437 29598146580545167828996289)
  ·
    refine ⟨22198609935408875871747217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29598146580545167828996289 22198609935408875871747217)
    ·
      refine ⟨16648957451556656903810413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22198609935408875871747217 16648957451556656903810413)
      ·
        refine ⟨6243359044333746338928905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16648957451556656903810413 6243359044333746338928905)
        ·
          refine ⟨4682519283250309754196679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243359044333746338928905 4682519283250309754196679)
          ·
            refine ⟨7023778924875464631295019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682519283250309754196679 7023778924875464631295019)
            ·
              refine ⟨10535668387313196946942529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7023778924875464631295019 10535668387313196946942529)
              ·
                refine ⟨7901751290484897710206897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10535668387313196946942529 7901751290484897710206897)
                ·
                  refine ⟨5926313467863673282655173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7901751290484897710206897 5926313467863673282655173)
                  ·
                    refine ⟨1111183775224438740497845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926313467863673282655173 1111183775224438740497845)
                    ·
                      rfl

theorem cell22_3246034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3246034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246034 prefixEnd_3246034 := by exact prefixLift 3246034
  have htrace : WordTrace (prefixWord ++ tailWord_3246034) baseStart_3246034 baseEnd_3246034 := by
    simpa [prefixWord, tailWord_3246034, baseEnd_3246034] using wordTrace_append hprefix tailTrace_3246034
  have hstable : (prefixWord ++ tailWord_3246034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246034).length < 2 ^ (prefixWord ++ tailWord_3246034).sum := by decide
  have hdescent : baseEnd_3246034 < baseStart_3246034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246038 : List Nat := [5, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_3246038 : Nat := 118140960795 + 3246038 * 2 ^ 59
def prefixEnd_3246038 : Nat := 4983230072969 + 3 ^ 40 * 3246038 * 2
def baseEnd_3246038 : Nat := 370395048168728021132611

theorem tailTrace_3246038 : CollatzResearch.WordTrace tailWord_3246038 prefixEnd_3246038 370395048168728021132611 := by
  unfold tailWord_3246038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399545763385386249945673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78928488142777453332753845 7399545763385386249945673)
  ·
    refine ⟨5549659322539039687459255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7399545763385386249945673 5549659322539039687459255)
    ·
      refine ⟨8324488983808559531188883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5549659322539039687459255 8324488983808559531188883)
      ·
        refine ⟨12486733475712839296783325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8324488983808559531188883 12486733475712839296783325)
        ·
          refine ⟨4682525053392314736293747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12486733475712839296783325 4682525053392314736293747)
          ·
            refine ⟨7023787580088472104440621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682525053392314736293747 7023787580088472104440621)
            ·
              refine ⟨2633920342533177039165233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7023787580088472104440621 2633920342533177039165233)
              ·
                refine ⟨1975440256899882779373925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633920342533177039165233 1975440256899882779373925)
                ·
                  refine ⟨370395048168728021132611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1975440256899882779373925 370395048168728021132611)
                  ·
                    rfl

theorem cell22_3246038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_3246038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246038 prefixEnd_3246038 := by exact prefixLift 3246038
  have htrace : WordTrace (prefixWord ++ tailWord_3246038) baseStart_3246038 baseEnd_3246038 := by
    simpa [prefixWord, tailWord_3246038, baseEnd_3246038] using wordTrace_append hprefix tailTrace_3246038
  have hstable : (prefixWord ++ tailWord_3246038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246038).length < 2 ^ (prefixWord ++ tailWord_3246038).sum := by decide
  have hdescent : baseEnd_3246038 < baseStart_3246038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246105 : List Nat := [1, 2, 1, 2, 1, 1, 3, 5, 6]
def baseStart_3246105 : Nat := 118140960795 + 3246105 * 2 ^ 59
def prefixEnd_3246105 : Nat := 4983230072969 + 3 ^ 40 * 3246105 * 2
def baseEnd_3246105 : Nat := 370402693325139407324209

theorem tailTrace_3246105 : CollatzResearch.WordTrace tailWord_3246105 prefixEnd_3246105 370402693325139407324209 := by
  unfold tailWord_3246105
  simp only [CollatzResearch.WordTrace]
  refine ⟨118395175904923450441819769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78930117269948966961213179 118395175904923450441819769)
  ·
    refine ⟨88796381928692587831364827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118395175904923450441819769 88796381928692587831364827)
    ·
      refine ⟨133194572893038881747047241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88796381928692587831364827 133194572893038881747047241)
      ·
        refine ⟨99895929669779161310285431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133194572893038881747047241 99895929669779161310285431)
        ·
          refine ⟨149843894504668741965428147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99895929669779161310285431 149843894504668741965428147)
          ·
            refine ⟨224765841757003112948142221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149843894504668741965428147 224765841757003112948142221)
            ·
              refine ⟨84287190658876167355553333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224765841757003112948142221 84287190658876167355553333)
              ·
                refine ⟨7901924124269640689583125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84287190658876167355553333 7901924124269640689583125)
                ·
                  refine ⟨370402693325139407324209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7901924124269640689583125 370402693325139407324209)
                  ·
                    rfl

theorem cell22_3246105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_3246105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246105 prefixEnd_3246105 := by exact prefixLift 3246105
  have htrace : WordTrace (prefixWord ++ tailWord_3246105) baseStart_3246105 baseEnd_3246105 := by
    simpa [prefixWord, tailWord_3246105, baseEnd_3246105] using wordTrace_append hprefix tailTrace_3246105
  have hstable : (prefixWord ++ tailWord_3246105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246105).length < 2 ^ (prefixWord ++ tailWord_3246105).sum := by decide
  have hdescent : baseEnd_3246105 < baseStart_3246105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3246122 : List Nat := [3, 1, 4, 1, 2, 1, 1, 1, 8]
def baseStart_3246122 : Nat := 118140960795 + 3246122 * 2 ^ 59
def prefixEnd_3246122 : Nat := 4983230072969 + 3 ^ 40 * 3246122 * 2
def baseEnd_3246122 : Nat := 370404633140945281432525

theorem tailTrace_3246122 : CollatzResearch.WordTrace tailWord_3246122 prefixEnd_3246122 370404633140945281432525 := by
  unfold tailWord_3246122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29598948986465465586297155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78930530630574574896792413 29598948986465465586297155)
  ·
    refine ⟨44398423479698198379445733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29598948986465465586297155 44398423479698198379445733)
    ·
      refine ⟨8324704402443412196146075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44398423479698198379445733 8324704402443412196146075)
      ·
        refine ⟨12487056603665118294219113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8324704402443412196146075 12487056603665118294219113)
        ·
          refine ⟨9365292452748838720664335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12487056603665118294219113 9365292452748838720664335)
          ·
            refine ⟨14047938679123258080996503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9365292452748838720664335 14047938679123258080996503)
            ·
              refine ⟨21071908018684887121494755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14047938679123258080996503 21071908018684887121494755)
              ·
                refine ⟨31607862028027330682242133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21071908018684887121494755 31607862028027330682242133)
                ·
                  refine ⟨370404633140945281432525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31607862028027330682242133 370404633140945281432525)
                  ·
                    rfl

theorem cell22_3246122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 1, 8].length) (baseStart_3246122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3246122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3246122 prefixEnd_3246122 := by exact prefixLift 3246122
  have htrace : WordTrace (prefixWord ++ tailWord_3246122) baseStart_3246122 baseEnd_3246122 := by
    simpa [prefixWord, tailWord_3246122, baseEnd_3246122] using wordTrace_append hprefix tailTrace_3246122
  have hstable : (prefixWord ++ tailWord_3246122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3246122).length < 2 ^ (prefixWord ++ tailWord_3246122).sum := by decide
  have hdescent : baseEnd_3246122 < baseStart_3246122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3246122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
