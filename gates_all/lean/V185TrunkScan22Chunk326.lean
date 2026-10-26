import V185TrunkScan22Chunk325

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2908900 : List Nat := [2, 3, 1, 1, 1, 5, 2, 3, 4]
def baseStart_2908900 : Nat := 118140960795 + 2908900 * 2 ^ 59
def prefixEnd_2908900 : Nat := 4983230072969 + 3 ^ 40 * 2908900 * 2
def baseEnd_2908900 : Nat := 331925305747505366460493

theorem tailTrace_2908900 : CollatzResearch.WordTrace tailWord_2908900 prefixEnd_2908900 331925305747505366460493 := by
  unfold tailWord_2908900
  simp only [CollatzResearch.WordTrace]
  refine ⟨53048149580779787706398077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70730866107706383608530769 53048149580779787706398077)
  ·
    refine ⟨19893056092792420389899279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53048149580779787706398077 19893056092792420389899279)
    ·
      refine ⟨29839584139188630584848919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19893056092792420389899279 29839584139188630584848919)
      ·
        refine ⟨44759376208782945877273379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29839584139188630584848919 44759376208782945877273379)
        ·
          refine ⟨67139064313174418815910069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44759376208782945877273379 67139064313174418815910069)
          ·
            refine ⟨6294287279360101763991569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67139064313174418815910069 6294287279360101763991569)
            ·
              refine ⟨4720715459520076322993677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6294287279360101763991569 4720715459520076322993677)
              ·
                refine ⟨1770268297320028621122629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720715459520076322993677 1770268297320028621122629)
                ·
                  refine ⟨331925305747505366460493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770268297320028621122629 331925305747505366460493)
                  ·
                    rfl

theorem cell22_2908900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_2908900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908900 prefixEnd_2908900 := by exact prefixLift 2908900
  have htrace : WordTrace (prefixWord ++ tailWord_2908900) baseStart_2908900 baseEnd_2908900 := by
    simpa [prefixWord, tailWord_2908900, baseEnd_2908900] using wordTrace_append hprefix tailTrace_2908900
  have hstable : (prefixWord ++ tailWord_2908900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908900).length < 2 ^ (prefixWord ++ tailWord_2908900).sum := by decide
  have hdescent : baseEnd_2908900 < baseStart_2908900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908911 : List Nat := [1, 1, 2, 1, 5, 3, 9]
def baseStart_2908911 : Nat := 118140960795 + 2908911 * 2 ^ 59
def prefixEnd_2908911 : Nat := 4983230072969 + 3 ^ 40 * 2908911 * 2
def baseEnd_2908911 : Nat := 36880728991382064346535

theorem tailTrace_2908911 : CollatzResearch.WordTrace tailWord_2908911 prefixEnd_2908911 36880728991382064346535 := by
  unfold tailWord_2908911
  simp only [CollatzResearch.WordTrace]
  refine ⟨106096700364519724291446587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70731133576346482860964391 106096700364519724291446587)
  ·
    refine ⟨159145050546779586437169881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106096700364519724291446587 159145050546779586437169881)
    ·
      refine ⟨119358787910084689827877411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159145050546779586437169881 119358787910084689827877411)
      ·
        refine ⟨179038181865127034741816117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119358787910084689827877411 179038181865127034741816117)
        ·
          refine ⟨16784829549855659507045261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179038181865127034741816117 16784829549855659507045261)
          ·
            refine ⟨6294311081195872315141973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16784829549855659507045261 6294311081195872315141973)
            ·
              refine ⟨36880728991382064346535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6294311081195872315141973 36880728991382064346535)
              ·
                rfl

theorem cell22_2908911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 9].length) (baseStart_2908911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908911 prefixEnd_2908911 := by exact prefixLift 2908911
  have htrace : WordTrace (prefixWord ++ tailWord_2908911) baseStart_2908911 baseEnd_2908911 := by
    simpa [prefixWord, tailWord_2908911, baseEnd_2908911] using wordTrace_append hprefix tailTrace_2908911
  have hstable : (prefixWord ++ tailWord_2908911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908911).length < 2 ^ (prefixWord ++ tailWord_2908911).sum := by decide
  have hdescent : baseEnd_2908911 < baseStart_2908911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908932 : List Nat := [2, 3, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_2908932 : Nat := 118140960795 + 2908932 * 2 ^ 59
def prefixEnd_2908932 : Nat := 4983230072969 + 3 ^ 40 * 2908932 * 2
def baseEnd_2908932 : Nat := 995786871496478682581381

theorem tailTrace_2908932 : CollatzResearch.WordTrace tailWord_2908932 prefixEnd_2908932 995786871496478682581381 := by
  unfold tailWord_2908932
  simp only [CollatzResearch.WordTrace]
  refine ⟨53048733148721822438980525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70731644198295763251974033 53048733148721822438980525)
  ·
    refine ⟨19893274930770683414617697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53048733148721822438980525 19893274930770683414617697)
    ·
      refine ⟨14919956198078012560963273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19893274930770683414617697 14919956198078012560963273)
      ·
        refine ⟨11189967148558509420722455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14919956198078012560963273 11189967148558509420722455)
        ·
          refine ⟨16784950722837764131083683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11189967148558509420722455 16784950722837764131083683)
          ·
            refine ⟨25177426084256646196625525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16784950722837764131083683 25177426084256646196625525)
            ·
              refine ⟨2360383695399060580933643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25177426084256646196625525 2360383695399060580933643)
              ·
                refine ⟨3540575543098590871400465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360383695399060580933643 3540575543098590871400465)
                ·
                  refine ⟨2655431657323943153550349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3540575543098590871400465 2655431657323943153550349)
                  ·
                    refine ⟨995786871496478682581381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655431657323943153550349 995786871496478682581381)
                    ·
                      rfl

theorem cell22_2908932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_2908932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908932 prefixEnd_2908932 := by exact prefixLift 2908932
  have htrace : WordTrace (prefixWord ++ tailWord_2908932) baseStart_2908932 baseEnd_2908932 := by
    simpa [prefixWord, tailWord_2908932, baseEnd_2908932] using wordTrace_append hprefix tailTrace_2908932
  have hstable : (prefixWord ++ tailWord_2908932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908932).length < 2 ^ (prefixWord ++ tailWord_2908932).sum := by decide
  have hdescent : baseEnd_2908932 < baseStart_2908932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2908943 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 3, 3]
def baseStart_2908943 : Nat := 118140960795 + 2908943 * 2 ^ 59
def prefixEnd_2908943 : Nat := 4983230072969 + 3 ^ 40 * 2908943 * 2
def baseEnd_2908943 : Nat := 995790637021278320556347

theorem tailTrace_2908943 : CollatzResearch.WordTrace tailWord_2908943 prefixEnd_2908943 995790637021278320556347 := by
  unfold tailWord_2908943
  simp only [CollatzResearch.WordTrace]
  refine ⟨106097867500403793756611483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70731911666935862504407655 106097867500403793756611483)
  ·
    refine ⟨159146801250605690634917225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106097867500403793756611483 159146801250605690634917225)
    ·
      refine ⟨119360100937954267976187919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159146801250605690634917225 119360100937954267976187919)
      ·
        refine ⟨179040151406931401964281879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119360100937954267976187919 179040151406931401964281879)
        ·
          refine ⟨268560227110397102946422819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179040151406931401964281879 268560227110397102946422819)
          ·
            refine ⟨402840340665595654419634229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268560227110397102946422819 402840340665595654419634229)
            ·
              refine ⟨37766281937399592601840709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 402840340665595654419634229 37766281937399592601840709)
              ·
                refine ⟨7081177863262423612845133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37766281937399592601840709 7081177863262423612845133)
                ·
                  refine ⟨2655441698723408854816925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7081177863262423612845133 2655441698723408854816925)
                  ·
                    refine ⟨995790637021278320556347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655441698723408854816925 995790637021278320556347)
                    ·
                      rfl

theorem cell22_2908943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 3].length) (baseStart_2908943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2908943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2908943 prefixEnd_2908943 := by exact prefixLift 2908943
  have htrace : WordTrace (prefixWord ++ tailWord_2908943) baseStart_2908943 baseEnd_2908943 := by
    simpa [prefixWord, tailWord_2908943, baseEnd_2908943] using wordTrace_append hprefix tailTrace_2908943
  have hstable : (prefixWord ++ tailWord_2908943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2908943).length < 2 ^ (prefixWord ++ tailWord_2908943).sum := by decide
  have hdescent : baseEnd_2908943 < baseStart_2908943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2908943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909065 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_2909065 : Nat := 118140960795 + 2909065 * 2 ^ 59
def prefixEnd_2909065 : Nat := 4983230072969 + 3 ^ 40 * 2909065 * 2
def baseEnd_2909065 : Nat := 995832400114510669005973

theorem tailTrace_2909065 : CollatzResearch.WordTrace tailWord_2909065 prefixEnd_2909065 995832400114510669005973 := by
  unfold tailWord_2909065
  simp only [CollatzResearch.WordTrace]
  refine ⟨106102317205961808592552649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70734878137307872395035099 106102317205961808592552649)
  ·
    refine ⟨79576737904471356444414487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106102317205961808592552649 79576737904471356444414487)
    ·
      refine ⟨119365106856707034666621731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79576737904471356444414487 119365106856707034666621731)
      ·
        refine ⟨179047660285060551999932597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119365106856707034666621731 179047660285060551999932597)
        ·
          refine ⟨16785718151724426749993681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179047660285060551999932597 16785718151724426749993681)
          ·
            refine ⟨12589288613793320062495261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16785718151724426749993681 12589288613793320062495261)
            ·
              refine ⟨4720983230172495023435723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12589288613793320062495261 4720983230172495023435723)
              ·
                refine ⟨7081474845258742535153585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4720983230172495023435723 7081474845258742535153585)
                ·
                  refine ⟨5311106133944056901365189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7081474845258742535153585 5311106133944056901365189)
                  ·
                    refine ⟨995832400114510669005973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311106133944056901365189 995832400114510669005973)
                    ·
                      rfl

theorem cell22_2909065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_2909065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909065 prefixEnd_2909065 := by exact prefixLift 2909065
  have htrace : WordTrace (prefixWord ++ tailWord_2909065) baseStart_2909065 baseEnd_2909065 := by
    simpa [prefixWord, tailWord_2909065, baseEnd_2909065] using wordTrace_append hprefix tailTrace_2909065
  have hstable : (prefixWord ++ tailWord_2909065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909065).length < 2 ^ (prefixWord ++ tailWord_2909065).sum := by decide
  have hdescent : baseEnd_2909065 < baseStart_2909065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909101 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2909101 : Nat := 118140960795 + 2909101 * 2 ^ 59
def prefixEnd_2909101 : Nat := 4983230072969 + 3 ^ 40 * 2909101 * 2
def baseEnd_2909101 : Nat := 995844723650218575105863

theorem tailTrace_2909101 : CollatzResearch.WordTrace tailWord_2909101 prefixEnd_2909101 995844723650218575105863 := by
  unfold tailWord_2909101
  simp only [CollatzResearch.WordTrace]
  refine ⟨106103630233831386740863157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70735753489220924493908771 106103630233831386740863157)
  ·
    refine ⟨9947215334421692506955921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106103630233831386740863157 9947215334421692506955921)
    ·
      refine ⟨7460411500816269380216941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9947215334421692506955921 7460411500816269380216941)
      ·
        refine ⟨2797654312806101017581353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7460411500816269380216941 2797654312806101017581353)
        ·
          refine ⟨2098240734604575763186015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2797654312806101017581353 2098240734604575763186015)
          ·
            refine ⟨3147361101906863644779023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098240734604575763186015 3147361101906863644779023)
            ·
              refine ⟨4721041652860295467168535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147361101906863644779023 4721041652860295467168535)
              ·
                refine ⟨7081562479290443200752803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721041652860295467168535 7081562479290443200752803)
                ·
                  refine ⟨10622343718935664801129205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7081562479290443200752803 10622343718935664801129205)
                  ·
                    refine ⟨995844723650218575105863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10622343718935664801129205 995844723650218575105863)
                    ·
                      rfl

theorem cell22_2909101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2909101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909101 prefixEnd_2909101 := by exact prefixLift 2909101
  have htrace : WordTrace (prefixWord ++ tailWord_2909101) baseStart_2909101 baseEnd_2909101 := by
    simpa [prefixWord, tailWord_2909101, baseEnd_2909101] using wordTrace_append hprefix tailTrace_2909101
  have hstable : (prefixWord ++ tailWord_2909101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909101).length < 2 ^ (prefixWord ++ tailWord_2909101).sum := by decide
  have hdescent : baseEnd_2909101 < baseStart_2909101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909142 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2909142 : Nat := 118140960795 + 2909142 * 2 ^ 59
def prefixEnd_2909142 : Nat := 4983230072969 + 3 ^ 40 * 2909142 * 2
def baseEnd_2909142 : Nat := 331952919596036044943579

theorem tailTrace_2909142 : CollatzResearch.WordTrace tailWord_2909142 prefixEnd_2909142 331952919596036044943579 := by
  unfold tailWord_2909142
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631570351667678171444105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70736750417788567162070453 6631570351667678171444105)
  ·
    refine ⟨4973677763750758628583079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6631570351667678171444105 4973677763750758628583079)
    ·
      refine ⟨7460516645626137942874619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973677763750758628583079 7460516645626137942874619)
      ·
        refine ⟨11190774968439206914311929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460516645626137942874619 11190774968439206914311929)
        ·
          refine ⟨8393081226329405185733947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11190774968439206914311929 8393081226329405185733947)
          ·
            refine ⟨12589621839494107778600921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393081226329405185733947 12589621839494107778600921)
            ·
              refine ⟨9442216379620580833950691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12589621839494107778600921 9442216379620580833950691)
              ·
                refine ⟨14163324569430871250926037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9442216379620580833950691 14163324569430871250926037)
                ·
                  refine ⟨331952919596036044943579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14163324569430871250926037 331952919596036044943579)
                  ·
                    rfl

theorem cell22_2909142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2909142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909142 prefixEnd_2909142 := by exact prefixLift 2909142
  have htrace : WordTrace (prefixWord ++ tailWord_2909142) baseStart_2909142 baseEnd_2909142 := by
    simpa [prefixWord, tailWord_2909142, baseEnd_2909142] using wordTrace_append hprefix tailTrace_2909142
  have hstable : (prefixWord ++ tailWord_2909142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909142).length < 2 ^ (prefixWord ++ tailWord_2909142).sum := by decide
  have hdescent : baseEnd_2909142 < baseStart_2909142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909146 : List Nat := [3, 1, 1, 2, 4, 2, 3, 2, 1, 3]
def baseStart_2909146 : Nat := 118140960795 + 2909146 * 2 ^ 59
def prefixEnd_2909146 : Nat := 4983230072969 + 3 ^ 40 * 2909146 * 2
def baseEnd_2909146 : Nat := 995860128069853457730725

theorem tailTrace_2909146 : CollatzResearch.WordTrace tailWord_2909146 prefixEnd_2909146 995860128069853457730725 := by
  unfold tailWord_2909146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26526317879667089856562823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70736847679112239617500861 26526317879667089856562823)
  ·
    refine ⟨39789476819500634784844235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26526317879667089856562823 39789476819500634784844235)
    ·
      refine ⟨59684215229250952177266353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39789476819500634784844235 59684215229250952177266353)
      ·
        refine ⟨44763161421938214132949765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59684215229250952177266353 44763161421938214132949765)
        ·
          refine ⟨8393092766613415149928081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44763161421938214132949765 8393092766613415149928081)
          ·
            refine ⟨6294819574960061362446061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8393092766613415149928081 6294819574960061362446061)
            ·
              refine ⟨2360557340610023010917273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6294819574960061362446061 2360557340610023010917273)
              ·
                refine ⟨1770418005457517258187955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2360557340610023010917273 1770418005457517258187955)
                ·
                  refine ⟨2655627008186275887281933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1770418005457517258187955 2655627008186275887281933)
                  ·
                    refine ⟨995860128069853457730725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655627008186275887281933 995860128069853457730725)
                    ·
                      rfl

theorem cell22_2909146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 2, 1, 3].length) (baseStart_2909146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909146 prefixEnd_2909146 := by exact prefixLift 2909146
  have htrace : WordTrace (prefixWord ++ tailWord_2909146) baseStart_2909146 baseEnd_2909146 := by
    simpa [prefixWord, tailWord_2909146, baseEnd_2909146] using wordTrace_append hprefix tailTrace_2909146
  have hstable : (prefixWord ++ tailWord_2909146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909146).length < 2 ^ (prefixWord ++ tailWord_2909146).sum := by decide
  have hdescent : baseEnd_2909146 < baseStart_2909146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909155 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 3, 4]
def baseStart_2909155 : Nat := 118140960795 + 2909155 * 2 ^ 59
def prefixEnd_2909155 : Nat := 4983230072969 + 3 ^ 40 * 2909155 * 2
def baseEnd_2909155 : Nat := 995863208953780434255697

theorem tailTrace_2909155 : CollatzResearch.WordTrace tailWord_2909155 prefixEnd_2909155 995863208953780434255697 := by
  unfold tailWord_2909155
  simp only [CollatzResearch.WordTrace]
  refine ⟨106105599775635753963328919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70737066517090502642219279 106105599775635753963328919)
  ·
    refine ⟨159158399663453630944993379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106105599775635753963328919 159158399663453630944993379)
    ·
      refine ⟨238737599495180446417490069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159158399663453630944993379 238737599495180446417490069)
      ·
        refine ⟨11190824976336583425819847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 238737599495180446417490069 11190824976336583425819847)
        ·
          refine ⟨16786237464504875138729771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11190824976336583425819847 16786237464504875138729771)
          ·
            refine ⟨25179356196757312708094657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16786237464504875138729771 25179356196757312708094657)
            ·
              refine ⟨18884517147567984531070993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25179356196757312708094657 18884517147567984531070993)
              ·
                refine ⟨14163387860675988398303245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18884517147567984531070993 14163387860675988398303245)
                ·
                  refine ⟨5311270447753495649363717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14163387860675988398303245 5311270447753495649363717)
                  ·
                    refine ⟨995863208953780434255697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311270447753495649363717 995863208953780434255697)
                    ·
                      rfl

theorem cell22_2909155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 3, 4].length) (baseStart_2909155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909155 prefixEnd_2909155 := by exact prefixLift 2909155
  have htrace : WordTrace (prefixWord ++ tailWord_2909155) baseStart_2909155 baseEnd_2909155 := by
    simpa [prefixWord, tailWord_2909155, baseEnd_2909155] using wordTrace_append hprefix tailTrace_2909155
  have hstable : (prefixWord ++ tailWord_2909155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909155).length < 2 ^ (prefixWord ++ tailWord_2909155).sum := by decide
  have hdescent : baseEnd_2909155 < baseStart_2909155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909159 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 5]
def baseStart_2909159 : Nat := 118140960795 + 2909159 * 2 ^ 59
def prefixEnd_2909159 : Nat := 4983230072969 + 3 ^ 40 * 2909159 * 2
def baseEnd_2909159 : Nat := 331954859411841919051895

theorem tailTrace_2909159 : CollatzResearch.WordTrace tailWord_2909159 prefixEnd_2909159 331954859411841919051895 := by
  unfold tailWord_2909159
  simp only [CollatzResearch.WordTrace]
  refine ⟨106105745667621262646474531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70737163778414175097649687 106105745667621262646474531)
  ·
    refine ⟨159158618501431893969711797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106105745667621262646474531 159158618501431893969711797)
    ·
      refine ⟨14921120484509240059660481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159158618501431893969711797 14921120484509240059660481)
      ·
        refine ⟨11190840363381930044745361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14921120484509240059660481 11190840363381930044745361)
        ·
          refine ⟨8393130272536447533559021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11190840363381930044745361 8393130272536447533559021)
          ·
            refine ⟨3147423852201167825084633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8393130272536447533559021 3147423852201167825084633)
            ·
              refine ⟨2360567889150875868813475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3147423852201167825084633 2360567889150875868813475)
              ·
                refine ⟨3540851833726313803220213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360567889150875868813475 3540851833726313803220213)
                ·
                  refine ⟨331954859411841919051895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3540851833726313803220213 331954859411841919051895)
                  ·
                    rfl

theorem cell22_2909159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 5].length) (baseStart_2909159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909159 prefixEnd_2909159 := by exact prefixLift 2909159
  have htrace : WordTrace (prefixWord ++ tailWord_2909159) baseStart_2909159 baseEnd_2909159 := by
    simpa [prefixWord, tailWord_2909159, baseEnd_2909159] using wordTrace_append hprefix tailTrace_2909159
  have hstable : (prefixWord ++ tailWord_2909159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909159).length < 2 ^ (prefixWord ++ tailWord_2909159).sum := by decide
  have hdescent : baseEnd_2909159 < baseStart_2909159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909185 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2909185 : Nat := 118140960795 + 2909185 * 2 ^ 59
def prefixEnd_2909185 : Nat := 4983230072969 + 3 ^ 40 * 2909185 * 2
def baseEnd_2909185 : Nat := 995873478566870356005605

theorem tailTrace_2909185 : CollatzResearch.WordTrace tailWord_2909185 prefixEnd_2909185 995873478566870356005605 := by
  unfold tailWord_2909185
  simp only [CollatzResearch.WordTrace]
  refine ⟨106106693965527069086921009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70737795977018046057947339 106106693965527069086921009)
  ·
    refine ⟨79580020474145301815190757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106106693965527069086921009 79580020474145301815190757)
    ·
      refine ⟨14921253838902244090348267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79580020474145301815190757 14921253838902244090348267)
      ·
        refine ⟨22381880758353366135522401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921253838902244090348267 22381880758353366135522401)
        ·
          refine ⟨16786410568765024601641801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22381880758353366135522401 16786410568765024601641801)
          ·
            refine ⟨12589807926573768451231351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16786410568765024601641801 12589807926573768451231351)
            ·
              refine ⟨18884711889860652676847027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12589807926573768451231351 18884711889860652676847027)
              ·
                refine ⟨28327067834790979015270541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18884711889860652676847027 28327067834790979015270541)
                ·
                  refine ⟨10622650438046617130726453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28327067834790979015270541 10622650438046617130726453)
                  ·
                    refine ⟨995873478566870356005605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10622650438046617130726453 995873478566870356005605)
                    ·
                      rfl

theorem cell22_2909185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2909185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909185 prefixEnd_2909185 := by exact prefixLift 2909185
  have htrace : WordTrace (prefixWord ++ tailWord_2909185) baseStart_2909185 baseEnd_2909185 := by
    simpa [prefixWord, tailWord_2909185, baseEnd_2909185] using wordTrace_append hprefix tailTrace_2909185
  have hstable : (prefixWord ++ tailWord_2909185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909185).length < 2 ^ (prefixWord ++ tailWord_2909185).sum := by decide
  have hdescent : baseEnd_2909185 < baseStart_2909185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909215 : List Nat := [1, 1, 2, 4, 1, 3, 3, 7]
def baseStart_2909215 : Nat := 118140960795 + 2909215 * 2 ^ 59
def prefixEnd_2909215 : Nat := 4983230072969 + 3 ^ 40 * 2909215 * 2
def baseEnd_2909215 : Nat := 110653749797773364195057

theorem tailTrace_2909215 : CollatzResearch.WordTrace tailWord_2909215 prefixEnd_2909215 110653749797773364195057 := by
  unfold tailWord_2909215
  simp only [CollatzResearch.WordTrace]
  refine ⟨106107788155418384210513099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70738525436945589473675399 106107788155418384210513099)
  ·
    refine ⟨159161682233127576315769649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106107788155418384210513099 159161682233127576315769649)
    ·
      refine ⟨119371261674845682236827237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159161682233127576315769649 119371261674845682236827237)
      ·
        refine ⟨22382111564033565419405107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119371261674845682236827237 22382111564033565419405107)
        ·
          refine ⟨33573167346050348129107661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22382111564033565419405107 33573167346050348129107661)
          ·
            refine ⟨12589937754768880548415373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33573167346050348129107661 12589937754768880548415373)
            ·
              refine ⟨4721226658038330205655765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12589937754768880548415373 4721226658038330205655765)
              ·
                refine ⟨110653749797773364195057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4721226658038330205655765 110653749797773364195057)
                ·
                  rfl

theorem cell22_2909215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 7].length) (baseStart_2909215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909215 prefixEnd_2909215 := by exact prefixLift 2909215
  have htrace : WordTrace (prefixWord ++ tailWord_2909215) baseStart_2909215 baseEnd_2909215 := by
    simpa [prefixWord, tailWord_2909215, baseEnd_2909215] using wordTrace_append hprefix tailTrace_2909215
  have hstable : (prefixWord ++ tailWord_2909215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909215).length < 2 ^ (prefixWord ++ tailWord_2909215).sum := by decide
  have hdescent : baseEnd_2909215 < baseStart_2909215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909270 : List Nat := [5, 2, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2909270 : Nat := 118140960795 + 2909270 * 2 ^ 59
def prefixEnd_2909270 : Nat := 4983230072969 + 3 ^ 40 * 2909270 * 2
def baseEnd_2909270 : Nat := 995902575803958467630345

theorem tailTrace_2909270 : CollatzResearch.WordTrace tailWord_2909270 prefixEnd_2909270 995902575803958467630345 := by
  unfold tailWord_2909270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631862135638695537735329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70739862780146085735843509 6631862135638695537735329)
  ·
    refine ⟨4973896601729021653301497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6631862135638695537735329 4973896601729021653301497)
    ·
      refine ⟨3730422451296766239976123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4973896601729021653301497 3730422451296766239976123)
      ·
        refine ⟨5595633676945149359964185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3730422451296766239976123 5595633676945149359964185)
        ·
          refine ⟨4196725257708862019973139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5595633676945149359964185 4196725257708862019973139)
          ·
            refine ⟨6295087886563293029959709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4196725257708862019973139 6295087886563293029959709)
            ·
              refine ⟨2360657957461234886234891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6295087886563293029959709 2360657957461234886234891)
              ·
                refine ⟨3540986936191852329352337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360657957461234886234891 3540986936191852329352337)
                ·
                  refine ⟨2655740202143889247014253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3540986936191852329352337 2655740202143889247014253)
                  ·
                    refine ⟨995902575803958467630345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2655740202143889247014253 995902575803958467630345)
                    ·
                      rfl

theorem cell22_2909270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2909270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909270 prefixEnd_2909270 := by exact prefixLift 2909270
  have htrace : WordTrace (prefixWord ++ tailWord_2909270) baseStart_2909270 baseEnd_2909270 := by
    simpa [prefixWord, tailWord_2909270, baseEnd_2909270] using wordTrace_append hprefix tailTrace_2909270
  have hstable : (prefixWord ++ tailWord_2909270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909270).length < 2 ^ (prefixWord ++ tailWord_2909270).sum := by decide
  have hdescent : baseEnd_2909270 < baseStart_2909270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909354 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2909354 : Nat := 118140960795 + 2909354 * 2 ^ 59
def prefixEnd_2909354 : Nat := 4983230072969 + 3 ^ 40 * 2909354 * 2
def baseEnd_2909354 : Nat := 995931330720610248530087

theorem tailTrace_2909354 : CollatzResearch.WordTrace tailWord_2909354 prefixEnd_2909354 995931330720610248530087 := by
  unfold tailWord_2909354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528214475478702737455779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70741905267943207299882077 26528214475478702737455779)
  ·
    refine ⟨39792321713218054106183669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26528214475478702737455779 39792321713218054106183669)
    ·
      refine ⟨3730530160614192572454719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39792321713218054106183669 3730530160614192572454719)
      ·
        refine ⟨5595795240921288858682079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3730530160614192572454719 5595795240921288858682079)
        ·
          refine ⟨8393692861381933288023119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5595795240921288858682079 8393692861381933288023119)
          ·
            refine ⟨12590539292072899932034679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393692861381933288023119 12590539292072899932034679)
            ·
              refine ⟨18885808938109349898052019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590539292072899932034679 18885808938109349898052019)
              ·
                refine ⟨28328713407164024847078029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18885808938109349898052019 28328713407164024847078029)
                ·
                  refine ⟨10623267527686509317654261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28328713407164024847078029 10623267527686509317654261)
                  ·
                    refine ⟨995931330720610248530087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10623267527686509317654261 995931330720610248530087)
                    ·
                      rfl

theorem cell22_2909354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2909354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909354 prefixEnd_2909354 := by exact prefixLift 2909354
  have htrace : WordTrace (prefixWord ++ tailWord_2909354) baseStart_2909354 baseEnd_2909354 := by
    simpa [prefixWord, tailWord_2909354, baseEnd_2909354] using wordTrace_append hprefix tailTrace_2909354
  have hstable : (prefixWord ++ tailWord_2909354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909354).length < 2 ^ (prefixWord ++ tailWord_2909354).sum := by decide
  have hdescent : baseEnd_2909354 < baseStart_2909354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909427 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 2, 5]
def baseStart_2909427 : Nat := 118140960795 + 2909427 * 2 ^ 59
def prefixEnd_2909427 : Nat := 4983230072969 + 3 ^ 40 * 2909427 * 2
def baseEnd_2909427 : Nat := 995956320112462391454863

theorem tailTrace_2909427 : CollatzResearch.WordTrace tailWord_2909427 prefixEnd_2909427 995956320112462391454863 := by
  unfold tailWord_2909427
  simp only [CollatzResearch.WordTrace]
  refine ⟨106115520430650344417230535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70743680287100229611487023 106115520430650344417230535)
  ·
    refine ⟨159173280645975516625845803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106115520430650344417230535 159173280645975516625845803)
    ·
      refine ⟨238759920968963274938768705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159173280645975516625845803 238759920968963274938768705)
      ·
        refine ⟨179069940726722456204076529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 238759920968963274938768705 179069940726722456204076529)
        ·
          refine ⟨134302455545041842153057397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179069940726722456204076529 134302455545041842153057397)
          ·
            refine ⟨12590855207347672701849131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134302455545041842153057397 12590855207347672701849131)
            ·
              refine ⟨18886282811021509052773697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12590855207347672701849131 18886282811021509052773697)
              ·
                refine ⟨14164712108266131789580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18886282811021509052773697 14164712108266131789580273)
                ·
                  refine ⟨10623534081199598842185205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14164712108266131789580273 10623534081199598842185205)
                  ·
                    refine ⟨995956320112462391454863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10623534081199598842185205 995956320112462391454863)
                    ·
                      rfl

theorem cell22_2909427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 5].length) (baseStart_2909427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909427 prefixEnd_2909427 := by exact prefixLift 2909427
  have htrace : WordTrace (prefixWord ++ tailWord_2909427) baseStart_2909427 baseEnd_2909427 := by
    simpa [prefixWord, tailWord_2909427, baseEnd_2909427] using wordTrace_append hprefix tailTrace_2909427
  have hstable : (prefixWord ++ tailWord_2909427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909427).length < 2 ^ (prefixWord ++ tailWord_2909427).sum := by decide
  have hdescent : baseEnd_2909427 < baseStart_2909427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909444 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_2909444 : Nat := 118140960795 + 2909444 * 2 ^ 59
def prefixEnd_2909444 : Nat := 4983230072969 + 3 ^ 40 * 2909444 * 2
def baseEnd_2909444 : Nat := 995962139559880013779811

theorem tailTrace_2909444 : CollatzResearch.WordTrace tailWord_2909444 prefixEnd_2909444 995962139559880013779811 := by
  unfold tailWord_2909444
  simp only [CollatzResearch.WordTrace]
  refine ⟨53058070235794378160299693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70744093647725837547066257 53058070235794378160299693)
  ·
    refine ⟨19896776338422891810112385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53058070235794378160299693 19896776338422891810112385)
    ·
      refine ⟨14922582253817168857584289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19896776338422891810112385 14922582253817168857584289)
      ·
        refine ⟨11191936690362876643188217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14922582253817168857584289 11191936690362876643188217)
        ·
          refine ⟨8393952517772157482391163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11191936690362876643188217 8393952517772157482391163)
          ·
            refine ⟨12590928776658236223586745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393952517772157482391163 12590928776658236223586745)
            ·
              refine ⟨9443196582493677167690059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12590928776658236223586745 9443196582493677167690059)
              ·
                refine ⟨14164794873740515751535089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9443196582493677167690059 14164794873740515751535089)
                ·
                  refine ⟨10623596155305386813651317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14164794873740515751535089 10623596155305386813651317)
                  ·
                    refine ⟨995962139559880013779811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10623596155305386813651317 995962139559880013779811)
                    ·
                      rfl

theorem cell22_2909444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_2909444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909444 prefixEnd_2909444 := by exact prefixLift 2909444
  have htrace : WordTrace (prefixWord ++ tailWord_2909444) baseStart_2909444 baseEnd_2909444 := by
    simpa [prefixWord, tailWord_2909444, baseEnd_2909444] using wordTrace_append hprefix tailTrace_2909444
  have hstable : (prefixWord ++ tailWord_2909444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909444).length < 2 ^ (prefixWord ++ tailWord_2909444).sum := by decide
  have hdescent : baseEnd_2909444 < baseStart_2909444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909457 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 6]
def baseStart_2909457 : Nat := 118140960795 + 2909457 * 2 ^ 59
def prefixEnd_2909457 : Nat := 4983230072969 + 3 ^ 40 * 2909457 * 2
def baseEnd_2909457 : Nat := 331988863241850771068257

theorem tailTrace_2909457 : CollatzResearch.WordTrace tailWord_2909457 prefixEnd_2909457 331988863241850771068257 := by
  unfold tailWord_2909457
  simp only [CollatzResearch.WordTrace]
  refine ⟨106116614620541659540822625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70744409747027773027215083 106116614620541659540822625)
  ·
    refine ⟨79587460965406244655616969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106116614620541659540822625 79587460965406244655616969)
    ·
      refine ⟨59690595724054683491712727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79587460965406244655616969 59690595724054683491712727)
      ·
        refine ⟨89535893586082025237569091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59690595724054683491712727 89535893586082025237569091)
        ·
          refine ⟨134303840379123037856353637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89535893586082025237569091 134303840379123037856353637)
          ·
            refine ⟨25181970071085569598066307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134303840379123037856353637 25181970071085569598066307)
            ·
              refine ⟨37772955106628354397099461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25181970071085569598066307 37772955106628354397099461)
              ·
                refine ⟨7082429082492816449456149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37772955106628354397099461 7082429082492816449456149)
                ·
                  refine ⟨331988863241850771068257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7082429082492816449456149 331988863241850771068257)
                  ·
                    rfl

theorem cell22_2909457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_2909457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909457 prefixEnd_2909457 := by exact prefixLift 2909457
  have htrace : WordTrace (prefixWord ++ tailWord_2909457) baseStart_2909457 baseEnd_2909457 := by
    simpa [prefixWord, tailWord_2909457, baseEnd_2909457] using wordTrace_append hprefix tailTrace_2909457
  have hstable : (prefixWord ++ tailWord_2909457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909457).length < 2 ^ (prefixWord ++ tailWord_2909457).sum := by decide
  have hdescent : baseEnd_2909457 < baseStart_2909457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909510 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_2909510 : Nat := 118140960795 + 2909510 * 2 ^ 59
def prefixEnd_2909510 : Nat := 4983230072969 + 3 ^ 40 * 2909510 * 2
def baseEnd_2909510 : Nat := 995984732708677841629609

theorem tailTrace_2909510 : CollatzResearch.WordTrace tailWord_2909510 prefixEnd_2909510 995984732708677841629609 := by
  unfold tailWord_2909510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3316204615292176549765687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70745698459566433061667989 3316204615292176549765687)
  ·
    refine ⟨4974306922938264824648531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3316204615292176549765687 4974306922938264824648531)
    ·
      refine ⟨7461460384407397236972797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974306922938264824648531 7461460384407397236972797)
      ·
        refine ⟨2798047644152773963864799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7461460384407397236972797 2798047644152773963864799)
        ·
          refine ⟨4197071466229160945797199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2798047644152773963864799 4197071466229160945797199)
          ·
            refine ⟨6295607199343741418695799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197071466229160945797199 6295607199343741418695799)
            ·
              refine ⟨9443410799015612128043699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295607199343741418695799 9443410799015612128043699)
              ·
                refine ⟨14165116198523418192065549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9443410799015612128043699 14165116198523418192065549)
                ·
                  refine ⟨5311918574446281822024581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14165116198523418192065549 5311918574446281822024581)
                  ·
                    refine ⟨995984732708677841629609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311918574446281822024581 995984732708677841629609)
                    ·
                      rfl

theorem cell22_2909510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_2909510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909510 prefixEnd_2909510 := by exact prefixLift 2909510
  have htrace : WordTrace (prefixWord ++ tailWord_2909510) baseStart_2909510 baseEnd_2909510 := by
    simpa [prefixWord, tailWord_2909510, baseEnd_2909510] using wordTrace_append hprefix tailTrace_2909510
  have hstable : (prefixWord ++ tailWord_2909510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909510).length < 2 ^ (prefixWord ++ tailWord_2909510).sum := by decide
  have hdescent : baseEnd_2909510 < baseStart_2909510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909549 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_2909549 : Nat := 118140960795 + 2909549 * 2 ^ 59
def prefixEnd_2909549 : Nat := 4983230072969 + 3 ^ 40 * 2909549 * 2
def baseEnd_2909549 : Nat := 995998083205694739904489

theorem tailTrace_2909549 : CollatzResearch.WordTrace tailWord_2909549 prefixEnd_2909549 995998083205694739904489 := by
  unfold tailWord_2909549
  simp only [CollatzResearch.WordTrace]
  refine ⟨106119970136208359253171701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70746646757472239502114467 106119970136208359253171701)
  ·
    refine ⟨9948747200269533679984847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106119970136208359253171701 9948747200269533679984847)
    ·
      refine ⟨14923120800404300519977271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9948747200269533679984847 14923120800404300519977271)
      ·
        refine ⟨22384681200606450779965907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14923120800404300519977271 22384681200606450779965907)
        ·
          refine ⟨33577021800909676169948861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22384681200606450779965907 33577021800909676169948861)
          ·
            refine ⟨12591383175341128563730823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33577021800909676169948861 12591383175341128563730823)
            ·
              refine ⟨18887074763011692845596235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12591383175341128563730823 18887074763011692845596235)
              ·
                refine ⟨28330612144517539268394353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18887074763011692845596235 28330612144517539268394353)
                ·
                  refine ⟨21247959108388154451295765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28330612144517539268394353 21247959108388154451295765)
                  ·
                    refine ⟨995998083205694739904489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21247959108388154451295765 995998083205694739904489)
                    ·
                      rfl

theorem cell22_2909549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_2909549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909549 prefixEnd_2909549 := by exact prefixLift 2909549
  have htrace : WordTrace (prefixWord ++ tailWord_2909549) baseStart_2909549 baseEnd_2909549 := by
    simpa [prefixWord, tailWord_2909549, baseEnd_2909549] using wordTrace_append hprefix tailTrace_2909549
  have hstable : (prefixWord ++ tailWord_2909549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909549).length < 2 ^ (prefixWord ++ tailWord_2909549).sum := by decide
  have hdescent : baseEnd_2909549 < baseStart_2909549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909564 : List Nat := [2, 2, 2, 1, 1, 1, 3, 5, 5]
def baseStart_2909564 : Nat := 118140960795 + 2909564 * 2 ^ 59
def prefixEnd_2909564 : Nat := 4983230072969 + 3 ^ 40 * 2909564 * 2
def baseEnd_2909564 : Nat := 332001072670746566926481

theorem tailTrace_2909564 : CollatzResearch.WordTrace tailWord_2909564 prefixEnd_2909564 332001072670746566926481 := by
  unfold tailWord_2909564
  simp only [CollatzResearch.WordTrace]
  refine ⟨53060258615577008407483873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70747011487436011209978497 53060258615577008407483873)
  ·
    refine ⟨39795193961682756305612905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53060258615577008407483873 39795193961682756305612905)
    ·
      refine ⟨29846395471262067229209679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39795193961682756305612905 29846395471262067229209679)
      ·
        refine ⟨44769593206893100843814519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29846395471262067229209679 44769593206893100843814519)
        ·
          refine ⟨67154389810339651265721779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44769593206893100843814519 67154389810339651265721779)
          ·
            refine ⟨100731584715509476898582669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67154389810339651265721779 100731584715509476898582669)
            ·
              refine ⟨37774344268316053836968501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100731584715509476898582669 37774344268316053836968501)
              ·
                refine ⟨3541344775154630047215797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37774344268316053836968501 3541344775154630047215797)
                ·
                  refine ⟨332001072670746566926481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3541344775154630047215797 332001072670746566926481)
                  ·
                    rfl

theorem cell22_2909564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_2909564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909564 prefixEnd_2909564 := by exact prefixLift 2909564
  have htrace : WordTrace (prefixWord ++ tailWord_2909564) baseStart_2909564 baseEnd_2909564 := by
    simpa [prefixWord, tailWord_2909564, baseEnd_2909564] using wordTrace_append hprefix tailTrace_2909564
  have hstable : (prefixWord ++ tailWord_2909564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909564).length < 2 ^ (prefixWord ++ tailWord_2909564).sum := by decide
  have hdescent : baseEnd_2909564 < baseStart_2909564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909598 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2909598 : Nat := 118140960795 + 2909598 * 2 ^ 59
def prefixEnd_2909598 : Nat := 4983230072969 + 3 ^ 40 * 2909598 * 2
def baseEnd_2909598 : Nat := 332004952302358315143113

theorem tailTrace_2909598 : CollatzResearch.WordTrace tailWord_2909598 prefixEnd_2909598 332004952302358315143113 := by
  unfold tailWord_2909598
  simp only [CollatzResearch.WordTrace]
  refine ⟨13265219664128855077713181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70747838208687227081136965 13265219664128855077713181)
  ·
    refine ⟨4974457374048320654142443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13265219664128855077713181 4974457374048320654142443)
    ·
      refine ⟨7461686061072480981213665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974457374048320654142443 7461686061072480981213665)
      ·
        refine ⟨5596264545804360735910249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7461686061072480981213665 5596264545804360735910249)
        ·
          refine ⟨4197198409353270551932687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5596264545804360735910249 4197198409353270551932687)
          ·
            refine ⟨6295797614029905827899031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197198409353270551932687 6295797614029905827899031)
            ·
              refine ⟨9443696421044858741848547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295797614029905827899031 9443696421044858741848547)
              ·
                refine ⟨14165544631567288112772821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9443696421044858741848547 14165544631567288112772821)
                ·
                  refine ⟨332004952302358315143113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14165544631567288112772821 332004952302358315143113)
                  ·
                    rfl

theorem cell22_2909598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2909598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909598 prefixEnd_2909598 := by exact prefixLift 2909598
  have htrace : WordTrace (prefixWord ++ tailWord_2909598) baseStart_2909598 baseEnd_2909598 := by
    simpa [prefixWord, tailWord_2909598, baseEnd_2909598] using wordTrace_append hprefix tailTrace_2909598
  have hstable : (prefixWord ++ tailWord_2909598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909598).length < 2 ^ (prefixWord ++ tailWord_2909598).sum := by decide
  have hdescent : baseEnd_2909598 < baseStart_2909598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909639 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2909639 : Nat := 118140960795 + 2909639 * 2 ^ 59
def prefixEnd_2909639 : Nat := 4983230072969 + 3 ^ 40 * 2909639 * 2
def baseEnd_2909639 : Nat := 996028892044964505154213

theorem tailTrace_2909639 : CollatzResearch.WordTrace tailWord_2909639 prefixEnd_2909639 996028892044964505154213 := by
  unfold tailWord_2909639
  simp only [CollatzResearch.WordTrace]
  refine ⟨106123252705882304623947971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70748835137254869749298647 106123252705882304623947971)
  ·
    refine ⟨159184879058823456935921957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106123252705882304623947971 159184879058823456935921957)
    ·
      refine ⟨29847164823529398175485367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159184879058823456935921957 29847164823529398175485367)
      ·
        refine ⟨44770747235294097263228051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29847164823529398175485367 44770747235294097263228051)
        ·
          refine ⟨67156120852941145894842077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44770747235294097263228051 67156120852941145894842077)
          ·
            refine ⟨25183545319852929710565779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67156120852941145894842077 25183545319852929710565779)
            ·
              refine ⟨37775317979779394565848669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25183545319852929710565779 37775317979779394565848669)
              ·
                refine ⟨14165744242417272962193251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37775317979779394565848669 14165744242417272962193251)
                ·
                  refine ⟨21248616363625909443289877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14165744242417272962193251 21248616363625909443289877)
                  ·
                    refine ⟨996028892044964505154213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21248616363625909443289877 996028892044964505154213)
                    ·
                      rfl

theorem cell22_2909639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2909639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909639 prefixEnd_2909639 := by exact prefixLift 2909639
  have htrace : WordTrace (prefixWord ++ tailWord_2909639) baseStart_2909639 baseEnd_2909639 := by
    simpa [prefixWord, tailWord_2909639, baseEnd_2909639] using wordTrace_append hprefix tailTrace_2909639
  have hstable : (prefixWord ++ tailWord_2909639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909639).length < 2 ^ (prefixWord ++ tailWord_2909639).sum := by decide
  have hdescent : baseEnd_2909639 < baseStart_2909639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909671 : List Nat := [1, 1, 5, 2, 1, 3, 2, 7]
def baseStart_2909671 : Nat := 118140960795 + 2909671 * 2 ^ 59
def prefixEnd_2909671 : Nat := 4983230072969 + 3 ^ 40 * 2909671 * 2
def baseEnd_2909671 : Nat := 110671094033214120928235

theorem tailTrace_2909671 : CollatzResearch.WordTrace tailWord_2909671 prefixEnd_2909671 110671094033214120928235 := by
  unfold tailWord_2909671
  simp only [CollatzResearch.WordTrace]
  refine ⟨106124419841766374089112867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70749613227844249392741911 106124419841766374089112867)
  ·
    refine ⟨159186629762649561133669301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106124419841766374089112867 159186629762649561133669301)
    ·
      refine ⟨14923746540248396356281497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 159186629762649561133669301 14923746540248396356281497)
      ·
        refine ⟨11192809905186297267211123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14923746540248396356281497 11192809905186297267211123)
        ·
          refine ⟨16789214857779445900816685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11192809905186297267211123 16789214857779445900816685)
          ·
            refine ⟨6295955571667292212806257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16789214857779445900816685 6295955571667292212806257)
            ·
              refine ⟨4721966678750469159604693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6295955571667292212806257 4721966678750469159604693)
              ·
                refine ⟨110671094033214120928235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4721966678750469159604693 110671094033214120928235)
                ·
                  rfl

theorem cell22_2909671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 7].length) (baseStart_2909671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909671 prefixEnd_2909671 := by exact prefixLift 2909671
  have htrace : WordTrace (prefixWord ++ tailWord_2909671) baseStart_2909671 baseEnd_2909671 := by
    simpa [prefixWord, tailWord_2909671, baseEnd_2909671] using wordTrace_append hprefix tailTrace_2909671
  have hstable : (prefixWord ++ tailWord_2909671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909671).length < 2 ^ (prefixWord ++ tailWord_2909671).sum := by decide
  have hdescent : baseEnd_2909671 < baseStart_2909671 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909699 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 7]
def baseStart_2909699 : Nat := 118140960795 + 2909699 * 2 ^ 59
def prefixEnd_2909699 : Nat := 4983230072969 + 3 ^ 40 * 2909699 * 2
def baseEnd_2909699 : Nat := 332016477090381449551343

theorem tailTrace_2909699 : CollatzResearch.WordTrace tailWord_2909699 prefixEnd_2909699 332016477090381449551343 := by
  unfold tailWord_2909699
  simp only [CollatzResearch.WordTrace]
  refine ⟨106125441085664934871132151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70750294057109956580754767 106125441085664934871132151)
  ·
    refine ⟨159188161628497402306698227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106125441085664934871132151 159188161628497402306698227)
    ·
      refine ⟨238782242442746103460047341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159188161628497402306698227 238782242442746103460047341)
      ·
        refine ⟨89543340916029788797517753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238782242442746103460047341 89543340916029788797517753)
        ·
          refine ⟨67157505687022341598138315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89543340916029788797517753 67157505687022341598138315)
          ·
            refine ⟨100736258530533512397207473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67157505687022341598138315 100736258530533512397207473)
            ·
              refine ⟨75552193897900134297905605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100736258530533512397207473 75552193897900134297905605)
              ·
                refine ⟨14166036355856275180857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75552193897900134297905605 14166036355856275180857301)
                ·
                  refine ⟨332016477090381449551343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14166036355856275180857301 332016477090381449551343)
                  ·
                    rfl

theorem cell22_2909699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 7].length) (baseStart_2909699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909699 prefixEnd_2909699 := by exact prefixLift 2909699
  have htrace : WordTrace (prefixWord ++ tailWord_2909699) baseStart_2909699 baseEnd_2909699 := by
    simpa [prefixWord, tailWord_2909699, baseEnd_2909699] using wordTrace_append hprefix tailTrace_2909699
  have hstable : (prefixWord ++ tailWord_2909699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909699).length < 2 ^ (prefixWord ++ tailWord_2909699).sum := by decide
  have hdescent : baseEnd_2909699 < baseStart_2909699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909709 : List Nat := [1, 7, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2909709 : Nat := 118140960795 + 2909709 * 2 ^ 59
def prefixEnd_2909709 : Nat := 4983230072969 + 3 ^ 40 * 2909709 * 2
def baseEnd_2909709 : Nat := 996052854475507655903999

theorem tailTrace_2909709 : CollatzResearch.WordTrace tailWord_2909709 prefixEnd_2909709 996052854475507655903999 := by
  unfold tailWord_2909709
  simp only [CollatzResearch.WordTrace]
  refine ⟨106125805815628706578996181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70750537210419137719330787 106125805815628706578996181)
  ·
    refine ⟨2487323573803797810445223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 106125805815628706578996181 2487323573803797810445223)
    ·
      refine ⟨3730985360705696715667835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2487323573803797810445223 3730985360705696715667835)
      ·
        refine ⟨5596478041058545073501753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3730985360705696715667835 5596478041058545073501753)
        ·
          refine ⟨4197358530793908805126315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5596478041058545073501753 4197358530793908805126315)
          ·
            refine ⟨6296037796190863207689473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197358530793908805126315 6296037796190863207689473)
            ·
              refine ⟨4722028347143147405767105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6296037796190863207689473 4722028347143147405767105)
              ·
                refine ⟨3541521260357360554325329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4722028347143147405767105 3541521260357360554325329)
                ·
                  refine ⟨2656140945268020415743997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3541521260357360554325329 2656140945268020415743997)
                  ·
                    refine ⟨996052854475507655903999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2656140945268020415743997 996052854475507655903999)
                    ·
                      rfl

theorem cell22_2909709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2909709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909709 prefixEnd_2909709 := by exact prefixLift 2909709
  have htrace : WordTrace (prefixWord ++ tailWord_2909709) baseStart_2909709 baseEnd_2909709 := by
    simpa [prefixWord, tailWord_2909709, baseEnd_2909709] using wordTrace_append hprefix tailTrace_2909709
  have hstable : (prefixWord ++ tailWord_2909709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909709).length < 2 ^ (prefixWord ++ tailWord_2909709).sum := by decide
  have hdescent : baseEnd_2909709 < baseStart_2909709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909761 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 8]
def baseStart_2909761 : Nat := 118140960795 + 2909761 * 2 ^ 59
def prefixEnd_2909761 : Nat := 4983230072969 + 3 ^ 40 * 2909761 * 2
def baseEnd_2909761 : Nat := 332023551712732284534613

theorem tailTrace_2909761 : CollatzResearch.WordTrace tailWord_2909761 prefixEnd_2909761 332023551712732284534613 := by
  unfold tailWord_2909761
  simp only [CollatzResearch.WordTrace]
  refine ⟨106127702411440319459889137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70751801607626879639926091 106127702411440319459889137)
  ·
    refine ⟨79595776808580239594916853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106127702411440319459889137 79595776808580239594916853)
    ·
      refine ⟨7462104075804397462023455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79595776808580239594916853 7462104075804397462023455)
      ·
        refine ⟨11193156113706596193035183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7462104075804397462023455 11193156113706596193035183)
        ·
          refine ⟨16789734170559894289552775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193156113706596193035183 16789734170559894289552775)
          ·
            refine ⟨25184601255839841434329163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16789734170559894289552775 25184601255839841434329163)
            ·
              refine ⟨37776901883759762151493745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25184601255839841434329163 37776901883759762151493745)
              ·
                refine ⟨28332676412819821613620309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37776901883759762151493745 28332676412819821613620309)
                ·
                  refine ⟨332023551712732284534613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28332676412819821613620309 332023551712732284534613)
                  ·
                    rfl

theorem cell22_2909761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 8].length) (baseStart_2909761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909761 prefixEnd_2909761 := by exact prefixLift 2909761
  have htrace : WordTrace (prefixWord ++ tailWord_2909761) baseStart_2909761 baseEnd_2909761 := by
    simpa [prefixWord, tailWord_2909761, baseEnd_2909761] using wordTrace_append hprefix tailTrace_2909761
  have hstable : (prefixWord ++ tailWord_2909761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909761).length < 2 ^ (prefixWord ++ tailWord_2909761).sum := by decide
  have hdescent : baseEnd_2909761 < baseStart_2909761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909778 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_2909778 : Nat := 118140960795 + 2909778 * 2 ^ 59
def prefixEnd_2909778 : Nat := 4983230072969 + 3 ^ 40 * 2909778 * 2
def baseEnd_2909778 : Nat := 332025491528538158642929

theorem tailTrace_2909778 : CollatzResearch.WordTrace tailWord_2909778 prefixEnd_2909778 332025491528538158642929 := by
  unfold tailWord_2909778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26532080613094682840814497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70752214968252487575505325 26532080613094682840814497)
  ·
    refine ⟨19899060459821012130610873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26532080613094682840814497 19899060459821012130610873)
    ·
      refine ⟨14924295344865759097958155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19899060459821012130610873 14924295344865759097958155)
      ·
        refine ⟨22386443017298638646937233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14924295344865759097958155 22386443017298638646937233)
        ·
          refine ⟨16789832262973978985202925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22386443017298638646937233 16789832262973978985202925)
          ·
            refine ⟨6296187098615242119451097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16789832262973978985202925 6296187098615242119451097)
            ·
              refine ⟨4722140323961431589588323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6296187098615242119451097 4722140323961431589588323)
              ·
                refine ⟨7083210485942147384382485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722140323961431589588323 7083210485942147384382485)
                ·
                  refine ⟨332025491528538158642929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7083210485942147384382485 332025491528538158642929)
                  ·
                    rfl

theorem cell22_2909778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_2909778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909778 prefixEnd_2909778 := by exact prefixLift 2909778
  have htrace : WordTrace (prefixWord ++ tailWord_2909778) baseStart_2909778 baseEnd_2909778 := by
    simpa [prefixWord, tailWord_2909778, baseEnd_2909778] using wordTrace_append hprefix tailTrace_2909778
  have hstable : (prefixWord ++ tailWord_2909778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909778).length < 2 ^ (prefixWord ++ tailWord_2909778).sum := by decide
  have hdescent : baseEnd_2909778 < baseStart_2909778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909836 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2909836 : Nat := 118140960795 + 2909836 * 2 ^ 59
def prefixEnd_2909836 : Nat := 4983230072969 + 3 ^ 40 * 2909836 * 2
def baseEnd_2909836 : Nat := 996096329170921657978609

theorem tailTrace_2909836 : CollatzResearch.WordTrace tailWord_2909836 prefixEnd_2909836 996096329170921657978609 := by
  unfold tailWord_2909836
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065218943084303634434681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70753625257445738179246241 53065218943084303634434681)
  ·
    refine ⟨39798914207313227725826011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53065218943084303634434681 39798914207313227725826011)
    ·
      refine ⟨59698371310969841588739017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39798914207313227725826011 59698371310969841588739017)
      ·
        refine ⟨44773778483227381191554263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59698371310969841588739017 44773778483227381191554263)
        ·
          refine ⟨67160667724841071787331395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44773778483227381191554263 67160667724841071787331395)
          ·
            refine ⟨100741001587261607680997093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67160667724841071787331395 100741001587261607680997093)
            ·
              refine ⟨18888937797611551440186955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100741001587261607680997093 18888937797611551440186955)
              ·
                refine ⟨28333406696417327160280433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18888937797611551440186955 28333406696417327160280433)
                ·
                  refine ⟨21250055022312995370210325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28333406696417327160280433 21250055022312995370210325)
                  ·
                    refine ⟨996096329170921657978609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21250055022312995370210325 996096329170921657978609)
                    ·
                      rfl

theorem cell22_2909836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2909836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909836 prefixEnd_2909836 := by exact prefixLift 2909836
  have htrace : WordTrace (prefixWord ++ tailWord_2909836) baseStart_2909836 baseEnd_2909836 := by
    simpa [prefixWord, tailWord_2909836, baseEnd_2909836] using wordTrace_append hprefix tailTrace_2909836
  have hstable : (prefixWord ++ tailWord_2909836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909836).length < 2 ^ (prefixWord ++ tailWord_2909836).sum := by decide
  have hdescent : baseEnd_2909836 < baseStart_2909836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909900 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_2909900 : Nat := 118140960795 + 2909900 * 2 ^ 59
def prefixEnd_2909900 : Nat := 4983230072969 + 3 ^ 40 * 2909900 * 2
def baseEnd_2909900 : Nat := 996118237678846824378413

theorem tailTrace_2909900 : CollatzResearch.WordTrace tailWord_2909900 prefixEnd_2909900 996118237678846824378413 := by
  unfold tailWord_2909900
  simp only [CollatzResearch.WordTrace]
  refine ⟨53066386078968373099599577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70755181438624497466132769 53066386078968373099599577)
  ·
    refine ⟨39799789559226279824699683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53066386078968373099599577 39799789559226279824699683)
    ·
      refine ⟨59699684338839419737049525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39799789559226279824699683 59699684338839419737049525)
      ·
        refine ⟨5596845406766195600348393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59699684338839419737049525 5596845406766195600348393)
        ·
          refine ⟨4197634055074646700261295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5596845406766195600348393 4197634055074646700261295)
          ·
            refine ⟨6296451082611970050391943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197634055074646700261295 6296451082611970050391943)
            ·
              refine ⟨9444676623917955075587915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296451082611970050391943 9444676623917955075587915)
              ·
                refine ⟨14167014935876932613381873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9444676623917955075587915 14167014935876932613381873)
                ·
                  refine ⟨10625261201907699460036405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14167014935876932613381873 10625261201907699460036405)
                  ·
                    refine ⟨996118237678846824378413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10625261201907699460036405 996118237678846824378413)
                    ·
                      rfl

theorem cell22_2909900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_2909900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909900 prefixEnd_2909900 := by exact prefixLift 2909900
  have htrace : WordTrace (prefixWord ++ tailWord_2909900) baseStart_2909900 baseEnd_2909900 := by
    simpa [prefixWord, tailWord_2909900, baseEnd_2909900] using wordTrace_append hprefix tailTrace_2909900
  have hstable : (prefixWord ++ tailWord_2909900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909900).length < 2 ^ (prefixWord ++ tailWord_2909900).sum := by decide
  have hdescent : baseEnd_2909900 < baseStart_2909900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909913 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 6]
def baseStart_2909913 : Nat := 118140960795 + 2909913 * 2 ^ 59
def prefixEnd_2909913 : Nat := 4983230072969 + 3 ^ 40 * 2909913 * 2
def baseEnd_2909913 : Nat := 332040895948173041267791

theorem tailTrace_2909913 : CollatzResearch.WordTrace tailWord_2909913 prefixEnd_2909913 332040895948173041267791 := by
  unfold tailWord_2909913
  simp only [CollatzResearch.WordTrace]
  refine ⟨106133246306889649419422393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70755497537926432946281595 106133246306889649419422393)
  ·
    refine ⟨79599934730167237064566795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106133246306889649419422393 79599934730167237064566795)
    ·
      refine ⟨119399902095250855596850193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79599934730167237064566795 119399902095250855596850193)
      ·
        refine ⟨89549926571438141697637645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119399902095250855596850193 89549926571438141697637645)
        ·
          refine ⟨33581222464289303136614117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89549926571438141697637645 33581222464289303136614117)
          ·
            refine ⟨6296479212054244338115147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33581222464289303136614117 6296479212054244338115147)
            ·
              refine ⟨9444718818081366507172721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296479212054244338115147 9444718818081366507172721)
              ·
                refine ⟨7083539113561024880379541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9444718818081366507172721 7083539113561024880379541)
                ·
                  refine ⟨332040895948173041267791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7083539113561024880379541 332040895948173041267791)
                  ·
                    rfl

theorem cell22_2909913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 6].length) (baseStart_2909913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909913 prefixEnd_2909913 := by exact prefixLift 2909913
  have htrace : WordTrace (prefixWord ++ tailWord_2909913) baseStart_2909913 baseEnd_2909913 := by
    simpa [prefixWord, tailWord_2909913, baseEnd_2909913] using wordTrace_append hprefix tailTrace_2909913
  have hstable : (prefixWord ++ tailWord_2909913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909913).length < 2 ^ (prefixWord ++ tailWord_2909913).sum := by decide
  have hdescent : baseEnd_2909913 < baseStart_2909913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909930 : List Nat := [3, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_2909930 : Nat := 118140960795 + 2909930 * 2 ^ 59
def prefixEnd_2909930 : Nat := 4983230072969 + 3 ^ 40 * 2909930 * 2
def baseEnd_2909930 : Nat := 332042835763978915376107

theorem tailTrace_2909930 : CollatzResearch.WordTrace tailWord_2909930 prefixEnd_2909930 332042835763978915376107 := by
  unfold tailWord_2909930
  simp only [CollatzResearch.WordTrace]
  refine ⟨26533466586957015330697811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70755910898552040881860829 26533466586957015330697811)
  ·
    refine ⟨39800199880435522996046717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26533466586957015330697811 39800199880435522996046717)
    ·
      refine ⟨14925074955163321123517519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39800199880435522996046717 14925074955163321123517519)
      ·
        refine ⟨22387612432744981685276279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14925074955163321123517519 22387612432744981685276279)
        ·
          refine ⟨33581418649117472527914419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22387612432744981685276279 33581418649117472527914419)
          ·
            refine ⟨50372127973676208791871629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33581418649117472527914419 50372127973676208791871629)
            ·
              refine ⟨18889547990128578296951861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50372127973676208791871629 18889547990128578296951861)
              ·
                refine ⟨1770895124074554215339237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18889547990128578296951861 1770895124074554215339237)
                ·
                  refine ⟨332042835763978915376107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770895124074554215339237 332042835763978915376107)
                  ·
                    rfl

theorem cell22_2909930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_2909930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909930 prefixEnd_2909930 := by exact prefixLift 2909930
  have htrace : WordTrace (prefixWord ++ tailWord_2909930) baseStart_2909930 baseEnd_2909930 := by
    simpa [prefixWord, tailWord_2909930, baseEnd_2909930] using wordTrace_append hprefix tailTrace_2909930
  have hstable : (prefixWord ++ tailWord_2909930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909930).length < 2 ^ (prefixWord ++ tailWord_2909930).sum := by decide
  have hdescent : baseEnd_2909930 < baseStart_2909930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909943 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 2, 4]
def baseStart_2909943 : Nat := 118140960795 + 2909943 * 2 ^ 59
def prefixEnd_2909943 : Nat := 4983230072969 + 3 ^ 40 * 2909943 * 2
def baseEnd_2909943 : Nat := 996132957457609045553281

theorem tailTrace_2909943 : CollatzResearch.WordTrace tailWord_2909943 prefixEnd_2909943 996132957457609045553281 := by
  unfold tailWord_2909943
  simp only [CollatzResearch.WordTrace]
  refine ⟨106134340496780964543014483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70756226997853976362009655 106134340496780964543014483)
  ·
    refine ⟨159201510745171446814521725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106134340496780964543014483 159201510745171446814521725)
    ·
      refine ⟨59700566529439292555445647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159201510745171446814521725 59700566529439292555445647)
      ·
        refine ⟨89550849794158938833168471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59700566529439292555445647 89550849794158938833168471)
        ·
          refine ⟨134326274691238408249752707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89550849794158938833168471 134326274691238408249752707)
          ·
            refine ⟨201489412036857612374629061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134326274691238408249752707 201489412036857612374629061)
            ·
              refine ⟨37779264756910802320242949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201489412036857612374629061 37779264756910802320242949)
              ·
                refine ⟨7083612141920775435045553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37779264756910802320242949 7083612141920775435045553)
                ·
                  refine ⟨5312709106440581576284165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7083612141920775435045553 5312709106440581576284165)
                  ·
                    refine ⟨996132957457609045553281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5312709106440581576284165 996132957457609045553281)
                    ·
                      rfl

theorem cell22_2909943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_2909943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909943 prefixEnd_2909943 := by exact prefixLift 2909943
  have htrace : WordTrace (prefixWord ++ tailWord_2909943) baseStart_2909943 baseEnd_2909943 := by
    simpa [prefixWord, tailWord_2909943, baseEnd_2909943] using wordTrace_append hprefix tailTrace_2909943
  have hstable : (prefixWord ++ tailWord_2909943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909943).length < 2 ^ (prefixWord ++ tailWord_2909943).sum := by decide
  have hdescent : baseEnd_2909943 < baseStart_2909943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2909975 : List Nat := [1, 1, 3, 4, 2, 1, 4, 6]
def baseStart_2909975 : Nat := 118140960795 + 2909975 * 2 ^ 59
def prefixEnd_2909975 : Nat := 4983230072969 + 3 ^ 40 * 2909975 * 2
def baseEnd_2909975 : Nat := 110682656856841292083687

theorem tailTrace_2909975 : CollatzResearch.WordTrace tailWord_2909975 prefixEnd_2909975 110682656856841292083687 := by
  unfold tailWord_2909975
  simp only [CollatzResearch.WordTrace]
  refine ⟨106135507632665034008179379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70757005088443356005452919 106135507632665034008179379)
  ·
    refine ⟨159203261448997551012269069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106135507632665034008179379 159203261448997551012269069)
    ·
      refine ⟨59701223043374081629600901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159203261448997551012269069 59701223043374081629600901)
      ·
        refine ⟨11193979320632640305550169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59701223043374081629600901 11193979320632640305550169)
        ·
          refine ⟨8395484490474480229162627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11193979320632640305550169 8395484490474480229162627)
          ·
            refine ⟨12593226735711720343743941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8395484490474480229162627 12593226735711720343743941)
            ·
              refine ⟨2361230012945947564451989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12593226735711720343743941 2361230012945947564451989)
              ·
                refine ⟨110682656856841292083687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2361230012945947564451989 110682656856841292083687)
                ·
                  rfl

theorem cell22_2909975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 6].length) (baseStart_2909975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2909975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2909975 prefixEnd_2909975 := by exact prefixLift 2909975
  have htrace : WordTrace (prefixWord ++ tailWord_2909975) baseStart_2909975 baseEnd_2909975 := by
    simpa [prefixWord, tailWord_2909975, baseEnd_2909975] using wordTrace_append hprefix tailTrace_2909975
  have hstable : (prefixWord ++ tailWord_2909975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2909975).length < 2 ^ (prefixWord ++ tailWord_2909975).sum := by decide
  have hdescent : baseEnd_2909975 < baseStart_2909975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2909975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910080 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_2910080 : Nat := 118140960795 + 2910080 * 2 ^ 59
def prefixEnd_2910080 : Nat := 4983230072969 + 3 ^ 40 * 2910080 * 2
def baseEnd_2910080 : Nat := 996179855357386354877861

theorem tailTrace_2910080 : CollatzResearch.WordTrace tailWord_2910080 prefixEnd_2910080 996179855357386354877861 := by
  unfold tailWord_2910080
  simp only [CollatzResearch.WordTrace]
  refine ⟨53069668648642318470375847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70759558198189757960501129 53069668648642318470375847)
  ·
    refine ⟨79604502972963477705563771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53069668648642318470375847 79604502972963477705563771)
    ·
      refine ⟨119406754459445216558345657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79604502972963477705563771 119406754459445216558345657)
      ·
        refine ⟨89555065844583912418759243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119406754459445216558345657 89555065844583912418759243)
        ·
          refine ⟨134332598766875868628138865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89555065844583912418759243 134332598766875868628138865)
          ·
            refine ⟨100749449075156901471104149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134332598766875868628138865 100749449075156901471104149)
            ·
              refine ⟨4722630425397979756458007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 100749449075156901471104149 4722630425397979756458007)
              ·
                refine ⟨7083945638096969634687011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722630425397979756458007 7083945638096969634687011)
                ·
                  refine ⟨10625918457145454452030517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7083945638096969634687011 10625918457145454452030517)
                  ·
                    refine ⟨996179855357386354877861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10625918457145454452030517 996179855357386354877861)
                    ·
                      rfl

theorem cell22_2910080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_2910080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910080 prefixEnd_2910080 := by exact prefixLift 2910080
  have htrace : WordTrace (prefixWord ++ tailWord_2910080) baseStart_2910080 baseEnd_2910080 := by
    simpa [prefixWord, tailWord_2910080, baseEnd_2910080] using wordTrace_append hprefix tailTrace_2910080
  have hstable : (prefixWord ++ tailWord_2910080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910080).length < 2 ^ (prefixWord ++ tailWord_2910080).sum := by decide
  have hdescent : baseEnd_2910080 < baseStart_2910080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910114 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2910114 : Nat := 118140960795 + 2910114 * 2 ^ 59
def prefixEnd_2910114 : Nat := 4983230072969 + 3 ^ 40 * 2910114 * 2
def baseEnd_2910114 : Nat := 996191494252221599527757

theorem tailTrace_2910114 : CollatzResearch.WordTrace tailWord_2910114 prefixEnd_2910114 996191494252221599527757 := by
  unfold tailWord_2910114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535144344790365186872349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70760384919440973831659597 26535144344790365186872349)
  ·
    refine ⟨9950679129296386945077131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26535144344790365186872349 9950679129296386945077131)
    ·
      refine ⟨14926018693944580417615697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9950679129296386945077131 14926018693944580417615697)
      ·
        refine ⟨11194514020458435313211773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14926018693944580417615697 11194514020458435313211773)
        ·
          refine ⟨4197942757671913242454415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11194514020458435313211773 4197942757671913242454415)
          ·
            refine ⟨6296914136507869863681623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4197942757671913242454415 6296914136507869863681623)
            ·
              refine ⟨9445371204761804795522435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6296914136507869863681623 9445371204761804795522435)
              ·
                refine ⟨14168056807142707193283653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9445371204761804795522435 14168056807142707193283653)
                ·
                  refine ⟨2656510651339257598740685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14168056807142707193283653 2656510651339257598740685)
                  ·
                    refine ⟨996191494252221599527757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2656510651339257598740685 996191494252221599527757)
                    ·
                      rfl

theorem cell22_2910114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2910114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910114 prefixEnd_2910114 := by exact prefixLift 2910114
  have htrace : WordTrace (prefixWord ++ tailWord_2910114) baseStart_2910114 baseEnd_2910114 := by
    simpa [prefixWord, tailWord_2910114, baseEnd_2910114] using wordTrace_append hprefix tailTrace_2910114
  have hstable : (prefixWord ++ tailWord_2910114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910114).length < 2 ^ (prefixWord ++ tailWord_2910114).sum := by decide
  have hdescent : baseEnd_2910114 < baseStart_2910114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910200 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 6]
def baseStart_2910200 : Nat := 118140960795 + 2910200 * 2 ^ 59
def prefixEnd_2910200 : Nat := 4983230072969 + 3 ^ 40 * 2910200 * 2
def baseEnd_2910200 : Nat := 332073644603248680625831

theorem tailTrace_2910200 : CollatzResearch.WordTrace tailWord_2910200 prefixEnd_2910200 332073644603248680625831 := by
  unfold tailWord_2910200
  simp only [CollatzResearch.WordTrace]
  refine ⟨53071857028424948717560027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70762476037899931623413369 53071857028424948717560027)
  ·
    refine ⟨79607785542637423076340041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53071857028424948717560027 79607785542637423076340041)
    ·
      refine ⟨59705839156978067307255031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79607785542637423076340041 59705839156978067307255031)
      ·
        refine ⟨89558758735467100960882547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59705839156978067307255031 89558758735467100960882547)
        ·
          refine ⟨134338138103200651441323821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89558758735467100960882547 134338138103200651441323821)
          ·
            refine ⟨50376801788700244290496433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134338138103200651441323821 50376801788700244290496433)
            ·
              refine ⟨37782601341525183217872325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50376801788700244290496433 37782601341525183217872325)
              ·
                refine ⟨7084237751535971853351061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37782601341525183217872325 7084237751535971853351061)
                ·
                  refine ⟨332073644603248680625831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7084237751535971853351061 332073644603248680625831)
                  ·
                    rfl

theorem cell22_2910200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_2910200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910200 prefixEnd_2910200 := by exact prefixLift 2910200
  have htrace : WordTrace (prefixWord ++ tailWord_2910200) baseStart_2910200 baseEnd_2910200 := by
    simpa [prefixWord, tailWord_2910200, baseEnd_2910200] using wordTrace_append hprefix tailTrace_2910200
  have hstable : (prefixWord ++ tailWord_2910200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910200).length < 2 ^ (prefixWord ++ tailWord_2910200).sum := by decide
  have hdescent : baseEnd_2910200 < baseStart_2910200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910219 : List Nat := [1, 1, 1, 1, 6, 1, 5, 1, 1, 4]
def baseStart_2910219 : Nat := 118140960795 + 2910219 * 2 ^ 59
def prefixEnd_2910219 : Nat := 4983230072969 + 3 ^ 40 * 2910219 * 2
def baseEnd_2910219 : Nat := 996227437898036325652435

theorem tailTrace_2910219 : CollatzResearch.WordTrace tailWord_2910219 prefixEnd_2910219 996227437898036325652435 := by
  unfold tailWord_2910219
  simp only [CollatzResearch.WordTrace]
  refine ⟨106144407043781063680061711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70762938029187375786707807 106144407043781063680061711)
  ·
    refine ⟨159216610565671595520092567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106144407043781063680061711 159216610565671595520092567)
    ·
      refine ⟨238824915848507393280138851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159216610565671595520092567 238824915848507393280138851)
      ·
        refine ⟨358237373772761089920208277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 238824915848507393280138851 358237373772761089920208277)
        ·
          refine ⟨16792376895598176090009763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 358237373772761089920208277 16792376895598176090009763)
          ·
            refine ⟨25188565343397264135014645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16792376895598176090009763 25188565343397264135014645)
            ·
              refine ⟨2361428000943493512657623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25188565343397264135014645 2361428000943493512657623)
              ·
                refine ⟨3542142001415240268986435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361428000943493512657623 3542142001415240268986435)
                ·
                  refine ⟨5313213002122860403479653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542142001415240268986435 5313213002122860403479653)
                  ·
                    refine ⟨996227437898036325652435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313213002122860403479653 996227437898036325652435)
                    ·
                      rfl

theorem cell22_2910219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 5, 1, 1, 4].length) (baseStart_2910219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910219 prefixEnd_2910219 := by exact prefixLift 2910219
  have htrace : WordTrace (prefixWord ++ tailWord_2910219) baseStart_2910219 baseEnd_2910219 := by
    simpa [prefixWord, tailWord_2910219, baseEnd_2910219] using wordTrace_append hprefix tailTrace_2910219
  have hstable : (prefixWord ++ tailWord_2910219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910219).length < 2 ^ (prefixWord ++ tailWord_2910219).sum := by decide
  have hdescent : baseEnd_2910219 < baseStart_2910219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910234 : List Nat := [3, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_2910234 : Nat := 118140960795 + 2910234 * 2 ^ 59
def prefixEnd_2910234 : Nat := 4983230072969 + 3 ^ 40 * 2910234 * 2
def baseEnd_2910234 : Nat := 332077524234860428842463

theorem tailTrace_2910234 : CollatzResearch.WordTrace tailWord_2910234 prefixEnd_2910234 332077524234860428842463 := by
  unfold tailWord_2910234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26536238534681680310464439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70763302759151147494571837 26536238534681680310464439)
  ·
    refine ⟨39804357802022520465696659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26536238534681680310464439 39804357802022520465696659)
    ·
      refine ⟨59706536703033780698544989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39804357802022520465696659 59706536703033780698544989)
      ·
        refine ⟨22389951263637667761954371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59706536703033780698544989 22389951263637667761954371)
        ·
          refine ⟨33584926895456501642931557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22389951263637667761954371 33584926895456501642931557)
          ·
            refine ⟨6297173792898094058049667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33584926895456501642931557 6297173792898094058049667)
            ·
              refine ⟨9445760689347141087074501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6297173792898094058049667 9445760689347141087074501)
              ·
                refine ⟨1771080129252588953826469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9445760689347141087074501 1771080129252588953826469)
                ·
                  refine ⟨332077524234860428842463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771080129252588953826469 332077524234860428842463)
                  ·
                    rfl

theorem cell22_2910234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_2910234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910234 prefixEnd_2910234 := by exact prefixLift 2910234
  have htrace : WordTrace (prefixWord ++ tailWord_2910234) baseStart_2910234 baseEnd_2910234 := by
    simpa [prefixWord, tailWord_2910234, baseEnd_2910234] using wordTrace_append hprefix tailTrace_2910234
  have hstable : (prefixWord ++ tailWord_2910234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910234).length < 2 ^ (prefixWord ++ tailWord_2910234).sum := by decide
  have hdescent : baseEnd_2910234 < baseStart_2910234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910270 : List Nat := [4, 2, 1, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2910270 : Nat := 118140960795 + 2910270 * 2 ^ 59
def prefixEnd_2910270 : Nat := 4983230072969 + 3 ^ 40 * 2910270 * 2
def baseEnd_2910270 : Nat := 996244896240289192627279

theorem tailTrace_2910270 : CollatzResearch.WordTrace tailWord_2910270 prefixEnd_2910270 996244896240289192627279 := by
  unfold tailWord_2910270
  simp only [CollatzResearch.WordTrace]
  refine ⟨13268283395824537423771033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70764178111064199593445509 13268283395824537423771033)
  ·
    refine ⟨9951212546868403067828275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13268283395824537423771033 9951212546868403067828275)
    ·
      refine ⟨14926818820302604601742413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9951212546868403067828275 14926818820302604601742413)
      ·
        refine ⟨5597557057613476725653405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14926818820302604601742413 5597557057613476725653405)
        ·
          refine ⟨2099083896605053772120027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5597557057613476725653405 2099083896605053772120027)
          ·
            refine ⟨3148625844907580658180041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099083896605053772120027 3148625844907580658180041)
            ·
              refine ⟨2361469383680685493635031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148625844907580658180041 2361469383680685493635031)
              ·
                refine ⟨3542204075521028240452547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361469383680685493635031 3542204075521028240452547)
                ·
                  refine ⟨5313306113281542360678821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542204075521028240452547 5313306113281542360678821)
                  ·
                    refine ⟨996244896240289192627279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313306113281542360678821 996244896240289192627279)
                    ·
                      rfl

theorem cell22_2910270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2910270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910270 prefixEnd_2910270 := by exact prefixLift 2910270
  have htrace : WordTrace (prefixWord ++ tailWord_2910270) baseStart_2910270 baseEnd_2910270 := by
    simpa [prefixWord, tailWord_2910270, baseEnd_2910270] using wordTrace_append hprefix tailTrace_2910270
  have hstable : (prefixWord ++ tailWord_2910270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910270).length < 2 ^ (prefixWord ++ tailWord_2910270).sum := by decide
  have hdescent : baseEnd_2910270 < baseStart_2910270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910275 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 1, 8]
def baseStart_2910275 : Nat := 118140960795 + 2910275 * 2 ^ 59
def prefixEnd_2910275 : Nat := 4983230072969 + 3 ^ 40 * 2910275 * 2
def baseEnd_2910275 : Nat := 996246607842470846252263

theorem tailTrace_2910275 : CollatzResearch.WordTrace tailWord_2910275 prefixEnd_2910275 996246607842470846252263 := by
  unfold tailWord_2910275
  simp only [CollatzResearch.WordTrace]
  refine ⟨106146449531578185244100279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70764299687718790162733519 106146449531578185244100279)
  ·
    refine ⟨159219674297367277866150419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106146449531578185244100279 159219674297367277866150419)
    ·
      refine ⟨238829511446050916799225629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159219674297367277866150419 238829511446050916799225629)
      ·
        refine ⟨89561066792269093799709611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 238829511446050916799225629 89561066792269093799709611)
        ·
          refine ⟨134341600188403640699564417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89561066792269093799709611 134341600188403640699564417)
          ·
            refine ⟨100756200141302730524673313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134341600188403640699564417 100756200141302730524673313)
            ·
              refine ⟨75567150105977047893504985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100756200141302730524673313 75567150105977047893504985)
              ·
                refine ⟨56675362579482785920128739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75567150105977047893504985 56675362579482785920128739)
                ·
                  refine ⟨85013043869224178880193109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56675362579482785920128739 85013043869224178880193109)
                  ·
                    refine ⟨996246607842470846252263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85013043869224178880193109 996246607842470846252263)
                    ·
                      rfl

theorem cell22_2910275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 8].length) (baseStart_2910275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910275 prefixEnd_2910275 := by exact prefixLift 2910275
  have htrace : WordTrace (prefixWord ++ tailWord_2910275) baseStart_2910275 baseEnd_2910275 := by
    simpa [prefixWord, tailWord_2910275, baseEnd_2910275] using wordTrace_append hprefix tailTrace_2910275
  have hstable : (prefixWord ++ tailWord_2910275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910275).length < 2 ^ (prefixWord ++ tailWord_2910275).sum := by decide
  have hdescent : baseEnd_2910275 < baseStart_2910275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910277 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_2910277 : Nat := 118140960795 + 2910277 * 2 ^ 59
def prefixEnd_2910277 : Nat := 4983230072969 + 3 ^ 40 * 2910277 * 2
def baseEnd_2910277 : Nat := 996247292483343507702257

theorem tailTrace_2910277 : CollatzResearch.WordTrace tailWord_2910277 prefixEnd_2910277 996247292483343507702257 := by
  unfold tailWord_2910277
  simp only [CollatzResearch.WordTrace]
  refine ⟨106146522477570939585673085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70764348318380626390448723 106146522477570939585673085)
  ·
    refine ⟨39804945929089102344627407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106146522477570939585673085 39804945929089102344627407)
    ·
      refine ⟨59707418893633653516941111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39804945929089102344627407 59707418893633653516941111)
      ·
        refine ⟨89561128340450480275411667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59707418893633653516941111 89561128340450480275411667)
        ·
          refine ⟨134341692510675720413117501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89561128340450480275411667 134341692510675720413117501)
          ·
            refine ⟨50378134691503395154919063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134341692510675720413117501 50378134691503395154919063)
            ·
              refine ⟨75567202037255092732378595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50378134691503395154919063 75567202037255092732378595)
              ·
                refine ⟨113350803055882639098567893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75567202037255092732378595 113350803055882639098567893)
                ·
                  refine ⟨2656659446622249353872685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 113350803055882639098567893 2656659446622249353872685)
                  ·
                    refine ⟨996247292483343507702257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2656659446622249353872685 996247292483343507702257)
                    ·
                      rfl

theorem cell22_2910277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_2910277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910277 prefixEnd_2910277 := by exact prefixLift 2910277
  have htrace : WordTrace (prefixWord ++ tailWord_2910277) baseStart_2910277 baseEnd_2910277 := by
    simpa [prefixWord, tailWord_2910277, baseEnd_2910277] using wordTrace_append hprefix tailTrace_2910277
  have hstable : (prefixWord ++ tailWord_2910277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910277).length < 2 ^ (prefixWord ++ tailWord_2910277).sum := by decide
  have hdescent : baseEnd_2910277 < baseStart_2910277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910307 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 5]
def baseStart_2910307 : Nat := 118140960795 + 2910307 * 2 ^ 59
def prefixEnd_2910307 : Nat := 4983230072969 + 3 ^ 40 * 2910307 * 2
def baseEnd_2910307 : Nat := 332085854032144476484055

theorem tailTrace_2910307 : CollatzResearch.WordTrace tailWord_2910307 prefixEnd_2910307 332085854032144476484055 := by
  unfold tailWord_2910307
  simp only [CollatzResearch.WordTrace]
  refine ⟨106147616667462254709265175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70765077778308169806176783 106147616667462254709265175)
  ·
    refine ⟨159221425001193382063897763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106147616667462254709265175 159221425001193382063897763)
    ·
      refine ⟨238832137501790073095846645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159221425001193382063897763 238832137501790073095846645)
      ·
        refine ⟨22390512890792819352735623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 238832137501790073095846645 22390512890792819352735623)
        ·
          refine ⟨33585769336189229029103435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22390512890792819352735623 33585769336189229029103435)
          ·
            refine ⟨50378654004283843543655153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33585769336189229029103435 50378654004283843543655153)
            ·
              refine ⟨37783990503212882657741365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50378654004283843543655153 37783990503212882657741365)
              ·
                refine ⟨3542249109676207749163253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37783990503212882657741365 3542249109676207749163253)
                ·
                  refine ⟨332085854032144476484055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542249109676207749163253 332085854032144476484055)
                  ·
                    rfl

theorem cell22_2910307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 5].length) (baseStart_2910307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910307 prefixEnd_2910307 := by exact prefixLift 2910307
  have htrace : WordTrace (prefixWord ++ tailWord_2910307) baseStart_2910307 baseEnd_2910307 := by
    simpa [prefixWord, tailWord_2910307, baseEnd_2910307] using wordTrace_append hprefix tailTrace_2910307
  have hstable : (prefixWord ++ tailWord_2910307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910307).length < 2 ^ (prefixWord ++ tailWord_2910307).sum := by decide
  have hdescent : baseEnd_2910307 < baseStart_2910307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910354 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 3, 4]
def baseStart_2910354 : Nat := 118140960795 + 2910354 * 2 ^ 59
def prefixEnd_2910354 : Nat := 4983230072969 + 3 ^ 40 * 2910354 * 2
def baseEnd_2910354 : Nat := 996273651156940973527021

theorem tailTrace_2910354 : CollatzResearch.WordTrace tailWord_2910354 prefixEnd_2910354 996273651156940973527021 := by
  unfold tailWord_2910354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26537332724572995434056529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70766220598861321157484077 26537332724572995434056529)
  ·
    refine ⟨19902999543429746575542397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26537332724572995434056529 19902999543429746575542397)
    ·
      refine ⟨7463624828786154965828399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19902999543429746575542397 7463624828786154965828399)
      ·
        refine ⟨11195437243179232448742599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7463624828786154965828399 11195437243179232448742599)
        ·
          refine ⟨16793155864768848673113899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11195437243179232448742599 16793155864768848673113899)
          ·
            refine ⟨25189733797153273009670849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16793155864768848673113899 25189733797153273009670849)
            ·
              refine ⟨18892300347864954757253137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25189733797153273009670849 18892300347864954757253137)
              ·
                refine ⟨14169225260898716067939853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18892300347864954757253137 14169225260898716067939853)
                ·
                  refine ⟨5313459472837018525477445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14169225260898716067939853 5313459472837018525477445)
                  ·
                    refine ⟨996273651156940973527021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313459472837018525477445 996273651156940973527021)
                    ·
                      rfl

theorem cell22_2910354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_2910354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910354 prefixEnd_2910354 := by exact prefixLift 2910354
  have htrace : WordTrace (prefixWord ++ tailWord_2910354) baseStart_2910354 baseEnd_2910354 := by
    simpa [prefixWord, tailWord_2910354, baseEnd_2910354] using wordTrace_append hprefix tailTrace_2910354
  have hstable : (prefixWord ++ tailWord_2910354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910354).length < 2 ^ (prefixWord ++ tailWord_2910354).sum := by decide
  have hdescent : baseEnd_2910354 < baseStart_2910354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910414 : List Nat := [4, 1, 1, 1, 4, 1, 3, 7]
def baseStart_2910414 : Nat := 118140960795 + 2910414 * 2 ^ 59
def prefixEnd_2910414 : Nat := 4983230072969 + 3 ^ 40 * 2910414 * 2
def baseEnd_2910414 : Nat := 110699354487013424114093

theorem tailTrace_2910414 : CollatzResearch.WordTrace tailWord_2910414 prefixEnd_2910414 110699354487013424114093 := by
  unfold tailWord_2910414
  simp only [CollatzResearch.WordTrace]
  refine ⟨13268939909759326497926287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70767679518716407988940197 13268939909759326497926287)
  ·
    refine ⟨19903409864638989746889431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13268939909759326497926287 19903409864638989746889431)
    ·
      refine ⟨29855114796958484620334147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19903409864638989746889431 29855114796958484620334147)
      ·
        refine ⟨44782672195437726930501221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29855114796958484620334147 44782672195437726930501221)
        ·
          refine ⟨8396751036644573799468979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44782672195437726930501221 8396751036644573799468979)
          ·
            refine ⟨12595126554966860699203469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8396751036644573799468979 12595126554966860699203469)
            ·
              refine ⟨4723172458112572762201301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12595126554966860699203469 4723172458112572762201301)
              ·
                refine ⟨110699354487013424114093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4723172458112572762201301 110699354487013424114093)
                ·
                  rfl

theorem cell22_2910414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_2910414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910414 prefixEnd_2910414 := by exact prefixLift 2910414
  have htrace : WordTrace (prefixWord ++ tailWord_2910414) baseStart_2910414 baseEnd_2910414 := by
    simpa [prefixWord, tailWord_2910414, baseEnd_2910414] using wordTrace_append hprefix tailTrace_2910414
  have hstable : (prefixWord ++ tailWord_2910414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910414).length < 2 ^ (prefixWord ++ tailWord_2910414).sum := by decide
  have hdescent : baseEnd_2910414 < baseStart_2910414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910474 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 2, 5]
def baseStart_2910474 : Nat := 118140960795 + 2910474 * 2 ^ 59
def prefixEnd_2910474 : Nat := 4983230072969 + 3 ^ 40 * 2910474 * 2
def baseEnd_2910474 : Nat := 996314729609300660526653

theorem tailTrace_2910474 : CollatzResearch.WordTrace tailWord_2910474 prefixEnd_2910474 996314729609300660526653 := by
  unfold tailWord_2910474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26538426914464310557648619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70769138438571494820396317 26538426914464310557648619)
  ·
    refine ⟨39807640371696465836472929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26538426914464310557648619 39807640371696465836472929)
    ·
      refine ⟨29855730278772349377354697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39807640371696465836472929 29855730278772349377354697)
      ·
        refine ⟨22391797709079262033016023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29855730278772349377354697 22391797709079262033016023)
        ·
          refine ⟨33587696563618893049524035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22391797709079262033016023 33587696563618893049524035)
          ·
            refine ⟨50381544845428339574286053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33587696563618893049524035 50381544845428339574286053)
            ·
              refine ⟨9446539658517813670178635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50381544845428339574286053 9446539658517813670178635)
              ·
                refine ⟨14169809487776720505267953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9446539658517813670178635 14169809487776720505267953)
                ·
                  refine ⟨10627357115832540378950965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14169809487776720505267953 10627357115832540378950965)
                  ·
                    refine ⟨996314729609300660526653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10627357115832540378950965 996314729609300660526653)
                    ·
                      rfl

theorem cell22_2910474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_2910474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910474 prefixEnd_2910474 := by exact prefixLift 2910474
  have htrace : WordTrace (prefixWord ++ tailWord_2910474) baseStart_2910474 baseEnd_2910474 := by
    simpa [prefixWord, tailWord_2910474, baseEnd_2910474] using wordTrace_append hprefix tailTrace_2910474
  have hstable : (prefixWord ++ tailWord_2910474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910474).length < 2 ^ (prefixWord ++ tailWord_2910474).sum := by decide
  have hdescent : baseEnd_2910474 < baseStart_2910474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910476 : List Nat := [2, 2, 1, 2, 2, 2, 5, 1, 5]
def baseStart_2910476 : Nat := 118140960795 + 2910476 * 2 ^ 59
def prefixEnd_2910476 : Nat := 4983230072969 + 3 ^ 40 * 2910476 * 2
def baseEnd_2910476 : Nat := 332105138083391107325549

theorem tailTrace_2910476 : CollatzResearch.WordTrace tailWord_2910476 prefixEnd_2910476 332105138083391107325549 := by
  unfold tailWord_2910476
  simp only [CollatzResearch.WordTrace]
  refine ⟨53076890301924998286083641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70769187069233331048111521 53076890301924998286083641)
  ·
    refine ⟨39807667726443748714562731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53076890301924998286083641 39807667726443748714562731)
    ·
      refine ⟨59711501589665623071844097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39807667726443748714562731 59711501589665623071844097)
      ·
        refine ⟨44783626192249217303883073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59711501589665623071844097 44783626192249217303883073)
        ·
          refine ⟨33587719644186912977912305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44783626192249217303883073 33587719644186912977912305)
          ·
            refine ⟨25190789733140184733434229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33587719644186912977912305 25190789733140184733434229)
            ·
              refine ⟨2361636537481892318759459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25190789733140184733434229 2361636537481892318759459)
              ·
                refine ⟨3542454806222838478139189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361636537481892318759459 3542454806222838478139189)
                ·
                  refine ⟨332105138083391107325549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542454806222838478139189 332105138083391107325549)
                  ·
                    rfl

theorem cell22_2910476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_2910476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910476 prefixEnd_2910476 := by exact prefixLift 2910476
  have htrace : WordTrace (prefixWord ++ tailWord_2910476) baseStart_2910476 baseEnd_2910476 := by
    simpa [prefixWord, tailWord_2910476, baseEnd_2910476] using wordTrace_append hprefix tailTrace_2910476
  have hstable : (prefixWord ++ tailWord_2910476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910476).length < 2 ^ (prefixWord ++ tailWord_2910476).sum := by decide
  have hdescent : baseEnd_2910476 < baseStart_2910476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910521 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 6]
def baseStart_2910521 : Nat := 118140960795 + 2910521 * 2 ^ 59
def prefixEnd_2910521 : Nat := 4983230072969 + 3 ^ 40 * 2910521 * 2
def baseEnd_2910521 : Nat := 332110272889936068200503

theorem tailTrace_2910521 : CollatzResearch.WordTrace tailWord_2910521 prefixEnd_2910521 332110272889936068200503 := by
  unfold tailWord_2910521
  simp only [CollatzResearch.WordTrace]
  refine ⟨106155421888686969257555417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70770281259124646171703611 106155421888686969257555417)
  ·
    refine ⟨79616566416515226943166563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106155421888686969257555417 79616566416515226943166563)
    ·
      refine ⟨119424849624772840414749845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79616566416515226943166563 119424849624772840414749845)
      ·
        refine ⟨5598039826161226894441399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119424849624772840414749845 5598039826161226894441399)
        ·
          refine ⟨8397059739241840341662099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598039826161226894441399 8397059739241840341662099)
          ·
            refine ⟨12595589608862760512493149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8397059739241840341662099 12595589608862760512493149)
            ·
              refine ⟨4723346103323535192184931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12595589608862760512493149 4723346103323535192184931)
              ·
                refine ⟨7085019154985302788277397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723346103323535192184931 7085019154985302788277397)
                ·
                  refine ⟨332110272889936068200503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7085019154985302788277397 332110272889936068200503)
                  ·
                    rfl

theorem cell22_2910521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 6].length) (baseStart_2910521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910521 prefixEnd_2910521 := by exact prefixLift 2910521
  have htrace : WordTrace (prefixWord ++ tailWord_2910521) baseStart_2910521 baseEnd_2910521 := by
    simpa [prefixWord, tailWord_2910521, baseEnd_2910521] using wordTrace_append hprefix tailTrace_2910521
  have hstable : (prefixWord ++ tailWord_2910521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910521).length < 2 ^ (prefixWord ++ tailWord_2910521).sum := by decide
  have hdescent : baseEnd_2910521 < baseStart_2910521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910551 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 2, 4]
def baseStart_2910551 : Nat := 118140960795 + 2910551 * 2 ^ 59
def prefixEnd_2910551 : Nat := 4983230072969 + 3 ^ 40 * 2910551 * 2
def baseEnd_2910551 : Nat := 996341088282898126351417

theorem tailTrace_2910551 : CollatzResearch.WordTrace tailWord_2910551 prefixEnd_2910551 996341088282898126351417 := by
  unfold tailWord_2910551
  simp only [CollatzResearch.WordTrace]
  refine ⟨106156516078578284381147507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70771010719052189587431671 106156516078578284381147507)
  ·
    refine ⟨159234774117867426571721261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106156516078578284381147507 159234774117867426571721261)
    ·
      refine ⟨59713040294200284964395473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159234774117867426571721261 59713040294200284964395473)
      ·
        refine ⟨44784780220650213723296605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59713040294200284964395473 44784780220650213723296605)
        ·
          refine ⟨16794292582743830146236227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44784780220650213723296605 16794292582743830146236227)
          ·
            refine ⟨25191438874115745219354341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16794292582743830146236227 25191438874115745219354341)
            ·
              refine ⟨4723394788896702228628939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25191438874115745219354341 4723394788896702228628939)
              ·
                refine ⟨7085092183345053342943409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723394788896702228628939 7085092183345053342943409)
                ·
                  refine ⟨5313819137508790007207557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085092183345053342943409 5313819137508790007207557)
                  ·
                    refine ⟨996341088282898126351417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313819137508790007207557 996341088282898126351417)
                    ·
                      rfl

theorem cell22_2910551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_2910551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910551 prefixEnd_2910551 := by exact prefixLift 2910551
  have htrace : WordTrace (prefixWord ++ tailWord_2910551) baseStart_2910551 baseEnd_2910551 := by
    simpa [prefixWord, tailWord_2910551, baseEnd_2910551] using wordTrace_append hprefix tailTrace_2910551
  have hstable : (prefixWord ++ tailWord_2910551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910551).length < 2 ^ (prefixWord ++ tailWord_2910551).sum := by decide
  have hdescent : baseEnd_2910551 < baseStart_2910551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910570 : List Nat := [3, 1, 3, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2910570 : Nat := 118140960795 + 2910570 * 2 ^ 59
def prefixEnd_2910570 : Nat := 4983230072969 + 3 ^ 40 * 2910570 * 2
def baseEnd_2910570 : Nat := 996347592371188410126359

theorem tailTrace_2910570 : CollatzResearch.WordTrace tailWord_2910570 prefixEnd_2910570 996347592371188410126359 := by
  unfold tailWord_2910570
  simp only [CollatzResearch.WordTrace]
  refine ⟨26539302266377362656522291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70771472710339633750726109 26539302266377362656522291)
  ·
    refine ⟨39808953399566043984783437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26539302266377362656522291 39808953399566043984783437)
    ·
      refine ⟨14928357524837266494293789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39808953399566043984783437 14928357524837266494293789)
      ·
        refine ⟨5598134071813974935360171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14928357524837266494293789 5598134071813974935360171)
        ·
          refine ⟨8397201107720962403040257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598134071813974935360171 8397201107720962403040257)
          ·
            refine ⟨6297900830790721802280193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8397201107720962403040257 6297900830790721802280193)
            ·
              refine ⟨4723425623093041351710145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6297900830790721802280193 4723425623093041351710145)
              ·
                refine ⟨3542569217319781013782609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4723425623093041351710145 3542569217319781013782609)
                ·
                  refine ⟨2656926912989835760336957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3542569217319781013782609 2656926912989835760336957)
                  ·
                    refine ⟨996347592371188410126359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2656926912989835760336957 996347592371188410126359)
                    ·
                      rfl

theorem cell22_2910570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2910570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910570 prefixEnd_2910570 := by exact prefixLift 2910570
  have htrace : WordTrace (prefixWord ++ tailWord_2910570) baseStart_2910570 baseEnd_2910570 := by
    simpa [prefixWord, tailWord_2910570, baseEnd_2910570] using wordTrace_append hprefix tailTrace_2910570
  have hstable : (prefixWord ++ tailWord_2910570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910570).length < 2 ^ (prefixWord ++ tailWord_2910570).sum := by decide
  have hdescent : baseEnd_2910570 < baseStart_2910570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910572 : List Nat := [2, 2, 1, 1, 7, 1, 2, 2, 4]
def baseStart_2910572 : Nat := 118140960795 + 2910572 * 2 ^ 59
def prefixEnd_2910572 : Nat := 4983230072969 + 3 ^ 40 * 2910572 * 2
def baseEnd_2910572 : Nat := 332116092337353690525451

theorem tailTrace_2910572 : CollatzResearch.WordTrace tailWord_2910572 prefixEnd_2910572 332116092337353690525451 := by
  unfold tailWord_2910572
  simp only [CollatzResearch.WordTrace]
  refine ⟨53078641005751102483830985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70771521341001469978441313 53078641005751102483830985)
  ·
    refine ⟨39808980754313326862873239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53078641005751102483830985 39808980754313326862873239)
    ·
      refine ⟨59713471131469990294309859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39808980754313326862873239 59713471131469990294309859)
      ·
        refine ⟨89570206697204985441464789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59713471131469990294309859 89570206697204985441464789)
        ·
          refine ⟨2099301719465741846284331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 89570206697204985441464789 2099301719465741846284331)
          ·
            refine ⟨3148952579198612769426497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099301719465741846284331 3148952579198612769426497)
            ·
              refine ⟨2361714434398959577069873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148952579198612769426497 2361714434398959577069873)
              ·
                refine ⟨1771285825799219682802405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361714434398959577069873 1771285825799219682802405)
                ·
                  refine ⟨332116092337353690525451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771285825799219682802405 332116092337353690525451)
                  ·
                    rfl

theorem cell22_2910572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_2910572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910572 prefixEnd_2910572 := by exact prefixLift 2910572
  have htrace : WordTrace (prefixWord ++ tailWord_2910572) baseStart_2910572 baseEnd_2910572 := by
    simpa [prefixWord, tailWord_2910572, baseEnd_2910572] using wordTrace_append hprefix tailTrace_2910572
  have hstable : (prefixWord ++ tailWord_2910572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910572).length < 2 ^ (prefixWord ++ tailWord_2910572).sum := by decide
  have hdescent : baseEnd_2910572 < baseStart_2910572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910602 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 2, 4]
def baseStart_2910602 : Nat := 118140960795 + 2910602 * 2 ^ 59
def prefixEnd_2910602 : Nat := 4983230072969 + 3 ^ 40 * 2910602 * 2
def baseEnd_2910602 : Nat := 996358546625150993326261

theorem tailTrace_2910602 : CollatzResearch.WordTrace tailWord_2910602 prefixEnd_2910602 996358546625150993326261 := by
  unfold tailWord_2910602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26539594050348380022813515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70772250800929013394169373 26539594050348380022813515)
  ·
    refine ⟨39809391075522570034220273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26539594050348380022813515 39809391075522570034220273)
    ·
      refine ⟨29857043306641927525665205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39809391075522570034220273 29857043306641927525665205)
      ·
        refine ⟨2799097809997680705531113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29857043306641927525665205 2799097809997680705531113)
        ·
          refine ⟨2099323357498260529148335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799097809997680705531113 2099323357498260529148335)
          ·
            refine ⟨3148985036247390793722503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099323357498260529148335 3148985036247390793722503)
            ·
              refine ⟨4723477554371086190583755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148985036247390793722503 4723477554371086190583755)
              ·
                refine ⟨7085216331556629285875633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4723477554371086190583755 7085216331556629285875633)
                ·
                  refine ⟨5313912248667471964406725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7085216331556629285875633 5313912248667471964406725)
                  ·
                    refine ⟨996358546625150993326261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5313912248667471964406725 996358546625150993326261)
                    ·
                      rfl

theorem cell22_2910602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_2910602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910602 prefixEnd_2910602 := by exact prefixLift 2910602
  have htrace : WordTrace (prefixWord ++ tailWord_2910602) baseStart_2910602 baseEnd_2910602 := by
    simpa [prefixWord, tailWord_2910602, baseEnd_2910602] using wordTrace_append hprefix tailTrace_2910602
  have hstable : (prefixWord ++ tailWord_2910602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910602).length < 2 ^ (prefixWord ++ tailWord_2910602).sum := by decide
  have hdescent : baseEnd_2910602 < baseStart_2910602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910609 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2910609 : Nat := 118140960795 + 2910609 * 2 ^ 59
def prefixEnd_2910609 : Nat := 4983230072969 + 3 ^ 40 * 2910609 * 2
def baseEnd_2910609 : Nat := 996360942868205308401239

theorem tailTrace_2910609 : CollatzResearch.WordTrace tailWord_2910609 prefixEnd_2910609 996360942868205308401239 := by
  unfold tailWord_2910609
  simp only [CollatzResearch.WordTrace]
  refine ⟨106158631512368160286758881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70772421008245440191172587 106158631512368160286758881)
  ·
    refine ⟨79618973634276120215069161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106158631512368160286758881 79618973634276120215069161)
    ·
      refine ⟨59714230225707090161301871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79618973634276120215069161 59714230225707090161301871)
      ·
        refine ⟨89571345338560635241952807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59714230225707090161301871 89571345338560635241952807)
        ·
          refine ⟨134357018007840952862929211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89571345338560635241952807 134357018007840952862929211)
          ·
            refine ⟨201535527011761429294393817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134357018007840952862929211 201535527011761429294393817)
            ·
              refine ⟨151151645258821071970795363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201535527011761429294393817 151151645258821071970795363)
              ·
                refine ⟨226727467888231607956193045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151151645258821071970795363 226727467888231607956193045)
                ·
                  refine ⟨10627850057260856622946549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 226727467888231607956193045 10627850057260856622946549)
                  ·
                    refine ⟨996360942868205308401239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10627850057260856622946549 996360942868205308401239)
                    ·
                      rfl

theorem cell22_2910609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2910609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910609 prefixEnd_2910609 := by exact prefixLift 2910609
  have htrace : WordTrace (prefixWord ++ tailWord_2910609) baseStart_2910609 baseEnd_2910609 := by
    simpa [prefixWord, tailWord_2910609, baseEnd_2910609] using wordTrace_append hprefix tailTrace_2910609
  have hstable : (prefixWord ++ tailWord_2910609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910609).length < 2 ^ (prefixWord ++ tailWord_2910609).sum := by decide
  have hdescent : baseEnd_2910609 < baseStart_2910609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910626 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2910626 : Nat := 118140960795 + 2910626 * 2 ^ 59
def prefixEnd_2910626 : Nat := 4983230072969 + 3 ^ 40 * 2910626 * 2
def baseEnd_2910626 : Nat := 996366762315622930726187

theorem tailTrace_2910626 : CollatzResearch.WordTrace tailWord_2910626 prefixEnd_2910626 996366762315622930726187 := by
  unfold tailWord_2910626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26539812888326643047531933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70772834368871048126751821 26539812888326643047531933)
  ·
    refine ⟨9952429833122491142824475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26539812888326643047531933 9952429833122491142824475)
    ·
      refine ⟨14928644749683736714236713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9952429833122491142824475 14928644749683736714236713)
      ·
        refine ⟨11196483562262802535677535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14928644749683736714236713 11196483562262802535677535)
        ·
          refine ⟨16794725343394203803516303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11196483562262802535677535 16794725343394203803516303)
          ·
            refine ⟨25192088015091305705274455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16794725343394203803516303 25192088015091305705274455)
            ·
              refine ⟨37788132022636958557911683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25192088015091305705274455 37788132022636958557911683)
              ·
                refine ⟨56682198033955437836867525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37788132022636958557911683 56682198033955437836867525)
                ·
                  refine ⟨10627912131366644594412661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56682198033955437836867525 10627912131366644594412661)
                  ·
                    refine ⟨996366762315622930726187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10627912131366644594412661 996366762315622930726187)
                    ·
                      rfl

theorem cell22_2910626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2910626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910626 prefixEnd_2910626 := by exact prefixLift 2910626
  have htrace : WordTrace (prefixWord ++ tailWord_2910626) baseStart_2910626 baseEnd_2910626 := by
    simpa [prefixWord, tailWord_2910626, baseEnd_2910626] using wordTrace_append hprefix tailTrace_2910626
  have hstable : (prefixWord ++ tailWord_2910626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910626).length < 2 ^ (prefixWord ++ tailWord_2910626).sum := by decide
  have hdescent : baseEnd_2910626 < baseStart_2910626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910632 : List Nat := [2, 1, 6, 1, 1, 1, 2, 4, 1, 3]
def baseStart_2910632 : Nat := 118140960795 + 2910632 * 2 ^ 59
def prefixEnd_2910632 : Nat := 4983230072969 + 3 ^ 40 * 2910632 * 2
def baseEnd_2910632 : Nat := 996368816238240915076169

theorem tailTrace_2910632 : CollatzResearch.WordTrace tailWord_2910632 prefixEnd_2910632 996368816238240915076169 := by
  unfold tailWord_2910632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53079735195642417607423075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70772980260856556809897433 53079735195642417607423075)
  ·
    refine ⟨79619602793463626411134613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53079735195642417607423075 79619602793463626411134613)
    ·
      refine ⟨3732168880943607488021935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79619602793463626411134613 3732168880943607488021935)
      ·
        refine ⟨5598253321415411232032903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732168880943607488021935 5598253321415411232032903)
        ·
          refine ⟨8397379982123116848049355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598253321415411232032903 8397379982123116848049355)
          ·
            refine ⟨12596069973184675272074033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8397379982123116848049355 12596069973184675272074033)
            ·
              refine ⟨9447052479888506454055525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12596069973184675272074033 9447052479888506454055525)
              ·
                refine ⟨1771322339979094960135411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9447052479888506454055525 1771322339979094960135411)
                ·
                  refine ⟨2656983509968642440203117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771322339979094960135411 2656983509968642440203117)
                  ·
                    refine ⟨996368816238240915076169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2656983509968642440203117 996368816238240915076169)
                    ·
                      rfl

theorem cell22_2910632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_2910632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910632 prefixEnd_2910632 := by exact prefixLift 2910632
  have htrace : WordTrace (prefixWord ++ tailWord_2910632) baseStart_2910632 baseEnd_2910632 := by
    simpa [prefixWord, tailWord_2910632, baseEnd_2910632] using wordTrace_append hprefix tailTrace_2910632
  have hstable : (prefixWord ++ tailWord_2910632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910632).length < 2 ^ (prefixWord ++ tailWord_2910632).sum := by decide
  have hdescent : baseEnd_2910632 < baseStart_2910632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910645 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 5]
def baseStart_2910645 : Nat := 118140960795 + 2910645 * 2 ^ 59
def prefixEnd_2910645 : Nat := 4983230072969 + 3 ^ 40 * 2910645 * 2
def baseEnd_2910645 : Nat := 332124422134637738167043

theorem tailTrace_2910645 : CollatzResearch.WordTrace tailWord_2910645 prefixEnd_2910645 332124422134637738167043 := by
  unfold tailWord_2910645
  simp only [CollatzResearch.WordTrace]
  refine ⟨106159944540237738435069389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70773296360158492290046259 106159944540237738435069389)
  ·
    refine ⟨39809979202589151913151021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106159944540237738435069389 39809979202589151913151021)
    ·
      refine ⟨14928742200970931967431633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39809979202589151913151021 14928742200970931967431633)
      ·
        refine ⟨11196556650728198975573725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14928742200970931967431633 11196556650728198975573725)
        ·
          refine ⟨4198708744023074615840147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11196556650728198975573725 4198708744023074615840147)
          ·
            refine ⟨6298063116034611923760221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4198708744023074615840147 6298063116034611923760221)
            ·
              refine ⟨2361773668512979471410083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6298063116034611923760221 2361773668512979471410083)
              ·
                refine ⟨3542660502769469207115125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361773668512979471410083 3542660502769469207115125)
                ·
                  refine ⟨332124422134637738167043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542660502769469207115125 332124422134637738167043)
                  ·
                    rfl

theorem cell22_2910645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_2910645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910645 prefixEnd_2910645 := by exact prefixLift 2910645
  have htrace : WordTrace (prefixWord ++ tailWord_2910645) baseStart_2910645 baseEnd_2910645 := by
    simpa [prefixWord, tailWord_2910645, baseEnd_2910645] using wordTrace_append hprefix tailTrace_2910645
  have hstable : (prefixWord ++ tailWord_2910645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910645).length < 2 ^ (prefixWord ++ tailWord_2910645).sum := by decide
  have hdescent : baseEnd_2910645 < baseStart_2910645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910688 : List Nat := [2, 1, 1, 3, 1, 1, 4, 4, 2, 3]
def baseStart_2910688 : Nat := 118140960795 + 2910688 * 2 ^ 59
def prefixEnd_2910688 : Nat := 4983230072969 + 3 ^ 40 * 2910688 * 2
def baseEnd_2910688 : Nat := 996387986182675435675997

theorem tailTrace_2910688 : CollatzResearch.WordTrace tailWord_2910688 prefixEnd_2910688 996387986182675435675997 := by
  unfold tailWord_2910688
  simp only [CollatzResearch.WordTrace]
  refine ⟨53080756439540978389442359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70774341919387971185923145 53080756439540978389442359)
  ·
    refine ⟨79621134659311467584163539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53080756439540978389442359 79621134659311467584163539)
    ·
      refine ⟨119431701988967201376245309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79621134659311467584163539 119431701988967201376245309)
      ·
        refine ⟨44786888245862700516091991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119431701988967201376245309 44786888245862700516091991)
        ·
          refine ⟨67180332368794050774137987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44786888245862700516091991 67180332368794050774137987)
          ·
            refine ⟨100770498553191076161206981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67180332368794050774137987 100770498553191076161206981)
            ·
              refine ⟨18894468478723326780226309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100770498553191076161206981 18894468478723326780226309)
              ·
                refine ⟨3542712839760623771292433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18894468478723326780226309 3542712839760623771292433)
                ·
                  refine ⟨2657034629820467828469325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3542712839760623771292433 2657034629820467828469325)
                  ·
                    refine ⟨996387986182675435675997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657034629820467828469325 996387986182675435675997)
                    ·
                      rfl

theorem cell22_2910688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 4, 2, 3].length) (baseStart_2910688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910688 prefixEnd_2910688 := by exact prefixLift 2910688
  have htrace : WordTrace (prefixWord ++ tailWord_2910688) baseStart_2910688 baseEnd_2910688 := by
    simpa [prefixWord, tailWord_2910688, baseEnd_2910688] using wordTrace_append hprefix tailTrace_2910688
  have hstable : (prefixWord ++ tailWord_2910688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910688).length < 2 ^ (prefixWord ++ tailWord_2910688).sum := by decide
  have hdescent : baseEnd_2910688 < baseStart_2910688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910709 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2910709 : Nat := 118140960795 + 2910709 * 2 ^ 59
def prefixEnd_2910709 : Nat := 4983230072969 + 3 ^ 40 * 2910709 * 2
def baseEnd_2910709 : Nat := 996395174911838380900933

theorem tailTrace_2910709 : CollatzResearch.WordTrace tailWord_2910709 prefixEnd_2910709 996395174911838380900933 := by
  unfold tailWord_2910709
  simp only [CollatzResearch.WordTrace]
  refine ⟨106162278812005877365399181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70774852541337251576932787 106162278812005877365399181)
  ·
    refine ⟨39810854554502204012024693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106162278812005877365399181 39810854554502204012024693)
    ·
      refine ⟨3732267614484581626127315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39810854554502204012024693 3732267614484581626127315)
      ·
        refine ⟨5598401421726872439190973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732267614484581626127315 5598401421726872439190973)
        ·
          refine ⟨2099400533147577164696615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5598401421726872439190973 2099400533147577164696615)
          ·
            refine ⟨3149100799721365747044923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099400533147577164696615 3149100799721365747044923)
            ·
              refine ⟨4723651199582048620567385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149100799721365747044923 4723651199582048620567385)
              ·
                refine ⟨3542738399686536465425539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4723651199582048620567385 3542738399686536465425539)
                ·
                  refine ⟨5314107599529804698138309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542738399686536465425539 5314107599529804698138309)
                  ·
                    refine ⟨996395174911838380900933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314107599529804698138309 996395174911838380900933)
                    ·
                      rfl

theorem cell22_2910709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2910709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910709 prefixEnd_2910709 := by exact prefixLift 2910709
  have htrace : WordTrace (prefixWord ++ tailWord_2910709) baseStart_2910709 baseEnd_2910709 := by
    simpa [prefixWord, tailWord_2910709, baseEnd_2910709] using wordTrace_append hprefix tailTrace_2910709
  have hstable : (prefixWord ++ tailWord_2910709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910709).length < 2 ^ (prefixWord ++ tailWord_2910709).sum := by decide
  have hdescent : baseEnd_2910709 < baseStart_2910709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910726 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2910726 : Nat := 118140960795 + 2910726 * 2 ^ 59
def prefixEnd_2910726 : Nat := 4983230072969 + 3 ^ 40 * 2910726 * 2
def baseEnd_2910726 : Nat := 996400994359256003225881

theorem tailTrace_2910726 : CollatzResearch.WordTrace tailWord_2910726 prefixEnd_2910726 996400994359256003225881 := by
  unfold tailWord_2910726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3317590589154509039649001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70775265901962859512512021 3317590589154509039649001)
  ·
    refine ⟨2488192941865881779736751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3317590589154509039649001 2488192941865881779736751)
    ·
      refine ⟨3732289412798822669605127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488192941865881779736751 3732289412798822669605127)
      ·
        refine ⟨5598434119198234004407691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732289412798822669605127 5598434119198234004407691)
        ·
          refine ⟨8397651178797351006611537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5598434119198234004407691 8397651178797351006611537)
          ·
            refine ⟨6298238384098013254958653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8397651178797351006611537 6298238384098013254958653)
            ·
              refine ⟨2361839394036754970609495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6298238384098013254958653 2361839394036754970609495)
              ·
                refine ⟨3542759091055132455914243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361839394036754970609495 3542759091055132455914243)
                ·
                  refine ⟨5314138636582698683871365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542759091055132455914243 5314138636582698683871365)
                  ·
                    refine ⟨996400994359256003225881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314138636582698683871365 996400994359256003225881)
                    ·
                      rfl

theorem cell22_2910726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2910726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910726 prefixEnd_2910726 := by exact prefixLift 2910726
  have htrace : WordTrace (prefixWord ++ tailWord_2910726) baseStart_2910726 baseEnd_2910726 := by
    simpa [prefixWord, tailWord_2910726, baseEnd_2910726] using wordTrace_append hprefix tailTrace_2910726
  have hstable : (prefixWord ++ tailWord_2910726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910726).length < 2 ^ (prefixWord ++ tailWord_2910726).sum := by decide
  have hdescent : baseEnd_2910726 < baseStart_2910726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910746 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_2910746 : Nat := 118140960795 + 2910746 * 2 ^ 59
def prefixEnd_2910746 : Nat := 4983230072969 + 3 ^ 40 * 2910746 * 2
def baseEnd_2910746 : Nat := 332135946922660872575273

theorem tailTrace_2910746 : CollatzResearch.WordTrace tailWord_2910746 prefixEnd_2910746 332135946922660872575273 := by
  unfold tailWord_2910746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26540907078217958171124023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70775752208581221789664061 26540907078217958171124023)
  ·
    refine ⟨39811360617326937256686035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26540907078217958171124023 39811360617326937256686035)
    ·
      refine ⟨59717040925990405885029053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39811360617326937256686035 59717040925990405885029053)
      ·
        refine ⟨22393890347246402206885895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59717040925990405885029053 22393890347246402206885895)
        ·
          refine ⟨33590835520869603310328843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22393890347246402206885895 33590835520869603310328843)
          ·
            refine ⟨50386253281304404965493265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33590835520869603310328843 50386253281304404965493265)
            ·
              refine ⟨37789689960978303724119949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50386253281304404965493265 37789689960978303724119949)
              ·
                refine ⟨14171133735366863896544981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37789689960978303724119949 14171133735366863896544981)
                ·
                  refine ⟨332135946922660872575273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14171133735366863896544981 332135946922660872575273)
                  ·
                    rfl

theorem cell22_2910746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_2910746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910746 prefixEnd_2910746 := by exact prefixLift 2910746
  have htrace : WordTrace (prefixWord ++ tailWord_2910746) baseStart_2910746 baseEnd_2910746 := by
    simpa [prefixWord, tailWord_2910746, baseEnd_2910746] using wordTrace_append hprefix tailTrace_2910746
  have hstable : (prefixWord ++ tailWord_2910746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910746).length < 2 ^ (prefixWord ++ tailWord_2910746).sum := by decide
  have hdescent : baseEnd_2910746 < baseStart_2910746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910797 : List Nat := [1, 6, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2910797 : Nat := 118140960795 + 2910797 * 2 ^ 59
def prefixEnd_2910797 : Nat := 4983230072969 + 3 ^ 40 * 2910797 * 2
def baseEnd_2910797 : Nat := 332141766370078494900221

theorem tailTrace_2910797 : CollatzResearch.WordTrace tailWord_2910797 prefixEnd_2910797 332141766370078494900221 := by
  unfold tailWord_2910797
  simp only [CollatzResearch.WordTrace]
  refine ⟨106165488435687068394602645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70776992290458045596401763 106165488435687068394602645)
  ·
    refine ⟨4976507270422831330996999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106165488435687068394602645 4976507270422831330996999)
    ·
      refine ⟨7464760905634246996495499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4976507270422831330996999 7464760905634246996495499)
      ·
        refine ⟨11197141358451370494743249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7464760905634246996495499 11197141358451370494743249)
        ·
          refine ⟨8397856018838527871057437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11197141358451370494743249 8397856018838527871057437)
          ·
            refine ⟨3149196007064447951646539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8397856018838527871057437 3149196007064447951646539)
            ·
              refine ⟨4723794010596671927469809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149196007064447951646539 4723794010596671927469809)
              ·
                refine ⟨3542845507947503945602357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4723794010596671927469809 3542845507947503945602357)
                ·
                  refine ⟨332141766370078494900221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542845507947503945602357 332141766370078494900221)
                  ·
                    rfl

theorem cell22_2910797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2910797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910797 prefixEnd_2910797 := by exact prefixLift 2910797
  have htrace : WordTrace (prefixWord ++ tailWord_2910797) baseStart_2910797 baseEnd_2910797 := by
    simpa [prefixWord, tailWord_2910797, baseEnd_2910797] using wordTrace_append hprefix tailTrace_2910797
  have hstable : (prefixWord ++ tailWord_2910797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910797).length < 2 ^ (prefixWord ++ tailWord_2910797).sum := by decide
  have hdescent : baseEnd_2910797 < baseStart_2910797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910853 : List Nat := [1, 3, 1, 1, 4, 4, 8]
def baseStart_2910853 : Nat := 118140960795 + 2910853 * 2 ^ 59
def prefixEnd_2910853 : Nat := 4983230072969 + 3 ^ 40 * 2910853 * 2
def baseEnd_2910853 : Nat := 36905350705728518714833

theorem tailTrace_2910853 : CollatzResearch.WordTrace tailWord_2910853 prefixEnd_2910853 36905350705728518714833 := by
  unfold tailWord_2910853
  simp only [CollatzResearch.WordTrace]
  refine ⟨106167530923484189958641213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70778353948989459972427475 106167530923484189958641213)
  ·
    refine ⟨39812824096306571234490455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106167530923484189958641213 39812824096306571234490455)
    ·
      refine ⟨59719236144459856851735683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39812824096306571234490455 59719236144459856851735683)
      ·
        refine ⟨89578854216689785277603525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59719236144459856851735683 89578854216689785277603525)
        ·
          refine ⟨16796035165629334739550661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89578854216689785277603525 16796035165629334739550661)
          ·
            refine ⟨3149256593555500263665749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16796035165629334739550661 3149256593555500263665749)
            ·
              refine ⟨36905350705728518714833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3149256593555500263665749 36905350705728518714833)
              ·
                rfl

theorem cell22_2910853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 8].length) (baseStart_2910853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910853 prefixEnd_2910853 := by exact prefixLift 2910853
  have htrace : WordTrace (prefixWord ++ tailWord_2910853) baseStart_2910853 baseEnd_2910853 := by
    simpa [prefixWord, tailWord_2910853, baseEnd_2910853] using wordTrace_append hprefix tailTrace_2910853
  have hstable : (prefixWord ++ tailWord_2910853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910853).length < 2 ^ (prefixWord ++ tailWord_2910853).sum := by decide
  have hdescent : baseEnd_2910853 < baseStart_2910853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910874 : List Nat := [3, 1, 1, 6, 1, 1, 1, 3, 2, 3]
def baseStart_2910874 : Nat := 118140960795 + 2910874 * 2 ^ 59
def prefixEnd_2910874 : Nat := 4983230072969 + 3 ^ 40 * 2910874 * 2
def baseEnd_2910874 : Nat := 996451657783832950525427

theorem tailTrace_2910874 : CollatzResearch.WordTrace tailWord_2910874 prefixEnd_2910874 996451657783832950525427 := by
  unfold tailWord_2910874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26542074214102027636288919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70778864570938740363437117 26542074214102027636288919)
  ·
    refine ⟨39813111321153041454433379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26542074214102027636288919 39813111321153041454433379)
    ·
      refine ⟨59719666981729562181650069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39813111321153041454433379 59719666981729562181650069)
      ·
        refine ⟨2799359389768573227264847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59719666981729562181650069 2799359389768573227264847)
        ·
          refine ⟨4199039084652859840897271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799359389768573227264847 4199039084652859840897271)
          ·
            refine ⟨6298558626979289761345907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199039084652859840897271 6298558626979289761345907)
            ·
              refine ⟨9447837940468934642018861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298558626979289761345907 9447837940468934642018861)
              ·
                refine ⟨3542939227675850490757073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9447837940468934642018861 3542939227675850490757073)
                ·
                  refine ⟨2657204420756887868067805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3542939227675850490757073 2657204420756887868067805)
                  ·
                    refine ⟨996451657783832950525427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657204420756887868067805 996451657783832950525427)
                    ·
                      rfl

theorem cell22_2910874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 3, 2, 3].length) (baseStart_2910874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910874 prefixEnd_2910874 := by exact prefixLift 2910874
  have htrace : WordTrace (prefixWord ++ tailWord_2910874) baseStart_2910874 baseEnd_2910874 := by
    simpa [prefixWord, tailWord_2910874, baseEnd_2910874] using wordTrace_append hprefix tailTrace_2910874
  have hstable : (prefixWord ++ tailWord_2910874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910874).length < 2 ^ (prefixWord ++ tailWord_2910874).sum := by decide
  have hdescent : baseEnd_2910874 < baseStart_2910874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910943 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 8]
def baseStart_2910943 : Nat := 118140960795 + 2910943 * 2 ^ 59
def prefixEnd_2910943 : Nat := 4983230072969 + 3 ^ 40 * 2910943 * 2
def baseEnd_2910943 : Nat := 332158425964646590183405

theorem tailTrace_2910943 : CollatzResearch.WordTrace tailWord_2910943 prefixEnd_2910943 332158425964646590183405 := by
  unfold tailWord_2910943
  simp only [CollatzResearch.WordTrace]
  refine ⟨106170813493158135329417483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70780542328772090219611655 106170813493158135329417483)
  ·
    refine ⟨159256220239737202994126225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106170813493158135329417483 159256220239737202994126225)
    ·
      refine ⟨119442165179802902245594669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159256220239737202994126225 119442165179802902245594669)
      ·
        refine ⟨44790811942426088342098001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119442165179802902245594669 44790811942426088342098001)
        ·
          refine ⟨33593108956819566256573501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44790811942426088342098001 33593108956819566256573501)
          ·
            refine ⟨12597415858807337346215063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33593108956819566256573501 12597415858807337346215063)
            ·
              refine ⟨18896123788211006019322595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597415858807337346215063 18896123788211006019322595)
              ·
                refine ⟨28344185682316509028983893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18896123788211006019322595 28344185682316509028983893)
                ·
                  refine ⟨332158425964646590183405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28344185682316509028983893 332158425964646590183405)
                  ·
                    rfl

theorem cell22_2910943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 8].length) (baseStart_2910943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910943 prefixEnd_2910943 := by exact prefixLift 2910943
  have htrace : WordTrace (prefixWord ++ tailWord_2910943) baseStart_2910943 baseEnd_2910943 := by
    simpa [prefixWord, tailWord_2910943, baseEnd_2910943] using wordTrace_append hprefix tailTrace_2910943
  have hstable : (prefixWord ++ tailWord_2910943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910943).length < 2 ^ (prefixWord ++ tailWord_2910943).sum := by decide
  have hdescent : baseEnd_2910943 < baseStart_2910943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910945 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 3, 4]
def baseStart_2910945 : Nat := 118140960795 + 2910945 * 2 ^ 59
def prefixEnd_2910945 : Nat := 4983230072969 + 3 ^ 40 * 2910945 * 2
def baseEnd_2910945 : Nat := 996475962534812432000209

theorem tailTrace_2910945 : CollatzResearch.WordTrace tailWord_2910945 prefixEnd_2910945 996475962534812432000209 := by
  unfold tailWord_2910945
  simp only [CollatzResearch.WordTrace]
  refine ⟨106170886439150889670990289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70780590959433926447326859 106170886439150889670990289)
  ·
    refine ⟨79628164829363167253242717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106170886439150889670990289 79628164829363167253242717)
    ·
      refine ⟨29860561811011187719966019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79628164829363167253242717 29860561811011187719966019)
      ·
        refine ⟨44790842716516781579949029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29860561811011187719966019 44790842716516781579949029)
        ·
          refine ⟨8398283009346896546240443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44790842716516781579949029 8398283009346896546240443)
          ·
            refine ⟨12597424514020344819360665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398283009346896546240443 12597424514020344819360665)
            ·
              refine ⟨9448068385515258614520499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12597424514020344819360665 9448068385515258614520499)
              ·
                refine ⟨14172102578272887921780749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9448068385515258614520499 14172102578272887921780749)
                ·
                  refine ⟨5314538466852332970667781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14172102578272887921780749 5314538466852332970667781)
                  ·
                    refine ⟨996475962534812432000209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314538466852332970667781 996475962534812432000209)
                    ·
                      rfl

theorem cell22_2910945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_2910945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910945 prefixEnd_2910945 := by exact prefixLift 2910945
  have htrace : WordTrace (prefixWord ++ tailWord_2910945) baseStart_2910945 baseEnd_2910945 := by
    simpa [prefixWord, tailWord_2910945, baseEnd_2910945] using wordTrace_append hprefix tailTrace_2910945
  have hstable : (prefixWord ++ tailWord_2910945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910945).length < 2 ^ (prefixWord ++ tailWord_2910945).sum := by decide
  have hdescent : baseEnd_2910945 < baseStart_2910945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910962 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 1, 4]
def baseStart_2910962 : Nat := 118140960795 + 2910962 * 2 ^ 59
def prefixEnd_2910962 : Nat := 4983230072969 + 3 ^ 40 * 2910962 * 2
def baseEnd_2910962 : Nat := 996481781982230054325157

theorem tailTrace_2910962 : CollatzResearch.WordTrace tailWord_2910962 prefixEnd_2910962 996481781982230054325157 := by
  unfold tailWord_2910962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26542876620022325393589785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70781004320059534382906093 26542876620022325393589785)
  ·
    refine ⟨19907157465016744045192339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26542876620022325393589785 19907157465016744045192339)
    ·
      refine ⟨29860736197525116067788509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19907157465016744045192339 29860736197525116067788509)
      ·
        refine ⟨11197776074071918525420691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29860736197525116067788509 11197776074071918525420691)
        ·
          refine ⟨16796664111107877788131037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197776074071918525420691 16796664111107877788131037)
          ·
            refine ⟨6298749041665454170549139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16796664111107877788131037 6298749041665454170549139)
            ·
              refine ⟨9448123562498181255823709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6298749041665454170549139 9448123562498181255823709)
              ·
                refine ⟨3543046335936817970933891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9448123562498181255823709 3543046335936817970933891)
                ·
                  refine ⟨5314569503905226956400837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543046335936817970933891 5314569503905226956400837)
                  ·
                    refine ⟨996481781982230054325157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5314569503905226956400837 996481781982230054325157)
                    ·
                      rfl

theorem cell22_2910962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_2910962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910962 prefixEnd_2910962 := by exact prefixLift 2910962
  have htrace : WordTrace (prefixWord ++ tailWord_2910962) baseStart_2910962 baseEnd_2910962 := by
    simpa [prefixWord, tailWord_2910962, baseEnd_2910962] using wordTrace_append hprefix tailTrace_2910962
  have hstable : (prefixWord ++ tailWord_2910962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910962).length < 2 ^ (prefixWord ++ tailWord_2910962).sum := by decide
  have hdescent : baseEnd_2910962 < baseStart_2910962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2910988 : List Nat := [2, 2, 1, 2, 2, 1, 1, 11]
def baseStart_2910988 : Nat := 118140960795 + 2910988 * 2 ^ 59
def prefixEnd_2910988 : Nat := 4983230072969 + 3 ^ 40 * 2910988 * 2
def baseEnd_2910988 : Nat := 110721186923730517019453

theorem tailTrace_2910988 : CollatzResearch.WordTrace tailWord_2910988 prefixEnd_2910988 110721186923730517019453 := by
  unfold tailWord_2910988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53086227388997554007402809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70781636518663405343203745 53086227388997554007402809)
  ·
    refine ⟨39814670541748165505552107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53086227388997554007402809 39814670541748165505552107)
    ·
      refine ⟨59722005812622248258328161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39814670541748165505552107 59722005812622248258328161)
      ·
        refine ⟨44791504359466686193746121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59722005812622248258328161 44791504359466686193746121)
        ·
          refine ⟨33593628269600014645309591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44791504359466686193746121 33593628269600014645309591)
          ·
            refine ⟨50390442404400021967964387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33593628269600014645309591 50390442404400021967964387)
            ·
              refine ⟨75585663606600032951946581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50390442404400021967964387 75585663606600032951946581)
              ·
                refine ⟨110721186923730517019453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 75585663606600032951946581 110721186923730517019453)
                ·
                  rfl

theorem cell22_2910988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 11].length) (baseStart_2910988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2910988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2910988 prefixEnd_2910988 := by exact prefixLift 2910988
  have htrace : WordTrace (prefixWord ++ tailWord_2910988) baseStart_2910988 baseEnd_2910988 := by
    simpa [prefixWord, tailWord_2910988, baseEnd_2910988] using wordTrace_append hprefix tailTrace_2910988
  have hstable : (prefixWord ++ tailWord_2910988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2910988).length < 2 ^ (prefixWord ++ tailWord_2910988).sum := by decide
  have hdescent : baseEnd_2910988 < baseStart_2910988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2910988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911022 : List Nat := [4, 1, 3, 2, 1, 3, 8]
def baseStart_2911022 : Nat := 118140960795 + 2911022 * 2 ^ 59
def prefixEnd_2911022 : Nat := 4983230072969 + 3 ^ 40 * 2911022 * 2
def baseEnd_2911022 : Nat := 36907493378089255474999

theorem tailTrace_2911022 : CollatzResearch.WordTrace tailWord_2911022 prefixEnd_2911022 36907493378089255474999 := by
  unfold tailWord_2911022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271711857483991477692915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70782463239914621214362213 13271711857483991477692915)
  ·
    refine ⟨19907567786225987216539373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13271711857483991477692915 19907567786225987216539373)
    ·
      refine ⟨7465337919834745206202265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19907567786225987216539373 7465337919834745206202265)
      ·
        refine ⟨5599003439876058904651699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7465337919834745206202265 5599003439876058904651699)
        ·
          refine ⟨8398505159814088356977549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599003439876058904651699 8398505159814088356977549)
          ·
            refine ⟨3149439434930283133866581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8398505159814088356977549 3149439434930283133866581)
            ·
              refine ⟨36907493378089255474999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3149439434930283133866581 36907493378089255474999)
              ·
                rfl

theorem cell22_2911022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 8].length) (baseStart_2911022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911022 prefixEnd_2911022 := by exact prefixLift 2911022
  have htrace : WordTrace (prefixWord ++ tailWord_2911022) baseStart_2911022 baseEnd_2911022 := by
    simpa [prefixWord, tailWord_2911022, baseEnd_2911022] using wordTrace_append hprefix tailTrace_2911022
  have hstable : (prefixWord ++ tailWord_2911022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911022).length < 2 ^ (prefixWord ++ tailWord_2911022).sum := by decide
  have hdescent : baseEnd_2911022 < baseStart_2911022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911112 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 6]
def baseStart_2911112 : Nat := 118140960795 + 2911112 * 2 ^ 59
def prefixEnd_2911112 : Nat := 4983230072969 + 3 ^ 40 * 2911112 * 2
def baseEnd_2911112 : Nat := 332177710015893221024899

theorem tailTrace_2911112 : CollatzResearch.WordTrace tailWord_2911112 prefixEnd_2911112 332177710015893221024899 := by
  unfold tailWord_2911112
  simp only [CollatzResearch.WordTrace]
  refine ⟨53088488714772938596159795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70784651619697251461546393 53088488714772938596159795)
  ·
    refine ⟨79632733072159407894239693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53088488714772938596159795 79632733072159407894239693)
    ·
      refine ⟨29862274902059777960339885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79632733072159407894239693 29862274902059777960339885)
      ·
        refine ⟨11198353088272416735127457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29862274902059777960339885 11198353088272416735127457)
        ·
          refine ⟨8398764816204312551345593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11198353088272416735127457 8398764816204312551345593)
          ·
            refine ⟨6299073612153234413509195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8398764816204312551345593 6299073612153234413509195)
            ·
              refine ⟨9448610418229851620263793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299073612153234413509195 9448610418229851620263793)
              ·
                refine ⟨7086457813672388715197845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9448610418229851620263793 7086457813672388715197845)
                ·
                  refine ⟨332177710015893221024899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7086457813672388715197845 332177710015893221024899)
                  ·
                    rfl

theorem cell22_2911112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_2911112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911112 prefixEnd_2911112 := by exact prefixLift 2911112
  have htrace : WordTrace (prefixWord ++ tailWord_2911112) baseStart_2911112 baseEnd_2911112 := by
    simpa [prefixWord, tailWord_2911112, baseEnd_2911112] using wordTrace_append hprefix tailTrace_2911112
  have hstable : (prefixWord ++ tailWord_2911112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911112).length < 2 ^ (prefixWord ++ tailWord_2911112).sum := by decide
  have hdescent : baseEnd_2911112 < baseStart_2911112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911127 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 4, 3]
def baseStart_2911127 : Nat := 118140960795 + 2911127 * 2 ^ 59
def prefixEnd_2911127 : Nat := 4983230072969 + 3 ^ 40 * 2911127 * 2
def baseEnd_2911127 : Nat := 996538264854224623949651

theorem tailTrace_2911127 : CollatzResearch.WordTrace tailWord_2911127 prefixEnd_2911127 996538264854224623949651 := by
  unfold tailWord_2911127
  simp only [CollatzResearch.WordTrace]
  refine ⟨106177524524491534754115635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70785016349661023169410423 106177524524491534754115635)
  ·
    refine ⟨159266286786737302131173453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106177524524491534754115635 159266286786737302131173453)
    ·
      refine ⟨59724857545026488299190045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159266286786737302131173453 59724857545026488299190045)
      ·
        refine ⟨22396821579384933112196267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59724857545026488299190045 22396821579384933112196267)
        ·
          refine ⟨33595232369077399668294401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22396821579384933112196267 33595232369077399668294401)
          ·
            refine ⟨25196424276808049751220801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33595232369077399668294401 25196424276808049751220801)
            ·
              refine ⟨18897318207606037313415601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25196424276808049751220801 18897318207606037313415601)
              ·
                refine ⟨14172988655704527985061701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18897318207606037313415601 14172988655704527985061701)
                ·
                  refine ⟨2657435372944598997199069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14172988655704527985061701 2657435372944598997199069)
                  ·
                    refine ⟨996538264854224623949651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657435372944598997199069 996538264854224623949651)
                    ·
                      rfl

theorem cell22_2911127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_2911127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911127 prefixEnd_2911127 := by exact prefixLift 2911127
  have htrace : WordTrace (prefixWord ++ tailWord_2911127) baseStart_2911127 baseEnd_2911127 := by
    simpa [prefixWord, tailWord_2911127, baseEnd_2911127] using wordTrace_append hprefix tailTrace_2911127
  have hstable : (prefixWord ++ tailWord_2911127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911127).length < 2 ^ (prefixWord ++ tailWord_2911127).sum := by decide
  have hdescent : baseEnd_2911127 < baseStart_2911127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911140 : List Nat := [2, 3, 1, 2, 1, 2, 11]
def baseStart_2911140 : Nat := 118140960795 + 2911140 * 2 ^ 59
def prefixEnd_2911140 : Nat := 4983230072969 + 3 ^ 40 * 2911140 * 2
def baseEnd_2911140 : Nat := 36908989445181367532393

theorem tailTrace_2911140 : CollatzResearch.WordTrace tailWord_2911140 prefixEnd_2911140 36908989445181367532393 := by
  unfold tailWord_2911140
  simp only [CollatzResearch.WordTrace]
  refine ⟨53088999336722218987169437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70785332448962958649559249 53088999336722218987169437)
  ·
    refine ⟨19908374751270832120188539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53088999336722218987169437 19908374751270832120188539)
    ·
      refine ⟨29862562126906248180282809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19908374751270832120188539 29862562126906248180282809)
      ·
        refine ⟨22396921595179686135212107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29862562126906248180282809 22396921595179686135212107)
        ·
          refine ⟨33595382392769529202818161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22396921595179686135212107 33595382392769529202818161)
          ·
            refine ⟨25196536794577146902113621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33595382392769529202818161 25196536794577146902113621)
            ·
              refine ⟨36908989445181367532393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25196536794577146902113621 36908989445181367532393)
              ·
                rfl

theorem cell22_2911140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 11].length) (baseStart_2911140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911140 prefixEnd_2911140 := by exact prefixLift 2911140
  have htrace : WordTrace (prefixWord ++ tailWord_2911140) baseStart_2911140 baseEnd_2911140 := by
    simpa [prefixWord, tailWord_2911140, baseEnd_2911140] using wordTrace_append hprefix tailTrace_2911140
  have hstable : (prefixWord ++ tailWord_2911140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911140).length < 2 ^ (prefixWord ++ tailWord_2911140).sum := by decide
  have hdescent : baseEnd_2911140 < baseStart_2911140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911161 : List Nat := [1, 2, 1, 4, 2, 3, 3, 1, 2, 3]
def baseStart_2911161 : Nat := 118140960795 + 2911161 * 2 ^ 59
def prefixEnd_2911161 : Nat := 4983230072969 + 3 ^ 40 * 2911161 * 2
def baseEnd_2911161 : Nat := 996549903749059868599547

theorem tailTrace_2911161 : CollatzResearch.WordTrace tailWord_2911161 prefixEnd_2911161 996549903749059868599547 := by
  unfold tailWord_2911161
  simp only [CollatzResearch.WordTrace]
  refine ⟨106178764606368358560853337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70785843070912239040568891 106178764606368358560853337)
  ·
    refine ⟨79634073454776268920640003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106178764606368358560853337 79634073454776268920640003)
    ·
      refine ⟨119451110182164403380960005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79634073454776268920640003 119451110182164403380960005)
      ·
        refine ⟨22397083159155825633930001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119451110182164403380960005 22397083159155825633930001)
        ·
          refine ⟨16797812369366869225447501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22397083159155825633930001 16797812369366869225447501)
          ·
            refine ⟨6299179638512575959542813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16797812369366869225447501 6299179638512575959542813)
            ·
              refine ⟨2362192364442215984828555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6299179638512575959542813 2362192364442215984828555)
              ·
                refine ⟨3543288546663323977242833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362192364442215984828555 3543288546663323977242833)
                ·
                  refine ⟨2657466409997492982932125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543288546663323977242833 2657466409997492982932125)
                  ·
                    refine ⟨996549903749059868599547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657466409997492982932125 996549903749059868599547)
                    ·
                      rfl

theorem cell22_2911161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 1, 2, 3].length) (baseStart_2911161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911161 prefixEnd_2911161 := by exact prefixLift 2911161
  have htrace : WordTrace (prefixWord ++ tailWord_2911161) baseStart_2911161 baseEnd_2911161 := by
    simpa [prefixWord, tailWord_2911161, baseEnd_2911161] using wordTrace_append hprefix tailTrace_2911161
  have hstable : (prefixWord ++ tailWord_2911161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911161).length < 2 ^ (prefixWord ++ tailWord_2911161).sum := by decide
  have hdescent : baseEnd_2911161 < baseStart_2911161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911185 : List Nat := [1, 2, 2, 1, 2, 1, 3, 1, 9]
def baseStart_2911185 : Nat := 118140960795 + 2911185 * 2 ^ 59
def prefixEnd_2911185 : Nat := 4983230072969 + 3 ^ 40 * 2911185 * 2
def baseEnd_2911185 : Nat := 332186039813177268666491

theorem tailTrace_2911185 : CollatzResearch.WordTrace tailWord_2911185 prefixEnd_2911185 332186039813177268666491 := by
  unfold tailWord_2911185
  simp only [CollatzResearch.WordTrace]
  refine ⟨106179639958281410659727009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70786426638854273773151339 106179639958281410659727009)
  ·
    refine ⟨79634729968711057994795257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106179639958281410659727009 79634729968711057994795257)
    ·
      refine ⟨59726047476533293496096443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79634729968711057994795257 59726047476533293496096443)
      ·
        refine ⟨89589071214799940244144665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59726047476533293496096443 89589071214799940244144665)
        ·
          refine ⟨67191803411099955183108499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89589071214799940244144665 67191803411099955183108499)
          ·
            refine ⟨100787705116649932774662749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67191803411099955183108499 100787705116649932774662749)
            ·
              refine ⟨37795389418743724790498531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100787705116649932774662749 37795389418743724790498531)
              ·
                refine ⟨56693084128115587185747797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37795389418743724790498531 56693084128115587185747797)
                ·
                  refine ⟨332186039813177268666491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56693084128115587185747797 332186039813177268666491)
                  ·
                    rfl

theorem cell22_2911185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 9].length) (baseStart_2911185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911185 prefixEnd_2911185 := by exact prefixLift 2911185
  have htrace : WordTrace (prefixWord ++ tailWord_2911185) baseStart_2911185 baseEnd_2911185 := by
    simpa [prefixWord, tailWord_2911185, baseEnd_2911185] using wordTrace_append hprefix tailTrace_2911185
  have hstable : (prefixWord ++ tailWord_2911185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911185).length < 2 ^ (prefixWord ++ tailWord_2911185).sum := by decide
  have hdescent : baseEnd_2911185 < baseStart_2911185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911309 : List Nat := [1, 6, 1, 1, 1, 3, 9]
def baseStart_2911309 : Nat := 118140960795 + 2911309 * 2 ^ 59
def prefixEnd_2911309 : Nat := 4983230072969 + 3 ^ 40 * 2911309 * 2
def baseEnd_2911309 : Nat := 36911132117542104292559

theorem tailTrace_2911309 : CollatzResearch.WordTrace tailWord_2911309 prefixEnd_2911309 36911132117542104292559 := by
  unfold tailWord_2911309
  simp only [CollatzResearch.WordTrace]
  refine ⟨106184162609832179837240981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70789441739888119891493987 106184162609832179837240981)
  ·
    refine ⟨4977382622335883429870671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106184162609832179837240981 4977382622335883429870671)
    ·
      refine ⟨7466073933503825144806007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4977382622335883429870671 7466073933503825144806007)
      ·
        refine ⟨11199110900255737717209011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7466073933503825144806007 11199110900255737717209011)
        ·
          refine ⟨16798666350383606575813517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199110900255737717209011 16798666350383606575813517)
          ·
            refine ⟨6299499881393852465930069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16798666350383606575813517 6299499881393852465930069)
            ·
              refine ⟨36911132117542104292559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6299499881393852465930069 36911132117542104292559)
              ·
                rfl

theorem cell22_2911309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 9].length) (baseStart_2911309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911309 prefixEnd_2911309 := by exact prefixLift 2911309
  have htrace : WordTrace (prefixWord ++ tailWord_2911309) baseStart_2911309 baseEnd_2911309 := by
    simpa [prefixWord, tailWord_2911309, baseEnd_2911309] using wordTrace_append hprefix tailTrace_2911309
  have hstable : (prefixWord ++ tailWord_2911309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911309).length < 2 ^ (prefixWord ++ tailWord_2911309).sum := by decide
  have hdescent : baseEnd_2911309 < baseStart_2911309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911322 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 2, 6]
def baseStart_2911322 : Nat := 118140960795 + 2911322 * 2 ^ 59
def prefixEnd_2911322 : Nat := 4983230072969 + 3 ^ 40 * 2911322 * 2
def baseEnd_2911322 : Nat := 996605017339309115324053

theorem tailTrace_2911322 : CollatzResearch.WordTrace tailWord_2911322 prefixEnd_2911322 996605017339309115324053 := by
  unfold tailWord_2911322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26546159189696270764366055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70789757839190055371642813 26546159189696270764366055)
  ·
    refine ⟨39819238784544406146549083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26546159189696270764366055 39819238784544406146549083)
    ·
      refine ⟨59728858176816609219823625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39819238784544406146549083 59728858176816609219823625)
      ·
        refine ⟨44796643632612456914867719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59728858176816609219823625 44796643632612456914867719)
        ·
          refine ⟨67194965448918685372301579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44796643632612456914867719 67194965448918685372301579)
          ·
            refine ⟨100792448173378028058452369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67194965448918685372301579 100792448173378028058452369)
            ·
              refine ⟨75594336130033521043839277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100792448173378028058452369 75594336130033521043839277)
              ·
                refine ⟨28347876048762570391439729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75594336130033521043839277 28347876048762570391439729)
                ·
                  refine ⟨21260907036571927793579797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28347876048762570391439729 21260907036571927793579797)
                  ·
                    refine ⟨996605017339309115324053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21260907036571927793579797 996605017339309115324053)
                    ·
                      rfl

theorem cell22_2911322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 2, 6].length) (baseStart_2911322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911322 prefixEnd_2911322 := by exact prefixLift 2911322
  have htrace : WordTrace (prefixWord ++ tailWord_2911322) baseStart_2911322 baseEnd_2911322 := by
    simpa [prefixWord, tailWord_2911322, baseEnd_2911322] using wordTrace_append hprefix tailTrace_2911322
  have hstable : (prefixWord ++ tailWord_2911322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911322).length < 2 ^ (prefixWord ++ tailWord_2911322).sum := by decide
  have hdescent : baseEnd_2911322 < baseStart_2911322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911330 : List Nat := [3, 3, 2, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2911330 : Nat := 118140960795 + 2911330 * 2 ^ 59
def prefixEnd_2911330 : Nat := 4983230072969 + 3 ^ 40 * 2911330 * 2
def baseEnd_2911330 : Nat := 996607755902799761124029

theorem tailTrace_2911330 : CollatzResearch.WordTrace tailWord_2911330 prefixEnd_2911330 996607755902799761124029 := by
  unfold tailWord_2911330
  simp only [CollatzResearch.WordTrace]
  refine ⟨26546232135689025105938861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70789952361837400282503629 26546232135689025105938861)
  ·
    refine ⟨9954837050883384414727073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26546232135689025105938861 9954837050883384414727073)
    ·
      refine ⟨7466127788162538311045305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9954837050883384414727073 7466127788162538311045305)
      ·
        refine ⟨5599595841121903733283979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7466127788162538311045305 5599595841121903733283979)
        ·
          refine ⟨8399393761682855599925969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599595841121903733283979 8399393761682855599925969)
          ·
            refine ⟨6299545321262141699944477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8399393761682855599925969 6299545321262141699944477)
            ·
              refine ⟨2362329495473303137479179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6299545321262141699944477 2362329495473303137479179)
              ·
                refine ⟨3543494243209954706218769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362329495473303137479179 3543494243209954706218769)
                ·
                  refine ⟨2657620682407466029664077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543494243209954706218769 2657620682407466029664077)
                  ·
                    refine ⟨996607755902799761124029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657620682407466029664077 996607755902799761124029)
                    ·
                      rfl

theorem cell22_2911330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2911330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911330 prefixEnd_2911330 := by exact prefixLift 2911330
  have htrace : WordTrace (prefixWord ++ tailWord_2911330) baseStart_2911330 baseEnd_2911330 := by
    simpa [prefixWord, tailWord_2911330, baseEnd_2911330] using wordTrace_append hprefix tailTrace_2911330
  have hstable : (prefixWord ++ tailWord_2911330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911330).length < 2 ^ (prefixWord ++ tailWord_2911330).sum := by decide
  have hdescent : baseEnd_2911330 < baseStart_2911330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911341 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_2911341 : Nat := 118140960795 + 2911341 * 2 ^ 59
def prefixEnd_2911341 : Nat := 4983230072969 + 3 ^ 40 * 2911341 * 2
def baseEnd_2911341 : Nat := 996611521427599399098995

theorem tailTrace_2911341 : CollatzResearch.WordTrace tailWord_2911341 prefixEnd_2911341 996611521427599399098995 := by
  unfold tailWord_2911341
  simp only [CollatzResearch.WordTrace]
  refine ⟨106185329745716249302405877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70790219830477499534937251 106185329745716249302405877)
  ·
    refine ⟨9954874663660898372100551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106185329745716249302405877 9954874663660898372100551)
    ·
      refine ⟨14932311995491347558150827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9954874663660898372100551 14932311995491347558150827)
      ·
        refine ⟨22398467993237021337226241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14932311995491347558150827 22398467993237021337226241)
        ·
          refine ⟨16798850994927766002919681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22398467993237021337226241 16798850994927766002919681)
          ·
            refine ⟨12599138246195824502189761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16798850994927766002919681 12599138246195824502189761)
            ·
              refine ⟨9449353684646868376642321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12599138246195824502189761 9449353684646868376642321)
              ·
                refine ⟨7087015263485151282481741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9449353684646868376642321 7087015263485151282481741)
                ·
                  refine ⟨2657630723806931730930653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7087015263485151282481741 2657630723806931730930653)
                  ·
                    refine ⟨996611521427599399098995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657630723806931730930653 996611521427599399098995)
                    ·
                      rfl

theorem cell22_2911341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_2911341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911341 prefixEnd_2911341 := by exact prefixLift 2911341
  have htrace : WordTrace (prefixWord ++ tailWord_2911341) baseStart_2911341 baseEnd_2911341 := by
    simpa [prefixWord, tailWord_2911341, baseEnd_2911341] using wordTrace_append hprefix tailTrace_2911341
  have hstable : (prefixWord ++ tailWord_2911341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911341).length < 2 ^ (prefixWord ++ tailWord_2911341).sum := by decide
  have hdescent : baseEnd_2911341 < baseStart_2911341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911352 : List Nat := [2, 1, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_2911352 : Nat := 118140960795 + 2911352 * 2 ^ 59
def prefixEnd_2911352 : Nat := 4983230072969 + 3 ^ 40 * 2911352 * 2
def baseEnd_2911352 : Nat := 996615286952399037073961

theorem tailTrace_2911352 : CollatzResearch.WordTrace tailWord_2911352 prefixEnd_2911352 996615286952399037073961 := by
  unfold tailWord_2911352
  simp only [CollatzResearch.WordTrace]
  refine ⟨53092865474338199090528155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70790487299117598787370873 53092865474338199090528155)
  ·
    refine ⟨79639298211507298635792233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53092865474338199090528155 79639298211507298635792233)
    ·
      refine ⟨59729473658630473976844175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79639298211507298635792233 59729473658630473976844175)
      ·
        refine ⟨89594210487945710965266263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59729473658630473976844175 89594210487945710965266263)
        ·
          refine ⟨134391315731918566447899395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89594210487945710965266263 134391315731918566447899395)
          ·
            refine ⟨201586973597877849671849093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134391315731918566447899395 201586973597877849671849093)
            ·
              refine ⟨37797557549602096813471705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201586973597877849671849093 37797557549602096813471705)
              ·
                refine ⟨28348168162201572610103779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37797557549602096813471705 28348168162201572610103779)
                ·
                  refine ⟨42522252243302358915155669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28348168162201572610103779 42522252243302358915155669)
                  ·
                    refine ⟨996615286952399037073961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42522252243302358915155669 996615286952399037073961)
                    ·
                      rfl

theorem cell22_2911352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_2911352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911352 prefixEnd_2911352 := by exact prefixLift 2911352
  have htrace : WordTrace (prefixWord ++ tailWord_2911352) baseStart_2911352 baseEnd_2911352 := by
    simpa [prefixWord, tailWord_2911352, baseEnd_2911352] using wordTrace_append hprefix tailTrace_2911352
  have hstable : (prefixWord ++ tailWord_2911352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911352).length < 2 ^ (prefixWord ++ tailWord_2911352).sum := by decide
  have hdescent : baseEnd_2911352 < baseStart_2911352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911388 : List Nat := [2, 2, 3, 2, 1, 4, 2, 1, 5]
def baseStart_2911388 : Nat := 118140960795 + 2911388 * 2 ^ 59
def prefixEnd_2911388 : Nat := 4983230072969 + 3 ^ 40 * 2911388 * 2
def baseEnd_2911388 : Nat := 332209203496035647724617

theorem tailTrace_2911388 : CollatzResearch.WordTrace tailWord_2911388 prefixEnd_2911388 332209203496035647724617 := by
  unfold tailWord_2911388
  simp only [CollatzResearch.WordTrace]
  refine ⟨53093521988272988164683409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70791362651030650886244545 53093521988272988164683409)
  ·
    refine ⟨39820141491204741123512557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53093521988272988164683409 39820141491204741123512557)
    ·
      refine ⟨14932553059201777921317209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39820141491204741123512557 14932553059201777921317209)
      ·
        refine ⟨11199414794401333440987907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14932553059201777921317209 11199414794401333440987907)
        ·
          refine ⟨16799122191602000161481861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199414794401333440987907 16799122191602000161481861)
          ·
            refine ⟨3149835410925375030277849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16799122191602000161481861 3149835410925375030277849)
            ·
              refine ⟨2362376558194031272708387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149835410925375030277849 2362376558194031272708387)
              ·
                refine ⟨3543564837291046909062581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362376558194031272708387 3543564837291046909062581)
                ·
                  refine ⟨332209203496035647724617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543564837291046909062581 332209203496035647724617)
                  ·
                    rfl

theorem cell22_2911388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_2911388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911388 prefixEnd_2911388 := by exact prefixLift 2911388
  have htrace : WordTrace (prefixWord ++ tailWord_2911388) baseStart_2911388 baseEnd_2911388 := by
    simpa [prefixWord, tailWord_2911388, baseEnd_2911388] using wordTrace_append hprefix tailTrace_2911388
  have hstable : (prefixWord ++ tailWord_2911388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911388).length < 2 ^ (prefixWord ++ tailWord_2911388).sum := by decide
  have hdescent : baseEnd_2911388 < baseStart_2911388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911426 : List Nat := [3, 5, 1, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2911426 : Nat := 118140960795 + 2911426 * 2 ^ 59
def prefixEnd_2911426 : Nat := 4983230072969 + 3 ^ 40 * 2911426 * 2
def baseEnd_2911426 : Nat := 996640618664687510723735

theorem tailTrace_2911426 : CollatzResearch.WordTrace tailWord_2911426 prefixEnd_2911426 996640618664687510723735 := by
  unfold tailWord_2911426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547107487602077204812533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70792286633605539212833421 26547107487602077204812533)
  ·
    refine ⟨2488791326962694737951175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26547107487602077204812533 2488791326962694737951175)
    ·
      refine ⟨3733186990444042106926763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488791326962694737951175 3733186990444042106926763)
      ·
        refine ⟨5599780485666063160390145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733186990444042106926763 5599780485666063160390145)
        ·
          refine ⟨4199835364249547370292609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5599780485666063160390145 4199835364249547370292609)
          ·
            refine ⟨3149876523187160527719457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4199835364249547370292609 3149876523187160527719457)
            ·
              refine ⟨2362407392390370395789593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149876523187160527719457 2362407392390370395789593)
              ·
                refine ⟨1771805544292777796842195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362407392390370395789593 1771805544292777796842195)
                ·
                  refine ⟨2657708316439166695263293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771805544292777796842195 2657708316439166695263293)
                  ·
                    refine ⟨996640618664687510723735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657708316439166695263293 996640618664687510723735)
                    ·
                      rfl

theorem cell22_2911426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2911426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911426 prefixEnd_2911426 := by exact prefixLift 2911426
  have htrace : WordTrace (prefixWord ++ tailWord_2911426) baseStart_2911426 baseEnd_2911426 := by
    simpa [prefixWord, tailWord_2911426, baseEnd_2911426] using wordTrace_append hprefix tailTrace_2911426
  have hstable : (prefixWord ++ tailWord_2911426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911426).length < 2 ^ (prefixWord ++ tailWord_2911426).sum := by decide
  have hdescent : baseEnd_2911426 < baseStart_2911426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911493 : List Nat := [1, 3, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_2911493 : Nat := 118140960795 + 2911493 * 2 ^ 59
def prefixEnd_2911493 : Nat := 4983230072969 + 3 ^ 40 * 2911493 * 2
def baseEnd_2911493 : Nat := 996663554133921669298529

theorem tailTrace_2911493 : CollatzResearch.WordTrace tailWord_2911493 prefixEnd_2911493 996663554133921669298529 := by
  unfold tailWord_2911493
  simp only [CollatzResearch.WordTrace]
  refine ⟨106190873641165579261939133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70793915760777052841292755 106190873641165579261939133)
  ·
    refine ⟨39821577615437092223227175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106190873641165579261939133 39821577615437092223227175)
    ·
      refine ⟨59732366423155638334840763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39821577615437092223227175 59732366423155638334840763)
      ·
        refine ⟨89598549634733457502261145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59732366423155638334840763 89598549634733457502261145)
        ·
          refine ⟨67198912226050093126695859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89598549634733457502261145 67198912226050093126695859)
          ·
            refine ⟨100798368339075139690043789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67198912226050093126695859 100798368339075139690043789)
            ·
              refine ⟨37799388127153177383766421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100798368339075139690043789 37799388127153177383766421)
              ·
                refine ⟨1771846318460305189864051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37799388127153177383766421 1771846318460305189864051)
                ·
                  refine ⟨2657769477690457784796077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771846318460305189864051 2657769477690457784796077)
                  ·
                    refine ⟨996663554133921669298529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657769477690457784796077 996663554133921669298529)
                    ·
                      rfl

theorem cell22_2911493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_2911493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911493 prefixEnd_2911493 := by exact prefixLift 2911493
  have htrace : WordTrace (prefixWord ++ tailWord_2911493) baseStart_2911493 baseEnd_2911493 := by
    simpa [prefixWord, tailWord_2911493, baseEnd_2911493] using wordTrace_append hprefix tailTrace_2911493
  have hstable : (prefixWord ++ tailWord_2911493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911493).length < 2 ^ (prefixWord ++ tailWord_2911493).sum := by decide
  have hdescent : baseEnd_2911493 < baseStart_2911493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911536 : List Nat := [2, 1, 1, 1, 2, 2, 3, 5, 1, 4]
def baseStart_2911536 : Nat := 118140960795 + 2911536 * 2 ^ 59
def prefixEnd_2911536 : Nat := 4983230072969 + 3 ^ 40 * 2911536 * 2
def baseEnd_2911536 : Nat := 996678273912683890473397

theorem tailTrace_2911536 : CollatzResearch.WordTrace tailWord_2911536 prefixEnd_2911536 996678273912683890473397 := by
  unfold tailWord_2911536
  simp only [CollatzResearch.WordTrace]
  refine ⟨53096220990004898802877231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70794961320006531737169641 53096220990004898802877231)
  ·
    refine ⟨79644331485007348204315847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53096220990004898802877231 79644331485007348204315847)
    ·
      refine ⟨119466497227511022306473771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79644331485007348204315847 119466497227511022306473771)
      ·
        refine ⟨179199745841266533459710657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119466497227511022306473771 179199745841266533459710657)
        ·
          refine ⟨134399809380949900094782993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179199745841266533459710657 134399809380949900094782993)
          ·
            refine ⟨100799857035712425071087245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134399809380949900094782993 100799857035712425071087245)
            ·
              refine ⟨37799946388392159401657717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100799857035712425071087245 37799946388392159401657717)
              ·
                refine ⟨3543744973911764943905411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37799946388392159401657717 3543744973911764943905411)
                ·
                  refine ⟨5315617460867647415858117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543744973911764943905411 5315617460867647415858117)
                  ·
                    refine ⟨996678273912683890473397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5315617460867647415858117 996678273912683890473397)
                    ·
                      rfl

theorem cell22_2911536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 5, 1, 4].length) (baseStart_2911536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911536 prefixEnd_2911536 := by exact prefixLift 2911536
  have htrace : WordTrace (prefixWord ++ tailWord_2911536) baseStart_2911536 baseEnd_2911536 := by
    simpa [prefixWord, tailWord_2911536, baseEnd_2911536] using wordTrace_append hprefix tailTrace_2911536
  have hstable : (prefixWord ++ tailWord_2911536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911536).length < 2 ^ (prefixWord ++ tailWord_2911536).sum := by decide
  have hdescent : baseEnd_2911536 < baseStart_2911536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911551 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 6]
def baseStart_2911551 : Nat := 118140960795 + 2911551 * 2 ^ 59
def prefixEnd_2911551 : Nat := 4983230072969 + 3 ^ 40 * 2911551 * 2
def baseEnd_2911551 : Nat := 332227802906409617116117

theorem tailTrace_2911551 : CollatzResearch.WordTrace tailWord_2911551 prefixEnd_2911551 332227802906409617116117 := by
  unfold tailWord_2911551
  simp only [CollatzResearch.WordTrace]
  refine ⟨106192989074955455167550507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70795326049970303445033671 106192989074955455167550507)
  ·
    refine ⟨159289483612433182751325761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106192989074955455167550507 159289483612433182751325761)
    ·
      refine ⟨119467112709324887063494321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159289483612433182751325761 119467112709324887063494321)
      ·
        refine ⟨89600334531993665297620741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119467112709324887063494321 89600334531993665297620741)
        ·
          refine ⟨16800062724748812243303889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89600334531993665297620741 16800062724748812243303889)
          ·
            refine ⟨12600047043561609182477917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16800062724748812243303889 12600047043561609182477917)
            ·
              refine ⟨4725017641335603443429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12600047043561609182477917 4725017641335603443429219)
              ·
                refine ⟨7087526462003405165143829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725017641335603443429219 7087526462003405165143829)
                ·
                  refine ⟨332227802906409617116117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7087526462003405165143829 332227802906409617116117)
                  ·
                    rfl

theorem cell22_2911551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 6].length) (baseStart_2911551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911551 prefixEnd_2911551 := by exact prefixLift 2911551
  have htrace : WordTrace (prefixWord ++ tailWord_2911551) baseStart_2911551 baseEnd_2911551 := by
    simpa [prefixWord, tailWord_2911551, baseEnd_2911551] using wordTrace_append hprefix tailTrace_2911551
  have hstable : (prefixWord ++ tailWord_2911551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911551).length < 2 ^ (prefixWord ++ tailWord_2911551).sum := by decide
  have hdescent : baseEnd_2911551 < baseStart_2911551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911566 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 1, 5]
def baseStart_2911566 : Nat := 118140960795 + 2911566 * 2 ^ 59
def prefixEnd_2911566 : Nat := 4983230072969 + 3 ^ 40 * 2911566 * 2
def baseEnd_2911566 : Nat := 996688543525773812223305

theorem tailTrace_2911566 : CollatzResearch.WordTrace tailWord_2911566 prefixEnd_2911566 996688543525773812223305 := by
  unfold tailWord_2911566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274192021237639091168319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70795690779934075152897701 13274192021237639091168319)
  ·
    refine ⟨19911288031856458636752479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13274192021237639091168319 19911288031856458636752479)
    ·
      refine ⟨29866932047784687955128719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19911288031856458636752479 29866932047784687955128719)
      ·
        refine ⟨44800398071677031932693079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29866932047784687955128719 44800398071677031932693079)
        ·
          refine ⟨67200597107515547899039619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44800398071677031932693079 67200597107515547899039619)
          ·
            refine ⟨100800895661273321848559429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67200597107515547899039619 100800895661273321848559429)
            ·
              refine ⟨18900167936488747846604893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100800895661273321848559429 18900167936488747846604893)
              ·
                refine ⟨7087562976183280442476835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18900167936488747846604893 7087562976183280442476835)
                ·
                  refine ⟨10631344464274920663715253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7087562976183280442476835 10631344464274920663715253)
                  ·
                    refine ⟨996688543525773812223305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10631344464274920663715253 996688543525773812223305)
                    ·
                      rfl

theorem cell22_2911566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_2911566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911566 prefixEnd_2911566 := by exact prefixLift 2911566
  have htrace : WordTrace (prefixWord ++ tailWord_2911566) baseStart_2911566 baseEnd_2911566 := by
    simpa [prefixWord, tailWord_2911566, baseEnd_2911566] using wordTrace_append hprefix tailTrace_2911566
  have hstable : (prefixWord ++ tailWord_2911566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911566).length < 2 ^ (prefixWord ++ tailWord_2911566).sum := by decide
  have hdescent : baseEnd_2911566 < baseStart_2911566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911628 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_2911628 : Nat := 118140960795 + 2911628 * 2 ^ 59
def prefixEnd_2911628 : Nat := 4983230072969 + 3 ^ 40 * 2911628 * 2
def baseEnd_2911628 : Nat := 996709767392826317173115

theorem tailTrace_2911628 : CollatzResearch.WordTrace tailWord_2911628 prefixEnd_2911628 996709767392826317173115 := by
  unfold tailWord_2911628
  simp only [CollatzResearch.WordTrace]
  refine ⟨53097898747838248659051769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70797198330450998212069025 53097898747838248659051769)
  ·
    refine ⟨39823424060878686494288827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53097898747838248659051769 39823424060878686494288827)
    ·
      refine ⟨59735136091318029741433241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39823424060878686494288827 59735136091318029741433241)
      ·
        refine ⟨44801352068488522306074931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59735136091318029741433241 44801352068488522306074931)
        ·
          refine ⟨67202028102732783459112397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44801352068488522306074931 67202028102732783459112397)
          ·
            refine ⟨25200760538524793797167149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67202028102732783459112397 25200760538524793797167149)
            ·
              refine ⟨9450285201946797673937681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25200760538524793797167149 9450285201946797673937681)
              ·
                refine ⟨7087713901460098255453261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9450285201946797673937681 7087713901460098255453261)
                ·
                  refine ⟨2657892713047536845794973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7087713901460098255453261 2657892713047536845794973)
                  ·
                    refine ⟨996709767392826317173115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657892713047536845794973 996709767392826317173115)
                    ·
                      rfl

theorem cell22_2911628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_2911628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911628 prefixEnd_2911628 := by exact prefixLift 2911628
  have htrace : WordTrace (prefixWord ++ tailWord_2911628) baseStart_2911628 baseEnd_2911628 := by
    simpa [prefixWord, tailWord_2911628, baseEnd_2911628] using wordTrace_append hprefix tailTrace_2911628
  have hstable : (prefixWord ++ tailWord_2911628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911628).length < 2 ^ (prefixWord ++ tailWord_2911628).sum := by decide
  have hdescent : baseEnd_2911628 < baseStart_2911628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911630 : List Nat := [4, 1, 1, 4, 2, 1, 3, 6]
def baseStart_2911630 : Nat := 118140960795 + 2911630 * 2 ^ 59
def prefixEnd_2911630 : Nat := 4983230072969 + 3 ^ 40 * 2911630 * 2
def baseEnd_2911630 : Nat := 110745605781522108735901

theorem tailTrace_2911630 : CollatzResearch.WordTrace tailWord_2911630 prefixEnd_2911630 110745605781522108735901 := by
  unfold tailWord_2911630
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274483805208656457459543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70797246961112834439784229 13274483805208656457459543)
  ·
    refine ⟨19911725707812984686189315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13274483805208656457459543 19911725707812984686189315)
    ·
      refine ⟨29867588561719477029283973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19911725707812984686189315 29867588561719477029283973)
      ·
        refine ⟨5600172855322401942990745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29867588561719477029283973 5600172855322401942990745)
        ·
          refine ⟨4200129641491801457243059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600172855322401942990745 4200129641491801457243059)
          ·
            refine ⟨6300194462237702185864589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200129641491801457243059 6300194462237702185864589)
            ·
              refine ⟨2362572923339138319699221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6300194462237702185864589 2362572923339138319699221)
              ·
                refine ⟨110745605781522108735901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2362572923339138319699221 110745605781522108735901)
                ·
                  rfl

theorem cell22_2911630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_2911630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911630 prefixEnd_2911630 := by exact prefixLift 2911630
  have htrace : WordTrace (prefixWord ++ tailWord_2911630) baseStart_2911630 baseEnd_2911630 := by
    simpa [prefixWord, tailWord_2911630, baseEnd_2911630] using wordTrace_append hprefix tailTrace_2911630
  have hstable : (prefixWord ++ tailWord_2911630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911630).length < 2 ^ (prefixWord ++ tailWord_2911630).sum := by decide
  have hdescent : baseEnd_2911630 < baseStart_2911630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911778 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2911778 : Nat := 118140960795 + 2911778 * 2 ^ 59
def prefixEnd_2911778 : Nat := 4983230072969 + 3 ^ 40 * 2911778 * 2
def baseEnd_2911778 : Nat := 996761115458275925922655

theorem tailTrace_2911778 : CollatzResearch.WordTrace tailWord_2911778 prefixEnd_2911778 996761115458275925922655 := by
  unfold tailWord_2911778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26550317111283268234015997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70800845630088715290709325 26550317111283268234015997)
  ·
    refine ⟨9956368916731225587755999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26550317111283268234015997 9956368916731225587755999)
    ·
      refine ⟨14934553375096838381633999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9956368916731225587755999 14934553375096838381633999)
      ·
        refine ⟨22401830062645257572450999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14934553375096838381633999 22401830062645257572450999)
        ·
          refine ⟨33602745093967886358676499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22401830062645257572450999 33602745093967886358676499)
          ·
            refine ⟨50404117640951829538014749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33602745093967886358676499 50404117640951829538014749)
            ·
              refine ⟨18901544115356936076755531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50404117640951829538014749 18901544115356936076755531)
              ·
                refine ⟨28352316173035404115133297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18901544115356936076755531 28352316173035404115133297)
                ·
                  refine ⟨21264237129776553086349973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28352316173035404115133297 21264237129776553086349973)
                  ·
                    refine ⟨996761115458275925922655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21264237129776553086349973 996761115458275925922655)
                    ·
                      rfl

theorem cell22_2911778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2911778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911778 prefixEnd_2911778 := by exact prefixLift 2911778
  have htrace : WordTrace (prefixWord ++ tailWord_2911778) baseStart_2911778 baseEnd_2911778 := by
    simpa [prefixWord, tailWord_2911778, baseEnd_2911778] using wordTrace_append hprefix tailTrace_2911778
  have hstable : (prefixWord ++ tailWord_2911778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911778).length < 2 ^ (prefixWord ++ tailWord_2911778).sum := by decide
  have hdescent : baseEnd_2911778 < baseStart_2911778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911904 : List Nat := [2, 1, 1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_2911904 : Nat := 118140960795 + 2911904 * 2 ^ 59
def prefixEnd_2911904 : Nat := 4983230072969 + 3 ^ 40 * 2911904 * 2
def baseEnd_2911904 : Nat := 996804247833253597272269

theorem tailTrace_2911904 : CollatzResearch.WordTrace tailWord_2911904 prefixEnd_2911904 996804247833253597272269 := by
  unfold tailWord_2911904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53102932021338298227575383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70803909361784397636767177 53102932021338298227575383)
  ·
    refine ⟨79654398032007447341363075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53102932021338298227575383 79654398032007447341363075)
    ·
      refine ⟨119481597048011171012044613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79654398032007447341363075 119481597048011171012044613)
      ·
        refine ⟨22402799446502094564758365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119481597048011171012044613 22402799446502094564758365)
        ·
          refine ⟨8401049792438285461784387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22402799446502094564758365 8401049792438285461784387)
          ·
            refine ⟨12601574688657428192676581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401049792438285461784387 12601574688657428192676581)
            ·
              refine ⟨2362795254123267786126859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12601574688657428192676581 2362795254123267786126859)
              ·
                refine ⟨3544192881184901679190289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362795254123267786126859 3544192881184901679190289)
                ·
                  refine ⟨2658144660888676259392717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544192881184901679190289 2658144660888676259392717)
                  ·
                    refine ⟨996804247833253597272269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658144660888676259392717 996804247833253597272269)
                    ·
                      rfl

theorem cell22_2911904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_2911904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911904 prefixEnd_2911904 := by exact prefixLift 2911904
  have htrace : WordTrace (prefixWord ++ tailWord_2911904) baseStart_2911904 baseEnd_2911904 := by
    simpa [prefixWord, tailWord_2911904, baseEnd_2911904] using wordTrace_append hprefix tailTrace_2911904
  have hstable : (prefixWord ++ tailWord_2911904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911904).length < 2 ^ (prefixWord ++ tailWord_2911904).sum := by decide
  have hdescent : baseEnd_2911904 < baseStart_2911904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911928 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 9]
def baseStart_2911928 : Nat := 118140960795 + 2911928 * 2 ^ 59
def prefixEnd_2911928 : Nat := 4983230072969 + 3 ^ 40 * 2911928 * 2
def baseEnd_2911928 : Nat := 332270821174575178224065

theorem tailTrace_2911928 : CollatzResearch.WordTrace tailWord_2911928 prefixEnd_2911928 332270821174575178224065 := by
  unfold tailWord_2911928
  simp only [CollatzResearch.WordTrace]
  refine ⟨53103369697294824277012219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70804492929726432369349625 53103369697294824277012219)
  ·
    refine ⟨79655054545942236415518329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53103369697294824277012219 79655054545942236415518329)
    ·
      refine ⟨59741290909456677311638747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79655054545942236415518329 59741290909456677311638747)
      ·
        refine ⟨89611936364185015967458121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59741290909456677311638747 89611936364185015967458121)
        ·
          refine ⟨67208952273138761975593591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89611936364185015967458121 67208952273138761975593591)
          ·
            refine ⟨100813428409708142963390387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67208952273138761975593591 100813428409708142963390387)
            ·
              refine ⟨151220142614562214445085581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100813428409708142963390387 151220142614562214445085581)
              ·
                refine ⟨56707553480460830416907093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151220142614562214445085581 56707553480460830416907093)
                ·
                  refine ⟨332270821174575178224065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56707553480460830416907093 332270821174575178224065)
                  ·
                    rfl

theorem cell22_2911928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_2911928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911928 prefixEnd_2911928 := by exact prefixLift 2911928
  have htrace : WordTrace (prefixWord ++ tailWord_2911928) baseStart_2911928 baseEnd_2911928 := by
    simpa [prefixWord, tailWord_2911928, baseEnd_2911928] using wordTrace_append hprefix tailTrace_2911928
  have hstable : (prefixWord ++ tailWord_2911928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911928).length < 2 ^ (prefixWord ++ tailWord_2911928).sum := by decide
  have hdescent : baseEnd_2911928 < baseStart_2911928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2911960 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 2, 5]
def baseStart_2911960 : Nat := 118140960795 + 2911960 * 2 ^ 59
def prefixEnd_2911960 : Nat := 4983230072969 + 3 ^ 40 * 2911960 * 2
def baseEnd_2911960 : Nat := 996823417777688117872097

theorem tailTrace_2911960 : CollatzResearch.WordTrace tailWord_2911960 prefixEnd_2911960 996823417777688117872097 := by
  unfold tailWord_2911960
  simp only [CollatzResearch.WordTrace]
  refine ⟨53103953265236859009594667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70805271020315812012792889 53103953265236859009594667)
  ·
    refine ⟨79655929897855288514392001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53103953265236859009594667 79655929897855288514392001)
    ·
      refine ⟨59741947423391466385794001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79655929897855288514392001 59741947423391466385794001)
      ·
        refine ⟨44806460567543599789345501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59741947423391466385794001 44806460567543599789345501)
        ·
          refine ⟨16802422712828849921004563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44806460567543599789345501 16802422712828849921004563)
          ·
            refine ⟨25203634069243274881506845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16802422712828849921004563 25203634069243274881506845)
            ·
              refine ⟨9451362775966228080565067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25203634069243274881506845 9451362775966228080565067)
              ·
                refine ⟨14177044163949342120847601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9451362775966228080565067 14177044163949342120847601)
                ·
                  refine ⟨10632783122962006590635701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14177044163949342120847601 10632783122962006590635701)
                  ·
                    refine ⟨996823417777688117872097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10632783122962006590635701 996823417777688117872097)
                    ·
                      rfl

theorem cell22_2911960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 2, 5].length) (baseStart_2911960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2911960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2911960 prefixEnd_2911960 := by exact prefixLift 2911960
  have htrace : WordTrace (prefixWord ++ tailWord_2911960) baseStart_2911960 baseEnd_2911960 := by
    simpa [prefixWord, tailWord_2911960, baseEnd_2911960] using wordTrace_append hprefix tailTrace_2911960
  have hstable : (prefixWord ++ tailWord_2911960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2911960).length < 2 ^ (prefixWord ++ tailWord_2911960).sum := by decide
  have hdescent : baseEnd_2911960 < baseStart_2911960 := by decide
  rcases family_descends (prefixWord ++ tailWord_2911960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912052 : List Nat := [2, 5, 1, 1, 2, 1, 10]
def baseStart_2912052 : Nat := 118140960795 + 2912052 * 2 ^ 59
def prefixEnd_2912052 : Nat := 4983230072969 + 3 ^ 40 * 2912052 * 2
def baseEnd_2912052 : Nat := 36920552268808538687845

theorem tailTrace_2912052 : CollatzResearch.WordTrace tailWord_2912052 prefixEnd_2912052 36920552268808538687845 := by
  unfold tailWord_2912052
  simp only [CollatzResearch.WordTrace]
  refine ⟨53105631023070208865769205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70807508030760278487692273 53105631023070208865769205)
  ·
    refine ⟨4978652908412832081165863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53105631023070208865769205 4978652908412832081165863)
    ·
      refine ⟨7467979362619248121748795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4978652908412832081165863 7467979362619248121748795)
      ·
        refine ⟨11201969043928872182623193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7467979362619248121748795 11201969043928872182623193)
        ·
          refine ⟨8401476782946654136967395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11201969043928872182623193 8401476782946654136967395)
          ·
            refine ⟨12602215174419981205451093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401476782946654136967395 12602215174419981205451093)
            ·
              refine ⟨36920552268808538687845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12602215174419981205451093 36920552268808538687845)
              ·
                rfl

theorem cell22_2912052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 10].length) (baseStart_2912052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912052 prefixEnd_2912052 := by exact prefixLift 2912052
  have htrace : WordTrace (prefixWord ++ tailWord_2912052) baseStart_2912052 baseEnd_2912052 := by
    simpa [prefixWord, tailWord_2912052, baseEnd_2912052] using wordTrace_append hprefix tailTrace_2912052
  have hstable : (prefixWord ++ tailWord_2912052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912052).length < 2 ^ (prefixWord ++ tailWord_2912052).sum := by decide
  have hdescent : baseEnd_2912052 < baseStart_2912052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912054 : List Nat := [5, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2912054 : Nat := 118140960795 + 2912054 * 2 ^ 59
def prefixEnd_2912054 : Nat := 4983230072969 + 3 ^ 40 * 2912054 * 2
def baseEnd_2912054 : Nat := 996855595898703206021809

theorem tailTrace_2912054 : CollatzResearch.WordTrace tailWord_2912054 prefixEnd_2912054 996855595898703206021809 := by
  unfold tailWord_2912054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6638208437008323254569451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70807556661422114715407477 6638208437008323254569451)
  ·
    refine ⟨9957312655512484881854177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6638208437008323254569451 9957312655512484881854177)
    ·
      refine ⟨7467984491634363661390633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9957312655512484881854177 7467984491634363661390633)
      ·
        refine ⟨5600988368725772746042975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7467984491634363661390633 5600988368725772746042975)
        ·
          refine ⟨8401482553088659119064463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600988368725772746042975 8401482553088659119064463)
          ·
            refine ⟨12602223829632988678596695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8401482553088659119064463 12602223829632988678596695)
            ·
              refine ⟨18903335744449483017895043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12602223829632988678596695 18903335744449483017895043)
              ·
                refine ⟨28355003616674224526842565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18903335744449483017895043 28355003616674224526842565)
                ·
                  refine ⟨5316563178126417098782981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28355003616674224526842565 5316563178126417098782981)
                  ·
                    refine ⟨996855595898703206021809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5316563178126417098782981 996855595898703206021809)
                    ·
                      rfl

theorem cell22_2912054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2912054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912054 prefixEnd_2912054 := by exact prefixLift 2912054
  have htrace : WordTrace (prefixWord ++ tailWord_2912054) baseStart_2912054 baseEnd_2912054 := by
    simpa [prefixWord, tailWord_2912054, baseEnd_2912054] using wordTrace_append hprefix tailTrace_2912054
  have hstable : (prefixWord ++ tailWord_2912054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912054).length < 2 ^ (prefixWord ++ tailWord_2912054).sum := by decide
  have hdescent : baseEnd_2912054 < baseStart_2912054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912161 : List Nat := [1, 2, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2912161 : Nat := 118140960795 + 2912161 * 2 ^ 59
def prefixEnd_2912161 : Nat := 4983230072969 + 3 ^ 40 * 2912161 * 2
def baseEnd_2912161 : Nat := 996892224185390593596481

theorem tailTrace_2912161 : CollatzResearch.WordTrace tailWord_2912161 prefixEnd_2912161 996892224185390593596481 := by
  unfold tailWord_2912161
  simp only [CollatzResearch.WordTrace]
  refine ⟨106215237602745529347256337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70810158401830352898170891 106215237602745529347256337)
  ·
    refine ⟨79661428202059147010442253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106215237602745529347256337 79661428202059147010442253)
    ·
      refine ⟨29873035575772180128915845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79661428202059147010442253 29873035575772180128915845)
      ·
        refine ⟨5601194170457283774171721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29873035575772180128915845 5601194170457283774171721)
        ·
          refine ⟨4200895627842962830628791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5601194170457283774171721 4200895627842962830628791)
          ·
            refine ⟨6301343441764444245943187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200895627842962830628791 6301343441764444245943187)
            ·
              refine ⟨9452015162646666368914781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301343441764444245943187 9452015162646666368914781)
              ·
                refine ⟨3544505685992499888343043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9452015162646666368914781 3544505685992499888343043)
                ·
                  refine ⟨5316758528988749832514565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544505685992499888343043 5316758528988749832514565)
                  ·
                    refine ⟨996892224185390593596481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5316758528988749832514565 996892224185390593596481)
                    ·
                      rfl

theorem cell22_2912161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2912161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912161 prefixEnd_2912161 := by exact prefixLift 2912161
  have htrace : WordTrace (prefixWord ++ tailWord_2912161) baseStart_2912161 baseEnd_2912161 := by
    simpa [prefixWord, tailWord_2912161, baseEnd_2912161] using wordTrace_append hprefix tailTrace_2912161
  have hstable : (prefixWord ++ tailWord_2912161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912161).length < 2 ^ (prefixWord ++ tailWord_2912161).sum := by decide
  have hdescent : baseEnd_2912161 < baseStart_2912161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912191 : List Nat := [1, 1, 2, 2, 2, 1, 7, 1, 2, 3]
def baseStart_2912191 : Nat := 118140960795 + 2912191 * 2 ^ 59
def prefixEnd_2912191 : Nat := 4983230072969 + 3 ^ 40 * 2912191 * 2
def baseEnd_2912191 : Nat := 996902493798480515346389

theorem tailTrace_2912191 : CollatzResearch.WordTrace tailWord_2912191 prefixEnd_2912191 996902493798480515346389 := by
  unfold tailWord_2912191
  simp only [CollatzResearch.WordTrace]
  refine ⟨106216331792636844470848427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70810887861757896313898951 106216331792636844470848427)
  ·
    refine ⟨159324497688955266706272641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106216331792636844470848427 159324497688955266706272641)
    ·
      refine ⟨119493373266716450029704481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159324497688955266706272641 119493373266716450029704481)
      ·
        refine ⟨89620029950037337522278361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119493373266716450029704481 89620029950037337522278361)
        ·
          refine ⟨67215022462528003141708771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89620029950037337522278361 67215022462528003141708771)
          ·
            refine ⟨100822533693792004712563157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67215022462528003141708771 100822533693792004712563157)
            ·
              refine ⟨2363028133448250110450699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 100822533693792004712563157 2363028133448250110450699)
              ·
                refine ⟨3544542200172375165676049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363028133448250110450699 3544542200172375165676049)
                ·
                  refine ⟨2658406650129281374257037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544542200172375165676049 2658406650129281374257037)
                  ·
                    refine ⟨996902493798480515346389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658406650129281374257037 996902493798480515346389)
                    ·
                      rfl

theorem cell22_2912191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 1, 2, 3].length) (baseStart_2912191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912191 prefixEnd_2912191 := by exact prefixLift 2912191
  have htrace : WordTrace (prefixWord ++ tailWord_2912191) baseStart_2912191 baseEnd_2912191 := by
    simpa [prefixWord, tailWord_2912191, baseEnd_2912191] using wordTrace_append hprefix tailTrace_2912191
  have hstable : (prefixWord ++ tailWord_2912191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912191).length < 2 ^ (prefixWord ++ tailWord_2912191).sum := by decide
  have hdescent : baseEnd_2912191 < baseStart_2912191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912204 : List Nat := [2, 2, 1, 4, 1, 2, 4, 6]
def baseStart_2912204 : Nat := 118140960795 + 2912204 * 2 ^ 59
def prefixEnd_2912204 : Nat := 4983230072969 + 3 ^ 40 * 2912204 * 2
def baseEnd_2912204 : Nat := 110767438218239201641261

theorem tailTrace_2912204 : CollatzResearch.WordTrace tailWord_2912204 prefixEnd_2912204 110767438218239201641261 := by
  unfold tailWord_2912204
  simp only [CollatzResearch.WordTrace]
  refine ⟨53108402970794873845535833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70811203961059831794047777 53108402970794873845535833)
  ·
    refine ⟨39831302228096155384151875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53108402970794873845535833 39831302228096155384151875)
    ·
      refine ⟨59746953342144233076227813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39831302228096155384151875 59746953342144233076227813)
      ·
        refine ⟨11202553751652043701792715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59746953342144233076227813 11202553751652043701792715)
        ·
          refine ⟨16803830627478065552689073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11202553751652043701792715 16803830627478065552689073)
          ·
            refine ⟨12602872970608549164516805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16803830627478065552689073 12602872970608549164516805)
            ·
              refine ⟨2363038681989102968346901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12602872970608549164516805 2363038681989102968346901)
              ·
                refine ⟨110767438218239201641261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2363038681989102968346901 110767438218239201641261)
                ·
                  rfl

theorem cell22_2912204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 4, 6].length) (baseStart_2912204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912204 prefixEnd_2912204 := by exact prefixLift 2912204
  have htrace : WordTrace (prefixWord ++ tailWord_2912204) baseStart_2912204 baseEnd_2912204 := by
    simpa [prefixWord, tailWord_2912204, baseEnd_2912204] using wordTrace_append hprefix tailTrace_2912204
  have hstable : (prefixWord ++ tailWord_2912204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912204).length < 2 ^ (prefixWord ++ tailWord_2912204).sum := by decide
  have hdescent : baseEnd_2912204 < baseStart_2912204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912210 : List Nat := [3, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2912210 : Nat := 118140960795 + 2912210 * 2 ^ 59
def prefixEnd_2912210 : Nat := 4983230072969 + 3 ^ 40 * 2912210 * 2
def baseEnd_2912210 : Nat := 332302999295590266373777

theorem tailTrace_2912210 : CollatzResearch.WordTrace tailWord_2912210 prefixEnd_2912210 332302999295590266373777 := by
  unfold tailWord_2912210
  simp only [CollatzResearch.WordTrace]
  refine ⟨26554256194892002678947521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70811349853045340477193389 26554256194892002678947521)
  ·
    refine ⟨19915692146169002009210641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26554256194892002678947521 19915692146169002009210641)
    ·
      refine ⟨14936769109626751506907981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19915692146169002009210641 14936769109626751506907981)
      ·
        refine ⟨5601288416110031815090493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14936769109626751506907981 5601288416110031815090493)
        ·
          refine ⟨2100483156041261930658935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5601288416110031815090493 2100483156041261930658935)
          ·
            refine ⟨3150724734061892895988403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100483156041261930658935 3150724734061892895988403)
            ·
              refine ⟨4726087101092839343982605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150724734061892895988403 4726087101092839343982605)
              ·
                refine ⟨1772282662909814753993477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4726087101092839343982605 1772282662909814753993477)
                ·
                  refine ⟨332302999295590266373777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772282662909814753993477 332302999295590266373777)
                  ·
                    rfl

theorem cell22_2912210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2912210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912210 prefixEnd_2912210 := by exact prefixLift 2912210
  have htrace : WordTrace (prefixWord ++ tailWord_2912210) baseStart_2912210 baseEnd_2912210 := by
    simpa [prefixWord, tailWord_2912210, baseEnd_2912210] using wordTrace_append hprefix tailTrace_2912210
  have hstable : (prefixWord ++ tailWord_2912210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912210).length < 2 ^ (prefixWord ++ tailWord_2912210).sum := by decide
  have hdescent : baseEnd_2912210 < baseStart_2912210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912221 : List Nat := [1, 4, 3, 1, 4, 1, 8]
def baseStart_2912221 : Nat := 118140960795 + 2912221 * 2 ^ 59
def prefixEnd_2912221 : Nat := 4983230072969 + 3 ^ 40 * 2912221 * 2
def baseEnd_2912221 : Nat := 36922694941169275448011

theorem tailTrace_2912221 : CollatzResearch.WordTrace tailWord_2912221 prefixEnd_2912221 36922694941169275448011 := by
  unfold tailWord_2912221
  simp only [CollatzResearch.WordTrace]
  refine ⟨106217425982528159594440517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70811617321685439729627011 106217425982528159594440517)
  ·
    refine ⟨19915767371724029923957597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106217425982528159594440517 19915767371724029923957597)
    ·
      refine ⟨7468412764396511221484099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19915767371724029923957597 7468412764396511221484099)
      ·
        refine ⟨11202619146594766832226149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468412764396511221484099 11202619146594766832226149)
        ·
          refine ⟨2100491089986518781042403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11202619146594766832226149 2100491089986518781042403)
          ·
            refine ⟨3150736634979778171563605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100491089986518781042403 3150736634979778171563605)
            ·
              refine ⟨36922694941169275448011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3150736634979778171563605 36922694941169275448011)
              ·
                rfl

theorem cell22_2912221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 8].length) (baseStart_2912221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912221 prefixEnd_2912221 := by exact prefixLift 2912221
  have htrace : WordTrace (prefixWord ++ tailWord_2912221) baseStart_2912221 baseEnd_2912221 := by
    simpa [prefixWord, tailWord_2912221, baseEnd_2912221] using wordTrace_append hprefix tailTrace_2912221
  have hstable : (prefixWord ++ tailWord_2912221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912221).length < 2 ^ (prefixWord ++ tailWord_2912221).sum := by decide
  have hdescent : baseEnd_2912221 < baseStart_2912221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912236 : List Nat := [2, 2, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_2912236 : Nat := 118140960795 + 2912236 * 2 ^ 59
def prefixEnd_2912236 : Nat := 4983230072969 + 3 ^ 40 * 2912236 * 2
def baseEnd_2912236 : Nat := 996917898218115397971251

theorem tailTrace_2912236 : CollatzResearch.WordTrace tailWord_2912236 prefixEnd_2912236 996917898218115397971251 := by
  unfold tailWord_2912236
  simp only [CollatzResearch.WordTrace]
  refine ⟨53108986538736908578118281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70811982051649211437491041 53108986538736908578118281)
  ·
    refine ⟨39831739904052681433588711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53108986538736908578118281 39831739904052681433588711)
    ·
      refine ⟨59747609856079022150383067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39831739904052681433588711 59747609856079022150383067)
      ·
        refine ⟨89621414784118533225574601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59747609856079022150383067 89621414784118533225574601)
        ·
          refine ⟨67216061088088899919180951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89621414784118533225574601 67216061088088899919180951)
          ·
            refine ⟨100824091632133349878771427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67216061088088899919180951 100824091632133349878771427)
            ·
              refine ⟨151236137448200024818157141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100824091632133349878771427 151236137448200024818157141)
              ·
                refine ⟨1772298485721094040837779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 151236137448200024818157141 1772298485721094040837779)
                ·
                  refine ⟨2658447728581641061256669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772298485721094040837779 2658447728581641061256669)
                  ·
                    refine ⟨996917898218115397971251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658447728581641061256669 996917898218115397971251)
                    ·
                      rfl

theorem cell22_2912236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_2912236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912236 prefixEnd_2912236 := by exact prefixLift 2912236
  have htrace : WordTrace (prefixWord ++ tailWord_2912236) baseStart_2912236 baseEnd_2912236 := by
    simpa [prefixWord, tailWord_2912236, baseEnd_2912236] using wordTrace_append hprefix tailTrace_2912236
  have hstable : (prefixWord ++ tailWord_2912236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912236).length < 2 ^ (prefixWord ++ tailWord_2912236).sum := by decide
  have hdescent : baseEnd_2912236 < baseStart_2912236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912249 : List Nat := [1, 2, 1, 3, 1, 5, 1, 3, 5]
def baseStart_2912249 : Nat := 118140960795 + 2912249 * 2 ^ 59
def prefixEnd_2912249 : Nat := 4983230072969 + 3 ^ 40 * 2912249 * 2
def baseEnd_2912249 : Nat := 332307449461262565798737

theorem tailTrace_2912249 : CollatzResearch.WordTrace tailWord_2912249 prefixEnd_2912249 332307449461262565798737 := by
  unfold tailWord_2912249
  simp only [CollatzResearch.WordTrace]
  refine ⟨106218447226426720376459801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70812298150951146917639867 106218447226426720376459801)
  ·
    refine ⟨79663835419820040282344851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106218447226426720376459801 79663835419820040282344851)
    ·
      refine ⟨119495753129730060423517277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79663835419820040282344851 119495753129730060423517277)
      ·
        refine ⟨44810907423648772658818979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119495753129730060423517277 44810907423648772658818979)
        ·
          refine ⟨67216361135473158988228469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44810907423648772658818979 67216361135473158988228469)
          ·
            refine ⟨6301533856450608655146419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67216361135473158988228469 6301533856450608655146419)
            ·
              refine ⟨9452300784675912982719629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301533856450608655146419 9452300784675912982719629)
              ·
                refine ⟨3544612794253467368519861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9452300784675912982719629 3544612794253467368519861)
                ·
                  refine ⟨332307449461262565798737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3544612794253467368519861 332307449461262565798737)
                  ·
                    rfl

theorem cell22_2912249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_2912249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912249 prefixEnd_2912249 := by exact prefixLift 2912249
  have htrace : WordTrace (prefixWord ++ tailWord_2912249) baseStart_2912249 baseEnd_2912249 := by
    simpa [prefixWord, tailWord_2912249, baseEnd_2912249] using wordTrace_append hprefix tailTrace_2912249
  have hstable : (prefixWord ++ tailWord_2912249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912249).length < 2 ^ (prefixWord ++ tailWord_2912249).sum := by decide
  have hdescent : baseEnd_2912249 < baseStart_2912249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912309 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2912309 : Nat := 118140960795 + 2912309 * 2 ^ 59
def prefixEnd_2912309 : Nat := 4983230072969 + 3 ^ 40 * 2912309 * 2
def baseEnd_2912309 : Nat := 996942887609967540896027

theorem tailTrace_2912309 : CollatzResearch.WordTrace tailWord_2912309 prefixEnd_2912309 996942887609967540896027 := by
  unfold tailWord_2912309
  simp only [CollatzResearch.WordTrace]
  refine ⟨106220635606209350623643981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70813757070806233749095987 106220635606209350623643981)
  ·
    refine ⟨39832738352328506483866493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106220635606209350623643981 39832738352328506483866493)
    ·
      refine ⟨14937276882123189931449935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39832738352328506483866493 14937276882123189931449935)
      ·
        refine ⟨22405915323184784897174903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937276882123189931449935 22405915323184784897174903)
        ·
          refine ⟨33608872984777177345762355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22405915323184784897174903 33608872984777177345762355)
          ·
            refine ⟨50413309477165766018643533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33608872984777177345762355 50413309477165766018643533)
            ·
              refine ⟨18904991053937162256991325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50413309477165766018643533 18904991053937162256991325)
              ·
                refine ⟨7089371645226435846371747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18904991053937162256991325 7089371645226435846371747)
                ·
                  refine ⟨10634057467839653769557621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7089371645226435846371747 10634057467839653769557621)
                  ·
                    refine ⟨996942887609967540896027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10634057467839653769557621 996942887609967540896027)
                    ·
                      rfl

theorem cell22_2912309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2912309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912309 prefixEnd_2912309 := by exact prefixLift 2912309
  have htrace : WordTrace (prefixWord ++ tailWord_2912309) baseStart_2912309 baseEnd_2912309 := by
    simpa [prefixWord, tailWord_2912309, baseEnd_2912309] using wordTrace_append hprefix tailTrace_2912309
  have hstable : (prefixWord ++ tailWord_2912309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912309).length < 2 ^ (prefixWord ++ tailWord_2912309).sum := by decide
  have hdescent : baseEnd_2912309 < baseStart_2912309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912405 : List Nat := [1, 3, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_2912405 : Nat := 118140960795 + 2912405 * 2 ^ 59
def prefixEnd_2912405 : Nat := 4983230072969 + 3 ^ 40 * 2912405 * 2
def baseEnd_2912405 : Nat := 996975750371855290495733

theorem tailTrace_2912405 : CollatzResearch.WordTrace tailWord_2912405 prefixEnd_2912405 996975750371855290495733 := by
  unfold tailWord_2912405
  simp only [CollatzResearch.WordTrace]
  refine ⟨106224137013861559019138669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70816091342574372679425779 106224137013861559019138669)
  ·
    refine ⟨39834051380198084632177001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106224137013861559019138669 39834051380198084632177001)
    ·
      refine ⟨29875538535148563474132751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39834051380198084632177001 29875538535148563474132751)
      ·
        refine ⟨44813307802722845211199127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29875538535148563474132751 44813307802722845211199127)
        ·
          refine ⟨67219961704084267816798691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44813307802722845211199127 67219961704084267816798691)
          ·
            refine ⟨100829942556126401725198037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67219961704084267816798691 100829942556126401725198037)
            ·
              refine ⟨2363201778659212540434329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 100829942556126401725198037 2363201778659212540434329)
              ·
                refine ⟨1772401333994409405325747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363201778659212540434329 1772401333994409405325747)
                ·
                  refine ⟨2658602000991614107988621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772401333994409405325747 2658602000991614107988621)
                  ·
                    refine ⟨996975750371855290495733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658602000991614107988621 996975750371855290495733)
                    ·
                      rfl

theorem cell22_2912405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_2912405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912405 prefixEnd_2912405 := by exact prefixLift 2912405
  have htrace : WordTrace (prefixWord ++ tailWord_2912405) baseStart_2912405 baseEnd_2912405 := by
    simpa [prefixWord, tailWord_2912405, baseEnd_2912405] using wordTrace_append hprefix tailTrace_2912405
  have hstable : (prefixWord ++ tailWord_2912405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912405).length < 2 ^ (prefixWord ++ tailWord_2912405).sum := by decide
  have hdescent : baseEnd_2912405 < baseStart_2912405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912418 : List Nat := [3, 3, 1, 3, 1, 2, 1, 3, 5]
def baseStart_2912418 : Nat := 118140960795 + 2912418 * 2 ^ 59
def prefixEnd_2912418 : Nat := 4983230072969 + 3 ^ 40 * 2912418 * 2
def baseEnd_2912418 : Nat := 332326733512509196640231

theorem tailTrace_2912418 : CollatzResearch.WordTrace tailWord_2912418 prefixEnd_2912418 332326733512509196640231 := by
  unfold tailWord_2912418
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556152790703615559840477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70816407441876308159574605 26556152790703615559840477)
  ·
    refine ⟨9958557296513855834940179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26556152790703615559840477 9958557296513855834940179)
    ·
      refine ⟨14937835944770783752410269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958557296513855834940179 14937835944770783752410269)
      ·
        refine ⟨5601688479289043907153851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14937835944770783752410269 5601688479289043907153851)
        ·
          refine ⟨8402532718933565860730777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601688479289043907153851 8402532718933565860730777)
          ·
            refine ⟨6301899539200174395548083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8402532718933565860730777 6301899539200174395548083)
            ·
              refine ⟨9452849308800261593322125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301899539200174395548083 9452849308800261593322125)
              ·
                refine ⟨3544818490800098097495797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9452849308800261593322125 3544818490800098097495797)
                ·
                  refine ⟨332326733512509196640231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3544818490800098097495797 332326733512509196640231)
                  ·
                    rfl

theorem cell22_2912418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_2912418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912418 prefixEnd_2912418 := by exact prefixLift 2912418
  have htrace : WordTrace (prefixWord ++ tailWord_2912418) baseStart_2912418 baseEnd_2912418 := by
    simpa [prefixWord, tailWord_2912418, baseEnd_2912418] using wordTrace_append hprefix tailTrace_2912418
  have hstable : (prefixWord ++ tailWord_2912418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912418).length < 2 ^ (prefixWord ++ tailWord_2912418).sum := by decide
  have hdescent : baseEnd_2912418 < baseStart_2912418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912489 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_2912489 : Nat := 118140960795 + 2912489 * 2 ^ 59
def prefixEnd_2912489 : Nat := 4983230072969 + 3 ^ 40 * 2912489 * 2
def baseEnd_2912489 : Nat := 997004505288507071395475

theorem tailTrace_2912489 : CollatzResearch.WordTrace tailWord_2912489 prefixEnd_2912489 997004505288507071395475 := by
  unfold tailWord_2912489
  simp only [CollatzResearch.WordTrace]
  refine ⟨106227200745557241365196521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70818133830371494243464347 106227200745557241365196521)
  ·
    refine ⟨79670400559167931023897391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106227200745557241365196521 79670400559167931023897391)
    ·
      refine ⟨119505600838751896535846087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79670400559167931023897391 119505600838751896535846087)
      ·
        refine ⟨179258401258127844803769131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119505600838751896535846087 179258401258127844803769131)
        ·
          refine ⟨268887601887191767205653697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179258401258127844803769131 268887601887191767205653697)
          ·
            refine ⟨201665701415393825404240273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268887601887191767205653697 201665701415393825404240273)
            ·
              refine ⟨151249276061545369053180205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201665701415393825404240273 151249276061545369053180205)
              ·
                refine ⟨56718478523079513394942577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151249276061545369053180205 56718478523079513394942577)
                ·
                  refine ⟨42538858892309635046206933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56718478523079513394942577 42538858892309635046206933)
                  ·
                    refine ⟨997004505288507071395475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42538858892309635046206933 997004505288507071395475)
                    ·
                      rfl

theorem cell22_2912489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_2912489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912489 prefixEnd_2912489 := by exact prefixLift 2912489
  have htrace : WordTrace (prefixWord ++ tailWord_2912489) baseStart_2912489 baseEnd_2912489 := by
    simpa [prefixWord, tailWord_2912489, baseEnd_2912489] using wordTrace_append hprefix tailTrace_2912489
  have hstable : (prefixWord ++ tailWord_2912489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912489).length < 2 ^ (prefixWord ++ tailWord_2912489).sum := by decide
  have hdescent : baseEnd_2912489 < baseStart_2912489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912491 : List Nat := [1, 1, 1, 1, 2, 5, 5, 6]
def baseStart_2912491 : Nat := 118140960795 + 2912491 * 2 ^ 59
def prefixEnd_2912491 : Nat := 4983230072969 + 3 ^ 40 * 2912491 * 2
def baseEnd_2912491 : Nat := 110778354436597748093941

theorem tailTrace_2912491 : CollatzResearch.WordTrace tailWord_2912491 prefixEnd_2912491 110778354436597748093941 := by
  unfold tailWord_2912491
  simp only [CollatzResearch.WordTrace]
  refine ⟨106227273691549995706769327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70818182461033330471179551 106227273691549995706769327)
  ·
    refine ⟨159340910537324993560153991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106227273691549995706769327 159340910537324993560153991)
    ·
      refine ⟨239011365805987490340230987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159340910537324993560153991 239011365805987490340230987)
      ·
        refine ⟨358517048708981235510346481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239011365805987490340230987 358517048708981235510346481)
        ·
          refine ⟨268887786531735926632759861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358517048708981235510346481 268887786531735926632759861)
          ·
            refine ⟨25208229987350243121821237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268887786531735926632759861 25208229987350243121821237)
            ·
              refine ⟨2363271561314085292670741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25208229987350243121821237 2363271561314085292670741)
              ·
                refine ⟨110778354436597748093941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2363271561314085292670741 110778354436597748093941)
                ·
                  rfl

theorem cell22_2912491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5, 6].length) (baseStart_2912491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912491 prefixEnd_2912491 := by exact prefixLift 2912491
  have htrace : WordTrace (prefixWord ++ tailWord_2912491) baseStart_2912491 baseEnd_2912491 := by
    simpa [prefixWord, tailWord_2912491, baseEnd_2912491] using wordTrace_append hprefix tailTrace_2912491
  have hstable : (prefixWord ++ tailWord_2912491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912491).length < 2 ^ (prefixWord ++ tailWord_2912491).sum := by decide
  have hdescent : baseEnd_2912491 < baseStart_2912491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912493 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_2912493 : Nat := 118140960795 + 2912493 * 2 ^ 59
def prefixEnd_2912493 : Nat := 4983230072969 + 3 ^ 40 * 2912493 * 2
def baseEnd_2912493 : Nat := 997005874570252394295463

theorem tailTrace_2912493 : CollatzResearch.WordTrace tailWord_2912493 prefixEnd_2912493 997005874570252394295463 := by
  unfold tailWord_2912493
  simp only [CollatzResearch.WordTrace]
  refine ⟨106227346637542750048342133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70818231091695166698894755 106227346637542750048342133)
  ·
    refine ⟨9958813747269632817032075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106227346637542750048342133 9958813747269632817032075)
    ·
      refine ⟨14938220620904449225548113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958813747269632817032075 14938220620904449225548113)
      ·
        refine ⟨11203665465678336919161085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14938220620904449225548113 11203665465678336919161085)
        ·
          refine ⟨4201374549629376344685407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11203665465678336919161085 4201374549629376344685407)
          ·
            refine ⟨6302061824444064517028111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4201374549629376344685407 6302061824444064517028111)
            ·
              refine ⟨9453092736666096775542167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302061824444064517028111 9453092736666096775542167)
              ·
                refine ⟨14179639104999145163313251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9453092736666096775542167 14179639104999145163313251)
                ·
                  refine ⟨21269458657498717744969877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14179639104999145163313251 21269458657498717744969877)
                  ·
                    refine ⟨997005874570252394295463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21269458657498717744969877 997005874570252394295463)
                    ·
                      rfl

theorem cell22_2912493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_2912493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912493 prefixEnd_2912493 := by exact prefixLift 2912493
  have htrace : WordTrace (prefixWord ++ tailWord_2912493) baseStart_2912493 baseEnd_2912493 := by
    simpa [prefixWord, tailWord_2912493, baseEnd_2912493] using wordTrace_append hprefix tailTrace_2912493
  have hstable : (prefixWord ++ tailWord_2912493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912493).length < 2 ^ (prefixWord ++ tailWord_2912493).sum := by decide
  have hdescent : baseEnd_2912493 < baseStart_2912493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912523 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 3, 3]
def baseStart_2912523 : Nat := 118140960795 + 2912523 * 2 ^ 59
def prefixEnd_2912523 : Nat := 4983230072969 + 3 ^ 40 * 2912523 * 2
def baseEnd_2912523 : Nat := 997016144183342316045371

theorem tailTrace_2912523 : CollatzResearch.WordTrace tailWord_2912523 prefixEnd_2912523 997016144183342316045371 := by
  unfold tailWord_2912523
  simp only [CollatzResearch.WordTrace]
  refine ⟨106228440827434065171934223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70818960551622710114622815 106228440827434065171934223)
  ·
    refine ⟨159342661241151097757901335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106228440827434065171934223 159342661241151097757901335)
    ·
      refine ⟨239013991861726646636852003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159342661241151097757901335 239013991861726646636852003)
      ·
        refine ⟨358520987792589969955278005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239013991861726646636852003 358520987792589969955278005)
        ·
          refine ⟨33611342605555309683307313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 358520987792589969955278005 33611342605555309683307313)
          ·
            refine ⟨25208506954166482262480485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33611342605555309683307313 25208506954166482262480485)
            ·
              refine ⟨4726595053906215424215091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25208506954166482262480485 4726595053906215424215091)
              ·
                refine ⟨7089892580859323136322637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726595053906215424215091 7089892580859323136322637)
                ·
                  refine ⟨2658709717822246176120989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7089892580859323136322637 2658709717822246176120989)
                  ·
                    refine ⟨997016144183342316045371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658709717822246176120989 997016144183342316045371)
                    ·
                      rfl

theorem cell22_2912523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 3].length) (baseStart_2912523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912523 prefixEnd_2912523 := by exact prefixLift 2912523
  have htrace : WordTrace (prefixWord ++ tailWord_2912523) baseStart_2912523 baseEnd_2912523 := by
    simpa [prefixWord, tailWord_2912523, baseEnd_2912523] using wordTrace_append hprefix tailTrace_2912523
  have hstable : (prefixWord ++ tailWord_2912523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912523).length < 2 ^ (prefixWord ++ tailWord_2912523).sum := by decide
  have hdescent : baseEnd_2912523 < baseStart_2912523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912542 : List Nat := [4, 3, 2, 1, 1, 3, 2, 6]
def baseStart_2912542 : Nat := 118140960795 + 2912542 * 2 ^ 59
def prefixEnd_2912542 : Nat := 4983230072969 + 3 ^ 40 * 2912542 * 2
def baseEnd_2912542 : Nat := 110780294252403622202257

theorem tailTrace_2912542 : CollatzResearch.WordTrace tailWord_2912542 prefixEnd_2912542 110780294252403622202257 := by
  unfold tailWord_2912542
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278641726795653927109485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70819422542910154277917253 13278641726795653927109485)
  ·
    refine ⟨4979490647548370222666057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13278641726795653927109485 4979490647548370222666057)
    ·
      refine ⟨3734617985661277666999543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4979490647548370222666057 3734617985661277666999543)
      ·
        refine ⟨5601926978491916500499315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3734617985661277666999543 5601926978491916500499315)
        ·
          refine ⟨8402890467737874750748973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5601926978491916500499315 8402890467737874750748973)
          ·
            refine ⟨3151083925401703031530865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8402890467737874750748973 3151083925401703031530865)
            ·
              refine ⟨2363312944051277273648149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3151083925401703031530865 2363312944051277273648149)
              ·
                refine ⟨110780294252403622202257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2363312944051277273648149 110780294252403622202257)
                ·
                  rfl

theorem cell22_2912542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2, 6].length) (baseStart_2912542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912542 prefixEnd_2912542 := by exact prefixLift 2912542
  have htrace : WordTrace (prefixWord ++ tailWord_2912542) baseStart_2912542 baseEnd_2912542 := by
    simpa [prefixWord, tailWord_2912542, baseEnd_2912542] using wordTrace_append hprefix tailTrace_2912542
  have hstable : (prefixWord ++ tailWord_2912542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912542).length < 2 ^ (prefixWord ++ tailWord_2912542).sum := by decide
  have hdescent : baseEnd_2912542 < baseStart_2912542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912574 : List Nat := [4, 2, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2912574 : Nat := 118140960795 + 2912574 * 2 ^ 59
def prefixEnd_2912574 : Nat := 4983230072969 + 3 ^ 40 * 2912574 * 2
def baseEnd_2912574 : Nat := 997033602525595183020215

theorem tailTrace_2912574 : CollatzResearch.WordTrace tailWord_2912574 prefixEnd_2912574 997033602525595183020215 := by
  unfold tailWord_2912574
  simp only [CollatzResearch.WordTrace]
  refine ⟨13278787618781162610255097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70820200633499533921360517 13278787618781162610255097)
  ·
    refine ⟨9959090714085871957691323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13278787618781162610255097 9959090714085871957691323)
    ·
      refine ⟨14938636071128807936536985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9959090714085871957691323 14938636071128807936536985)
      ·
        refine ⟨11203977053346605952402739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14938636071128807936536985 11203977053346605952402739)
        ·
          refine ⟨16805965580019908928604109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203977053346605952402739 16805965580019908928604109)
          ·
            refine ⟨6302237092507465848226541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16805965580019908928604109 6302237092507465848226541)
            ·
              refine ⟨2363338909690299693084953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6302237092507465848226541 2363338909690299693084953)
              ·
                refine ⟨1772504182267724769813715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363338909690299693084953 1772504182267724769813715)
                ·
                  refine ⟨2658756273401587154720573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772504182267724769813715 2658756273401587154720573)
                  ·
                    refine ⟨997033602525595183020215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658756273401587154720573 997033602525595183020215)
                    ·
                      rfl

theorem cell22_2912574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2912574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912574 prefixEnd_2912574 := by exact prefixLift 2912574
  have htrace : WordTrace (prefixWord ++ tailWord_2912574) baseStart_2912574 baseEnd_2912574 := by
    simpa [prefixWord, tailWord_2912574, baseEnd_2912574] using wordTrace_append hprefix tailTrace_2912574
  have hstable : (prefixWord ++ tailWord_2912574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912574).length < 2 ^ (prefixWord ++ tailWord_2912574).sum := by decide
  have hdescent : baseEnd_2912574 < baseStart_2912574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912613 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_2912613 : Nat := 118140960795 + 2912613 * 2 ^ 59
def prefixEnd_2912613 : Nat := 4983230072969 + 3 ^ 40 * 2912613 * 2
def baseEnd_2912613 : Nat := 997046953022612081295095

theorem tailTrace_2912613 : CollatzResearch.WordTrace tailWord_2912613 prefixEnd_2912613 997046953022612081295095 := by
  unfold tailWord_2912613
  simp only [CollatzResearch.WordTrace]
  refine ⟨106231723397108010542710493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70821148931405340361806995 106231723397108010542710493)
  ·
    refine ⟨39836896273915503953516435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106231723397108010542710493 39836896273915503953516435)
    ·
      refine ⟨59755344410873255930274653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39836896273915503953516435 59755344410873255930274653)
      ·
        refine ⟨22408254154077470973852995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59755344410873255930274653 22408254154077470973852995)
        ·
          refine ⟨33612381231116206460779493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22408254154077470973852995 33612381231116206460779493)
          ·
            refine ⟨6302321480834288711396155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33612381231116206460779493 6302321480834288711396155)
            ·
              refine ⟨9453482221251433067094233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6302321480834288711396155 9453482221251433067094233)
              ·
                refine ⟨7090111665938574800320675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9453482221251433067094233 7090111665938574800320675)
                ·
                  refine ⟨10635167498907862200481013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7090111665938574800320675 10635167498907862200481013)
                  ·
                    refine ⟨997046953022612081295095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10635167498907862200481013 997046953022612081295095)
                    ·
                      rfl

theorem cell22_2912613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_2912613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912613 prefixEnd_2912613 := by exact prefixLift 2912613
  have htrace : WordTrace (prefixWord ++ tailWord_2912613) baseStart_2912613 baseEnd_2912613 := by
    simpa [prefixWord, tailWord_2912613, baseEnd_2912613] using wordTrace_append hprefix tailTrace_2912613
  have hstable : (prefixWord ++ tailWord_2912613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912613).length < 2 ^ (prefixWord ++ tailWord_2912613).sum := by decide
  have hdescent : baseEnd_2912613 < baseStart_2912613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912626 : List Nat := [3, 2, 1, 2, 1, 13]
def baseStart_2912626 : Nat := 118140960795 + 2912626 * 2 ^ 59
def prefixEnd_2912626 : Nat := 4983230072969 + 3 ^ 40 * 2912626 * 2
def baseEnd_2912626 : Nat := 12309276582571412107655

theorem tailTrace_2912626 : CollatzResearch.WordTrace tailWord_2912626 prefixEnd_2912626 12309276582571412107655 := by
  unfold tailWord_2912626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26558049386515228440733433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70821465030707275841955821 26558049386515228440733433)
  ·
    refine ⟨19918537039886421330550075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26558049386515228440733433 19918537039886421330550075)
    ·
      refine ⟨29877805559829631995825113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19918537039886421330550075 29877805559829631995825113)
      ·
        refine ⟨22408354169872223996868835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29877805559829631995825113 22408354169872223996868835)
        ·
          refine ⟨33612531254808335995303253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22408354169872223996868835 33612531254808335995303253)
          ·
            refine ⟨12309276582571412107655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 33612531254808335995303253 12309276582571412107655)
            ·
              rfl

theorem cell22_2912626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 13].length) (baseStart_2912626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912626 prefixEnd_2912626 := by exact prefixLift 2912626
  have htrace : WordTrace (prefixWord ++ tailWord_2912626) baseStart_2912626 baseEnd_2912626 := by
    simpa [prefixWord, tailWord_2912626, baseEnd_2912626] using wordTrace_append hprefix tailTrace_2912626
  have hstable : (prefixWord ++ tailWord_2912626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912626).length < 2 ^ (prefixWord ++ tailWord_2912626).sum := by decide
  have hdescent : baseEnd_2912626 < baseStart_2912626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912735 : List Nat := [1, 1, 2, 3, 3, 2, 2, 3, 1, 4]
def baseStart_2912735 : Nat := 118140960795 + 2912735 * 2 ^ 59
def prefixEnd_2912735 : Nat := 4983230072969 + 3 ^ 40 * 2912735 * 2
def baseEnd_2912735 : Nat := 997088716115844429744721

theorem tailTrace_2912735 : CollatzResearch.WordTrace tailWord_2912735 prefixEnd_2912735 997088716115844429744721 := by
  unfold tailWord_2912735
  simp only [CollatzResearch.WordTrace]
  refine ⟨106236173102666025378651659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70824115401777350252434439 106236173102666025378651659)
  ·
    refine ⟨159354259653999038067977489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106236173102666025378651659 159354259653999038067977489)
    ·
      refine ⟨119515694740499278550983117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159354259653999038067977489 119515694740499278550983117)
      ·
        refine ⟨44818385527687229456618669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119515694740499278550983117 44818385527687229456618669)
        ·
          refine ⟨16806894572882711046232001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44818385527687229456618669 16806894572882711046232001)
          ·
            refine ⟨12605170929662033284674001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16806894572882711046232001 12605170929662033284674001)
            ·
              refine ⟨9453878197246524963505501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12605170929662033284674001 9453878197246524963505501)
              ·
                refine ⟨3545204323967446861314563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9453878197246524963505501 3545204323967446861314563)
                ·
                  refine ⟨5317806485951170291971845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545204323967446861314563 5317806485951170291971845)
                  ·
                    refine ⟨997088716115844429744721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5317806485951170291971845 997088716115844429744721)
                    ·
                      rfl

theorem cell22_2912735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_2912735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912735 prefixEnd_2912735 := by exact prefixLift 2912735
  have htrace : WordTrace (prefixWord ++ tailWord_2912735) baseStart_2912735 baseEnd_2912735 := by
    simpa [prefixWord, tailWord_2912735, baseEnd_2912735] using wordTrace_append hprefix tailTrace_2912735
  have hstable : (prefixWord ++ tailWord_2912735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912735).length < 2 ^ (prefixWord ++ tailWord_2912735).sum := by decide
  have hdescent : baseEnd_2912735 < baseStart_2912735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912750 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_2912750 : Nat := 118140960795 + 2912750 * 2 ^ 59
def prefixEnd_2912750 : Nat := 4983230072969 + 3 ^ 40 * 2912750 * 2
def baseEnd_2912750 : Nat := 332364616974129796873225

theorem tailTrace_2912750 : CollatzResearch.WordTrace tailWord_2912750 prefixEnd_2912750 332364616974129796873225 := by
  unfold tailWord_2912750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13279590024701460367555963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70824480131741121960298469 13279590024701460367555963)
  ·
    refine ⟨19919385037052190551333945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13279590024701460367555963 19919385037052190551333945)
    ·
      refine ⟨14939538777789142913500459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19919385037052190551333945 14939538777789142913500459)
      ·
        refine ⟨22409308166683714370250689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14939538777789142913500459 22409308166683714370250689)
        ·
          refine ⟨16806981125012785777688017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22409308166683714370250689 16806981125012785777688017)
          ·
            refine ⟨12605235843759589333266013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16806981125012785777688017 12605235843759589333266013)
            ·
              refine ⟨4726963441409845999974755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12605235843759589333266013 4726963441409845999974755)
              ·
                refine ⟨7090445162114768999962133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726963441409845999974755 7090445162114768999962133)
                ·
                  refine ⟨332364616974129796873225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7090445162114768999962133 332364616974129796873225)
                  ·
                    rfl

theorem cell22_2912750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_2912750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912750 prefixEnd_2912750 := by exact prefixLift 2912750
  have htrace : WordTrace (prefixWord ++ tailWord_2912750) baseStart_2912750 baseEnd_2912750 := by
    simpa [prefixWord, tailWord_2912750, baseEnd_2912750] using wordTrace_append hprefix tailTrace_2912750
  have hstable : (prefixWord ++ tailWord_2912750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912750).length < 2 ^ (prefixWord ++ tailWord_2912750).sum := by decide
  have hdescent : baseEnd_2912750 < baseStart_2912750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912778 : List Nat := [3, 1, 2, 2, 2, 1, 1, 10]
def baseStart_2912778 : Nat := 118140960795 + 2912778 * 2 ^ 59
def prefixEnd_2912778 : Nat := 4983230072969 + 3 ^ 40 * 2912778 * 2
def baseEnd_2912778 : Nat := 110789270654956294546621

theorem tailTrace_2912778 : CollatzResearch.WordTrace tailWord_2912778 prefixEnd_2912778 110789270654956294546621 := by
  unfold tailWord_2912778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26559435360377560930616747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70825160961006829148311325 26559435360377560930616747)
  ·
    refine ⟨39839153040566341395925121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26559435360377560930616747 39839153040566341395925121)
    ·
      refine ⟨29879364780424756046943841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39839153040566341395925121 29879364780424756046943841)
      ·
        refine ⟨22409523585318567035207881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29879364780424756046943841 22409523585318567035207881)
        ·
          refine ⟨16807142688988925276405911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22409523585318567035207881 16807142688988925276405911)
          ·
            refine ⟨25210714033483387914608867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16807142688988925276405911 25210714033483387914608867)
            ·
              refine ⟨37816071050225081871913301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25210714033483387914608867 37816071050225081871913301)
              ·
                refine ⟨110789270654956294546621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 37816071050225081871913301 110789270654956294546621)
                ·
                  rfl

theorem cell22_2912778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 10].length) (baseStart_2912778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912778 prefixEnd_2912778 := by exact prefixLift 2912778
  have htrace : WordTrace (prefixWord ++ tailWord_2912778) baseStart_2912778 baseEnd_2912778 := by
    simpa [prefixWord, tailWord_2912778, baseEnd_2912778] using wordTrace_append hprefix tailTrace_2912778
  have hstable : (prefixWord ++ tailWord_2912778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912778).length < 2 ^ (prefixWord ++ tailWord_2912778).sum := by decide
  have hdescent : baseEnd_2912778 < baseStart_2912778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912780 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_2912780 : Nat := 118140960795 + 2912780 * 2 ^ 59
def prefixEnd_2912780 : Nat := 4983230072969 + 3 ^ 40 * 2912780 * 2
def baseEnd_2912780 : Nat := 997104120535479312369583

theorem tailTrace_2912780 : CollatzResearch.WordTrace tailWord_2912780 prefixEnd_2912780 997104120535479312369583 := by
  unfold tailWord_2912780
  simp only [CollatzResearch.WordTrace]
  refine ⟨53118907193751499032019897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70825209591668665376026529 53118907193751499032019897)
  ·
    refine ⟨39839180395313624274014923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53118907193751499032019897 39839180395313624274014923)
    ·
      refine ⟨59758770592970436411022385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39839180395313624274014923 59758770592970436411022385)
      ·
        refine ⟨44819077944727827308266789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59758770592970436411022385 44819077944727827308266789)
        ·
          refine ⟨8403577114636467620300023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44819077944727827308266789 8403577114636467620300023)
          ·
            refine ⟨12605365671954701430450035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8403577114636467620300023 12605365671954701430450035)
            ·
              refine ⟨18908048507932052145675053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12605365671954701430450035 18908048507932052145675053)
              ·
                refine ⟨7090518190474519554628145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18908048507932052145675053 7090518190474519554628145)
                ·
                  refine ⟨5317888642855889665971109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090518190474519554628145 5317888642855889665971109)
                  ·
                    refine ⟨997104120535479312369583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5317888642855889665971109 997104120535479312369583)
                    ·
                      rfl

theorem cell22_2912780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_2912780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912780 prefixEnd_2912780 := by exact prefixLift 2912780
  have htrace : WordTrace (prefixWord ++ tailWord_2912780) baseStart_2912780 baseEnd_2912780 := by
    simpa [prefixWord, tailWord_2912780, baseEnd_2912780] using wordTrace_append hprefix tailTrace_2912780
  have hstable : (prefixWord ++ tailWord_2912780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912780).length < 2 ^ (prefixWord ++ tailWord_2912780).sum := by decide
  have hdescent : baseEnd_2912780 < baseStart_2912780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912844 : List Nat := [2, 2, 1, 3, 1, 2, 4, 3, 1, 3]
def baseStart_2912844 : Nat := 118140960795 + 2912844 * 2 ^ 59
def prefixEnd_2912844 : Nat := 4983230072969 + 3 ^ 40 * 2912844 * 2
def baseEnd_2912844 : Nat := 997126029043404478769387

theorem tailTrace_2912844 : CollatzResearch.WordTrace tailWord_2912844 prefixEnd_2912844 997126029043404478769387 := by
  unfold tailWord_2912844
  simp only [CollatzResearch.WordTrace]
  refine ⟨53120074329635568497184793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70826765772847424662913057 53120074329635568497184793)
  ·
    refine ⟨39840055747226676372888595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53120074329635568497184793 39840055747226676372888595)
    ·
      refine ⟨59760083620840014559332893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39840055747226676372888595 59760083620840014559332893)
      ·
        refine ⟨22410031357815005459749835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59760083620840014559332893 22410031357815005459749835)
        ·
          refine ⟨33615047036722508189624753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22410031357815005459749835 33615047036722508189624753)
          ·
            refine ⟨25211285277541881142218565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33615047036722508189624753 25211285277541881142218565)
            ·
              refine ⟨4727115989539102714165981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25211285277541881142218565 4727115989539102714165981)
              ·
                refine ⟨1772668496077163517812243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4727115989539102714165981 1772668496077163517812243)
                ·
                  refine ⟨2659002744115745276718365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772668496077163517812243 2659002744115745276718365)
                  ·
                    refine ⟨997126029043404478769387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659002744115745276718365 997126029043404478769387)
                    ·
                      rfl

theorem cell22_2912844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 3, 1, 3].length) (baseStart_2912844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912844 prefixEnd_2912844 := by exact prefixLift 2912844
  have htrace : WordTrace (prefixWord ++ tailWord_2912844) baseStart_2912844 baseEnd_2912844 := by
    simpa [prefixWord, tailWord_2912844, baseEnd_2912844] using wordTrace_append hprefix tailTrace_2912844
  have hstable : (prefixWord ++ tailWord_2912844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912844).length < 2 ^ (prefixWord ++ tailWord_2912844).sum := by decide
  have hdescent : baseEnd_2912844 < baseStart_2912844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912915 : List Nat := [1, 1, 1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_2912915 : Nat := 118140960795 + 2912915 * 2 ^ 59
def prefixEnd_2912915 : Nat := 4983230072969 + 3 ^ 40 * 2912915 * 2
def baseEnd_2912915 : Nat := 997150333794383960244169

theorem tailTrace_2912915 : CollatzResearch.WordTrace tailWord_2912915 prefixEnd_2912915 997150333794383960244169 := by
  unfold tailWord_2912915
  simp only [CollatzResearch.WordTrace]
  refine ⟨106242738242013916120204199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70828492161342610746802799 106242738242013916120204199)
  ·
    refine ⟨159364107363020874180306299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106242738242013916120204199 159364107363020874180306299)
    ·
      refine ⟨239046161044531311270459449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159364107363020874180306299 239046161044531311270459449)
      ·
        refine ⟨179284620783398483452844587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239046161044531311270459449 179284620783398483452844587)
        ·
          refine ⟨268926931175097725179266881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179284620783398483452844587 268926931175097725179266881)
          ·
            refine ⟨201695198381323293884450161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268926931175097725179266881 201695198381323293884450161)
            ·
              refine ⟨151271398785992470413337621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201695198381323293884450161 151271398785992470413337621)
              ·
                refine ⟨7090846818093397050625201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151271398785992470413337621 7090846818093397050625201)
                ·
                  refine ⟨5318135113570047787968901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090846818093397050625201 5318135113570047787968901)
                  ·
                    refine ⟨997150333794383960244169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318135113570047787968901 997150333794383960244169)
                    ·
                      rfl

theorem cell22_2912915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_2912915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912915 prefixEnd_2912915 := by exact prefixLift 2912915
  have htrace : WordTrace (prefixWord ++ tailWord_2912915) baseStart_2912915 baseEnd_2912915 := by
    simpa [prefixWord, tailWord_2912915, baseEnd_2912915] using wordTrace_append hprefix tailTrace_2912915
  have hstable : (prefixWord ++ tailWord_2912915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912915).length < 2 ^ (prefixWord ++ tailWord_2912915).sum := by decide
  have hdescent : baseEnd_2912915 < baseStart_2912915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912919 : List Nat := [1, 1, 3, 3, 2, 1, 5, 2, 4]
def baseStart_2912919 : Nat := 118140960795 + 2912919 * 2 ^ 59
def prefixEnd_2912919 : Nat := 4983230072969 + 3 ^ 40 * 2912919 * 2
def baseEnd_2912919 : Nat := 332383901025376427714719

theorem tailTrace_2912919 : CollatzResearch.WordTrace tailWord_2912919 prefixEnd_2912919 332383901025376427714719 := by
  unfold tailWord_2912919
  simp only [CollatzResearch.WordTrace]
  refine ⟨106242884133999424803349811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70828589422666283202233207 106242884133999424803349811)
  ·
    refine ⟨159364326200999137205024717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106242884133999424803349811 159364326200999137205024717)
    ·
      refine ⟨59761622325374676451884269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159364326200999137205024717 59761622325374676451884269)
      ·
        refine ⟨22410608372015503669456601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59761622325374676451884269 22410608372015503669456601)
        ·
          refine ⟨16807956279011627752092451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22410608372015503669456601 16807956279011627752092451)
          ·
            refine ⟨25211934418517441628138677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16807956279011627752092451 25211934418517441628138677)
            ·
              refine ⟨2363618851736010152638001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25211934418517441628138677 2363618851736010152638001)
              ·
                refine ⟨1772714138802007614478501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363618851736010152638001 1772714138802007614478501)
                ·
                  refine ⟨332383901025376427714719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772714138802007614478501 332383901025376427714719)
                  ·
                    rfl

theorem cell22_2912919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 4].length) (baseStart_2912919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912919 prefixEnd_2912919 := by exact prefixLift 2912919
  have htrace : WordTrace (prefixWord ++ tailWord_2912919) baseStart_2912919 baseEnd_2912919 := by
    simpa [prefixWord, tailWord_2912919, baseEnd_2912919] using wordTrace_append hprefix tailTrace_2912919
  have hstable : (prefixWord ++ tailWord_2912919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912919).length < 2 ^ (prefixWord ++ tailWord_2912919).sum := by decide
  have hdescent : baseEnd_2912919 < baseStart_2912919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912938 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2912938 : Nat := 118140960795 + 2912938 * 2 ^ 59
def prefixEnd_2912938 : Nat := 4983230072969 + 3 ^ 40 * 2912938 * 2
def baseEnd_2912938 : Nat := 997158207164419566919099

theorem tailTrace_2912938 : CollatzResearch.WordTrace tailWord_2912938 prefixEnd_2912938 997158207164419566919099 := by
  unfold tailWord_2912938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26560894280232647762072867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70829051413953727365527645 26560894280232647762072867)
  ·
    refine ⟨39841341420348971643109301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26560894280232647762072867 39841341420348971643109301)
    ·
      refine ⟨3735125758157716091541497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39841341420348971643109301 3735125758157716091541497)
      ·
        refine ⟨2801344318618287068656123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3735125758157716091541497 2801344318618287068656123)
        ·
          refine ⟨4202016477927430602984185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801344318618287068656123 4202016477927430602984185)
          ·
            refine ⟨3151512358445572952238139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4202016477927430602984185 3151512358445572952238139)
            ·
              refine ⟨4727268537668359428357209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151512358445572952238139 4727268537668359428357209)
              ·
                refine ⟨3545451403251269571267907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727268537668359428357209 3545451403251269571267907)
                ·
                  refine ⟨5318177104876904356901861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545451403251269571267907 5318177104876904356901861)
                  ·
                    refine ⟨997158207164419566919099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318177104876904356901861 997158207164419566919099)
                    ·
                      rfl

theorem cell22_2912938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2912938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912938 prefixEnd_2912938 := by exact prefixLift 2912938
  have htrace : WordTrace (prefixWord ++ tailWord_2912938) baseStart_2912938 baseEnd_2912938 := by
    simpa [prefixWord, tailWord_2912938, baseEnd_2912938] using wordTrace_append hprefix tailTrace_2912938
  have hstable : (prefixWord ++ tailWord_2912938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912938).length < 2 ^ (prefixWord ++ tailWord_2912938).sum := by decide
  have hdescent : baseEnd_2912938 < baseStart_2912938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912949 : List Nat := [1, 3, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2912949 : Nat := 118140960795 + 2912949 * 2 ^ 59
def prefixEnd_2912949 : Nat := 4983230072969 + 3 ^ 40 * 2912949 * 2
def baseEnd_2912949 : Nat := 997161972689219204894065

theorem tailTrace_2912949 : CollatzResearch.WordTrace tailWord_2912949 prefixEnd_2912949 997161972689219204894065 := by
  unfold tailWord_2912949
  simp only [CollatzResearch.WordTrace]
  refine ⟨106243978323890739926941901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70829318882593826617961267 106243978323890739926941901)
  ·
    refine ⟨39841491871459027472603213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106243978323890739926941901 39841491871459027472603213)
    ·
      refine ⟨14940559451797135302226205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39841491871459027472603213 14940559451797135302226205)
      ·
        refine ⟨5602709794423925738334827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14940559451797135302226205 5602709794423925738334827)
        ·
          refine ⟨8404064691635888607502241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5602709794423925738334827 8404064691635888607502241)
          ·
            refine ⟨6303048518726916455626681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8404064691635888607502241 6303048518726916455626681)
            ·
              refine ⟨4727286389045187341720011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303048518726916455626681 4727286389045187341720011)
              ·
                refine ⟨7090929583567781012580017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727286389045187341720011 7090929583567781012580017)
                ·
                  refine ⟨5318197187675835759435013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090929583567781012580017 5318197187675835759435013)
                  ·
                    refine ⟨997161972689219204894065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318197187675835759435013 997161972689219204894065)
                    ·
                      rfl

theorem cell22_2912949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2912949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912949 prefixEnd_2912949 := by exact prefixLift 2912949
  have htrace : WordTrace (prefixWord ++ tailWord_2912949) baseStart_2912949 baseEnd_2912949 := by
    simpa [prefixWord, tailWord_2912949, baseEnd_2912949] using wordTrace_append hprefix tailTrace_2912949
  have hstable : (prefixWord ++ tailWord_2912949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912949).length < 2 ^ (prefixWord ++ tailWord_2912949).sum := by decide
  have hdescent : baseEnd_2912949 < baseStart_2912949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2912981 : List Nat := [1, 3, 2, 5, 2, 1, 1, 7]
def baseStart_2912981 : Nat := 118140960795 + 2912981 * 2 ^ 59
def prefixEnd_2912981 : Nat := 4983230072969 + 3 ^ 40 * 2912981 * 2
def baseEnd_2912981 : Nat := 110796991882575754232663

theorem tailTrace_2912981 : CollatzResearch.WordTrace tailWord_2912981 prefixEnd_2912981 110796991882575754232663 := by
  unfold tailWord_2912981
  simp only [CollatzResearch.WordTrace]
  refine ⟨106245145459774809392106797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70830096973183206261404531 106245145459774809392106797)
  ·
    refine ⟨39841929547415553522040049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106245145459774809392106797 39841929547415553522040049)
    ·
      refine ⟨29881447160561665141530037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39841929547415553522040049 29881447160561665141530037)
      ·
        refine ⟨2801385671302656107018441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29881447160561665141530037 2801385671302656107018441)
        ·
          refine ⟨2101039253476992080263831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2801385671302656107018441 2101039253476992080263831)
          ·
            refine ⟨3151558880215488120395747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101039253476992080263831 3151558880215488120395747)
            ·
              refine ⟨4727338320323232180593621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151558880215488120395747 4727338320323232180593621)
              ·
                refine ⟨110796991882575754232663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4727338320323232180593621 110796991882575754232663)
                ·
                  rfl

theorem cell22_2912981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 7].length) (baseStart_2912981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2912981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2912981 prefixEnd_2912981 := by exact prefixLift 2912981
  have htrace : WordTrace (prefixWord ++ tailWord_2912981) baseStart_2912981 baseEnd_2912981 := by
    simpa [prefixWord, tailWord_2912981, baseEnd_2912981] using wordTrace_append hprefix tailTrace_2912981
  have hstable : (prefixWord ++ tailWord_2912981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2912981).length < 2 ^ (prefixWord ++ tailWord_2912981).sum := by decide
  have hdescent : baseEnd_2912981 < baseStart_2912981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2912981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913026 : List Nat := [3, 4, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2913026 : Nat := 118140960795 + 2913026 * 2 ^ 59
def prefixEnd_2913026 : Nat := 4983230072969 + 3 ^ 40 * 2913026 * 2
def baseEnd_2913026 : Nat := 332396110454272223572943

theorem tailTrace_2913026 : CollatzResearch.WordTrace tailWord_2913026 prefixEnd_2913026 332396110454272223572943 := by
  unfold tailWord_2913026
  simp only [CollatzResearch.WordTrace]
  refine ⟨26561696686152945519373733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70831191163074521384996621 26561696686152945519373733)
  ·
    refine ⟨4980318128653677284882575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26561696686152945519373733 4980318128653677284882575)
    ·
      refine ⟨7470477192980515927323863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980318128653677284882575 7470477192980515927323863)
      ·
        refine ⟨11205715789470773890985795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7470477192980515927323863 11205715789470773890985795)
        ·
          refine ⟨16808573684206160836478693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11205715789470773890985795 16808573684206160836478693)
          ·
            refine ⟨3151607565788655156839755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16808573684206160836478693 3151607565788655156839755)
            ·
              refine ⟨4727411348682982735259633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151607565788655156839755 4727411348682982735259633)
              ·
                refine ⟨3545558511512237051444725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727411348682982735259633 3545558511512237051444725)
                ·
                  refine ⟨332396110454272223572943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3545558511512237051444725 332396110454272223572943)
                  ·
                    rfl

theorem cell22_2913026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2913026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913026 prefixEnd_2913026 := by exact prefixLift 2913026
  have htrace : WordTrace (prefixWord ++ tailWord_2913026) baseStart_2913026 baseEnd_2913026 := by
    simpa [prefixWord, tailWord_2913026, baseEnd_2913026] using wordTrace_append hprefix tailTrace_2913026
  have hstable : (prefixWord ++ tailWord_2913026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913026).length < 2 ^ (prefixWord ++ tailWord_2913026).sum := by decide
  have hdescent : baseEnd_2913026 < baseStart_2913026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913065 : List Nat := [1, 2, 1, 1, 1, 1, 1, 14]
def baseStart_2913065 : Nat := 118140960795 + 2913065 * 2 ^ 59
def prefixEnd_2913065 : Nat := 4983230072969 + 3 ^ 40 * 2913065 * 2
def baseEnd_2913065 : Nat := 110800186873314840999301

theorem tailTrace_2913065 : CollatzResearch.WordTrace tailWord_2913065 prefixEnd_2913065 110800186873314840999301 := by
  unfold tailWord_2913065
  simp only [CollatzResearch.WordTrace]
  refine ⟨106248209191470491738164649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70832139460980327825443099 106248209191470491738164649)
  ·
    refine ⟨79686156893602868803623487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106248209191470491738164649 79686156893602868803623487)
    ·
      refine ⟨119529235340404303205435231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79686156893602868803623487 119529235340404303205435231)
      ·
        refine ⟨179293853010606454808152847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119529235340404303205435231 179293853010606454808152847)
        ·
          refine ⟨268940779515909682212229271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179293853010606454808152847 268940779515909682212229271)
          ·
            refine ⟨403411169273864523318343907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 268940779515909682212229271 403411169273864523318343907)
            ·
              refine ⟨605116753910796784977515861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403411169273864523318343907 605116753910796784977515861)
              ·
                refine ⟨110800186873314840999301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 605116753910796784977515861 110800186873314840999301)
                ·
                  rfl

theorem cell22_2913065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 14].length) (baseStart_2913065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913065 prefixEnd_2913065 := by exact prefixLift 2913065
  have htrace : WordTrace (prefixWord ++ tailWord_2913065) baseStart_2913065 baseEnd_2913065 := by
    simpa [prefixWord, tailWord_2913065, baseEnd_2913065] using wordTrace_append hprefix tailTrace_2913065
  have hstable : (prefixWord ++ tailWord_2913065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913065).length < 2 ^ (prefixWord ++ tailWord_2913065).sum := by decide
  have hdescent : baseEnd_2913065 < baseStart_2913065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913159 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2913159 : Nat := 118140960795 + 2913159 * 2 ^ 59
def prefixEnd_2913159 : Nat := 4983230072969 + 3 ^ 40 * 2913159 * 2
def baseEnd_2913159 : Nat := 997233859980848657143421

theorem tailTrace_2913159 : CollatzResearch.WordTrace tailWord_2913159 prefixEnd_2913159 997233859980848657143421 := by
  unfold tailWord_2913159
  simp only [CollatzResearch.WordTrace]
  refine ⟨106251637653129945792086531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70834425102086630528057687 106251637653129945792086531)
  ·
    refine ⟨159377456479694918688129797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106251637653129945792086531 159377456479694918688129797)
    ·
      refine ⟨29883273089942797254024337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159377456479694918688129797 29883273089942797254024337)
      ·
        refine ⟨22412454817457097940518253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29883273089942797254024337 22412454817457097940518253)
        ·
          refine ⟨8404670556546411727694345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22412454817457097940518253 8404670556546411727694345)
          ·
            refine ⟨6303502917409808795770759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8404670556546411727694345 6303502917409808795770759)
            ·
              refine ⟨9455254376114713193656139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303502917409808795770759 9455254376114713193656139)
              ·
                refine ⟨14182881564172069790484209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9455254376114713193656139 14182881564172069790484209)
                ·
                  refine ⟨10637161173129052342863157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14182881564172069790484209 10637161173129052342863157)
                  ·
                    refine ⟨997233859980848657143421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10637161173129052342863157 997233859980848657143421)
                    ·
                      rfl

theorem cell22_2913159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2913159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913159 prefixEnd_2913159 := by exact prefixLift 2913159
  have htrace : WordTrace (prefixWord ++ tailWord_2913159) baseStart_2913159 baseEnd_2913159 := by
    simpa [prefixWord, tailWord_2913159, baseEnd_2913159] using wordTrace_append hprefix tailTrace_2913159
  have hstable : (prefixWord ++ tailWord_2913159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913159).length < 2 ^ (prefixWord ++ tailWord_2913159).sum := by decide
  have hdescent : baseEnd_2913159 < baseStart_2913159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913232 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 1, 9]
def baseStart_2913232 : Nat := 118140960795 + 2913232 * 2 ^ 59
def prefixEnd_2913232 : Nat := 4983230072969 + 3 ^ 40 * 2913232 * 2
def baseEnd_2913232 : Nat := 997258849372700800068197

theorem tailTrace_2913232 : CollatzResearch.WordTrace tailWord_2913232 prefixEnd_2913232 997258849372700800068197 := by
  unfold tailWord_2913232
  simp only [CollatzResearch.WordTrace]
  refine ⟨53127150090932739629746975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70836200121243652839662633 53127150090932739629746975)
  ·
    refine ⟨79690725136399109444620463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53127150090932739629746975 79690725136399109444620463)
    ·
      refine ⟨119536087704598664166930695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79690725136399109444620463 119536087704598664166930695)
      ·
        refine ⟨179304131556897996250396043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119536087704598664166930695 179304131556897996250396043)
        ·
          refine ⟨268956197335346994375594065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179304131556897996250396043 268956197335346994375594065)
          ·
            refine ⟨201717148001510245781695549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268956197335346994375594065 201717148001510245781695549)
            ·
              refine ⟨75643930500566342168135831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201717148001510245781695549 75643930500566342168135831)
              ·
                refine ⟨113465895750849513252203747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75643930500566342168135831 113465895750849513252203747)
                ·
                  refine ⟨170198843626274269878305621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113465895750849513252203747 170198843626274269878305621)
                  ·
                    refine ⟨997258849372700800068197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 170198843626274269878305621 997258849372700800068197)
                    ·
                      rfl

theorem cell22_2913232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_2913232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913232 prefixEnd_2913232 := by exact prefixLift 2913232
  have htrace : WordTrace (prefixWord ++ tailWord_2913232) baseStart_2913232 baseEnd_2913232 := by
    simpa [prefixWord, tailWord_2913232, baseEnd_2913232] using wordTrace_append hprefix tailTrace_2913232
  have hstable : (prefixWord ++ tailWord_2913232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913232).length < 2 ^ (prefixWord ++ tailWord_2913232).sum := by decide
  have hdescent : baseEnd_2913232 < baseStart_2913232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913238 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2913238 : Nat := 118140960795 + 2913238 * 2 ^ 59
def prefixEnd_2913238 : Nat := 4983230072969 + 3 ^ 40 * 2913238 * 2
def baseEnd_2913238 : Nat := 997260903295318784418179

theorem tailTrace_2913238 : CollatzResearch.WordTrace tailWord_2913238 prefixEnd_2913238 997260903295318784418179 := by
  unfold tailWord_2913238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640907438740233892763273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70836346013229161522808245 6640907438740233892763273)
  ·
    refine ⟨4980680579055175419572455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640907438740233892763273 4980680579055175419572455)
    ·
      refine ⟨7471020868582763129358683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980680579055175419572455 7471020868582763129358683)
      ·
        refine ⟨11206531302874144694038025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471020868582763129358683 11206531302874144694038025)
        ·
          refine ⟨8404898477155608520528519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11206531302874144694038025 8404898477155608520528519)
          ·
            refine ⟨12607347715733412780792779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8404898477155608520528519 12607347715733412780792779)
            ·
              refine ⟨18911021573600119171189169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12607347715733412780792779 18911021573600119171189169)
              ·
                refine ⟨14183266180200089378391877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18911021573600119171189169 14183266180200089378391877)
                ·
                  refine ⟨2659362408787516758448477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14183266180200089378391877 2659362408787516758448477)
                  ·
                    refine ⟨997260903295318784418179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659362408787516758448477 997260903295318784418179)
                    ·
                      rfl

theorem cell22_2913238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2913238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913238 prefixEnd_2913238 := by exact prefixLift 2913238
  have htrace : WordTrace (prefixWord ++ tailWord_2913238) baseStart_2913238 baseEnd_2913238 := by
    simpa [prefixWord, tailWord_2913238, baseEnd_2913238] using wordTrace_append hprefix tailTrace_2913238
  have hstable : (prefixWord ++ tailWord_2913238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913238).length < 2 ^ (prefixWord ++ tailWord_2913238).sum := by decide
  have hdescent : baseEnd_2913238 < baseStart_2913238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913253 : List Nat := [1, 3, 1, 6, 1, 1, 1, 2, 2, 4]
def baseStart_2913253 : Nat := 118140960795 + 2913253 * 2 ^ 59
def prefixEnd_2913253 : Nat := 4983230072969 + 3 ^ 40 * 2913253 * 2
def baseEnd_2913253 : Nat := 997266038101863745293133

theorem tailTrace_2913253 : CollatzResearch.WordTrace tailWord_2913253 prefixEnd_2913253 997266038101863745293133 := by
  unfold tailWord_2913253
  simp only [CollatzResearch.WordTrace]
  refine ⟨106255066114789399846008413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70836710743192933230672275 106255066114789399846008413)
  ·
    refine ⟨39845649793046024942253155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106255066114789399846008413 39845649793046024942253155)
    ·
      refine ⟨59768474689569037413379733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39845649793046024942253155 59768474689569037413379733)
      ·
        refine ⟨2801647251073548628752175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 59768474689569037413379733 2801647251073548628752175)
        ·
          refine ⟨4202470876610322943128263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801647251073548628752175 4202470876610322943128263)
          ·
            refine ⟨6303706314915484414692395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202470876610322943128263 6303706314915484414692395)
            ·
              refine ⟨9455559472373226622038593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303706314915484414692395 9455559472373226622038593)
              ·
                refine ⟨7091669604279919966528945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9455559472373226622038593 7091669604279919966528945)
                ·
                  refine ⟨5318752203209939974896709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7091669604279919966528945 5318752203209939974896709)
                  ·
                    refine ⟨997266038101863745293133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318752203209939974896709 997266038101863745293133)
                    ·
                      rfl

theorem cell22_2913253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 4].length) (baseStart_2913253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913253 prefixEnd_2913253 := by exact prefixLift 2913253
  have htrace : WordTrace (prefixWord ++ tailWord_2913253) baseStart_2913253 baseEnd_2913253 := by
    simpa [prefixWord, tailWord_2913253, baseEnd_2913253] using wordTrace_append hprefix tailTrace_2913253
  have hstable : (prefixWord ++ tailWord_2913253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913253).length < 2 ^ (prefixWord ++ tailWord_2913253).sum := by decide
  have hdescent : baseEnd_2913253 < baseStart_2913253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913324 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 6]
def baseStart_2913324 : Nat := 118140960795 + 2913324 * 2 ^ 59
def prefixEnd_2913324 : Nat := 4983230072969 + 3 ^ 40 * 2913324 * 2
def baseEnd_2913324 : Nat := 332430114284281075589305

theorem tailTrace_2913324 : CollatzResearch.WordTrace tailWord_2913324 prefixEnd_2913324 332430114284281075589305 := by
  unfold tailWord_2913324
  simp only [CollatzResearch.WordTrace]
  refine ⟨53128827848766089485921513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70838437131688119314562017 53128827848766089485921513)
  ·
    refine ⟨39846620886574567114441135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53128827848766089485921513 39846620886574567114441135)
    ·
      refine ⟨59769931329861850671661703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39846620886574567114441135 59769931329861850671661703)
      ·
        refine ⟨89654896994792776007492555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59769931329861850671661703 89654896994792776007492555)
        ·
          refine ⟨134482345492189164011238833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89654896994792776007492555 134482345492189164011238833)
          ·
            refine ⟨100861759119141873008429125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134482345492189164011238833 100861759119141873008429125)
            ·
              refine ⟨18911579834839101189080461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100861759119141873008429125 18911579834839101189080461)
              ·
                refine ⟨7091842438064662945905173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18911579834839101189080461 7091842438064662945905173)
                ·
                  refine ⟨332430114284281075589305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7091842438064662945905173 332430114284281075589305)
                  ·
                    rfl

theorem cell22_2913324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 6].length) (baseStart_2913324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913324 prefixEnd_2913324 := by exact prefixLift 2913324
  have htrace : WordTrace (prefixWord ++ tailWord_2913324) baseStart_2913324 baseEnd_2913324 := by
    simpa [prefixWord, tailWord_2913324, baseEnd_2913324] using wordTrace_append hprefix tailTrace_2913324
  have hstable : (prefixWord ++ tailWord_2913324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913324).length < 2 ^ (prefixWord ++ tailWord_2913324).sum := by decide
  have hdescent : baseEnd_2913324 < baseStart_2913324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913326 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2913326 : Nat := 118140960795 + 2913326 * 2 ^ 59
def prefixEnd_2913326 : Nat := 4983230072969 + 3 ^ 40 * 2913326 * 2
def baseEnd_2913326 : Nat := 997291027493715888217909

theorem tailTrace_2913326 : CollatzResearch.WordTrace tailWord_2913326 prefixEnd_2913326 997291027493715888217909 := by
  unfold tailWord_2913326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282216080440616664176979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70838485762349955542277221 13282216080440616664176979)
  ·
    refine ⟨19923324120660924996265469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13282216080440616664176979 19923324120660924996265469)
    ·
      refine ⟨7471246545247846873599551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19923324120660924996265469 7471246545247846873599551)
      ·
        refine ⟨11206869817871770310399327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471246545247846873599551 11206869817871770310399327)
        ·
          refine ⟨16810304726807655465598991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11206869817871770310399327 16810304726807655465598991)
          ·
            refine ⟨25215457090211483198398487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16810304726807655465598991 25215457090211483198398487)
            ·
              refine ⟨37823185635317224797597731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25215457090211483198398487 37823185635317224797597731)
              ·
                refine ⟨56734778452975837196396597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37823185635317224797597731 56734778452975837196396597)
                ·
                  refine ⟨5318885479966484737162181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56734778452975837196396597 5318885479966484737162181)
                  ·
                    refine ⟨997291027493715888217909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5318885479966484737162181 997291027493715888217909)
                    ·
                      rfl

theorem cell22_2913326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2913326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913326 prefixEnd_2913326 := by exact prefixLift 2913326
  have htrace : WordTrace (prefixWord ++ tailWord_2913326) baseStart_2913326 baseEnd_2913326 := by
    simpa [prefixWord, tailWord_2913326, baseEnd_2913326] using wordTrace_append hprefix tailTrace_2913326
  have hstable : (prefixWord ++ tailWord_2913326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913326).length < 2 ^ (prefixWord ++ tailWord_2913326).sum := by decide
  have hdescent : baseEnd_2913326 < baseStart_2913326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913341 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 6]
def baseStart_2913341 : Nat := 118140960795 + 2913341 * 2 ^ 59
def prefixEnd_2913341 : Nat := 4983230072969 + 3 ^ 40 * 2913341 * 2
def baseEnd_2913341 : Nat := 332432054100086949697621

theorem tailTrace_2913341 : CollatzResearch.WordTrace tailWord_2913341 prefixEnd_2913341 332432054100086949697621 := by
  unfold tailWord_2913341
  simp only [CollatzResearch.WordTrace]
  refine ⟨106258275738470590875211877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70838850492313727250141251 106258275738470590875211877)
  ·
    refine ⟨19923426700963235789102227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106258275738470590875211877 19923426700963235789102227)
    ·
      refine ⟨29885140051444853683653341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19923426700963235789102227 29885140051444853683653341)
      ·
        refine ⟨11206927519291820131370003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29885140051444853683653341 11206927519291820131370003)
        ·
          refine ⟨16810391278937730197055005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11206927519291820131370003 16810391278937730197055005)
          ·
            refine ⟨6303896729601648823895627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16810391278937730197055005 6303896729601648823895627)
            ·
              refine ⟨9455845094402473235843441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303896729601648823895627 9455845094402473235843441)
              ·
                refine ⟨7091883820801854926882581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9455845094402473235843441 7091883820801854926882581)
                ·
                  refine ⟨332432054100086949697621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7091883820801854926882581 332432054100086949697621)
                  ·
                    rfl

theorem cell22_2913341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_2913341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913341 prefixEnd_2913341 := by exact prefixLift 2913341
  have htrace : WordTrace (prefixWord ++ tailWord_2913341) baseStart_2913341 baseEnd_2913341 := by
    simpa [prefixWord, tailWord_2913341, baseEnd_2913341] using wordTrace_append hprefix tailTrace_2913341
  have hstable : (prefixWord ++ tailWord_2913341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913341).length < 2 ^ (prefixWord ++ tailWord_2913341).sum := by decide
  have hdescent : baseEnd_2913341 < baseStart_2913341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913356 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_2913356 : Nat := 118140960795 + 2913356 * 2 ^ 59
def prefixEnd_2913356 : Nat := 4983230072969 + 3 ^ 40 * 2913356 * 2
def baseEnd_2913356 : Nat := 997301297106805809967817

theorem tailTrace_2913356 : CollatzResearch.WordTrace tailWord_2913356 prefixEnd_2913356 997301297106805809967817 := by
  unfold tailWord_2913356
  simp only [CollatzResearch.WordTrace]
  refine ⟨53129411416708124218503961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70839215222277498958005281 53129411416708124218503961)
  ·
    refine ⟨39847058562531093163877971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53129411416708124218503961 39847058562531093163877971)
    ·
      refine ⟨59770587843796639745816957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39847058562531093163877971 59770587843796639745816957)
      ·
        refine ⟨22413970441423739904681359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59770587843796639745816957 22413970441423739904681359)
        ·
          refine ⟨33620955662135609857022039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22413970441423739904681359 33620955662135609857022039)
          ·
            refine ⟨50431433493203414785533059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33620955662135609857022039 50431433493203414785533059)
            ·
              refine ⟨75647150239805122178299589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50431433493203414785533059 75647150239805122178299589)
              ·
                refine ⟨14183840669963460408431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75647150239805122178299589 14183840669963460408431173)
                ·
                  refine ⟨2659470125618148826580845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14183840669963460408431173 2659470125618148826580845)
                  ·
                    refine ⟨997301297106805809967817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659470125618148826580845 997301297106805809967817)
                    ·
                      rfl

theorem cell22_2913356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_2913356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913356 prefixEnd_2913356 := by exact prefixLift 2913356
  have htrace : WordTrace (prefixWord ++ tailWord_2913356) baseStart_2913356 baseEnd_2913356 := by
    simpa [prefixWord, tailWord_2913356, baseEnd_2913356] using wordTrace_append hprefix tailTrace_2913356
  have hstable : (prefixWord ++ tailWord_2913356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913356).length < 2 ^ (prefixWord ++ tailWord_2913356).sum := by decide
  have hdescent : baseEnd_2913356 < baseStart_2913356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913358 : List Nat := [4, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_2913358 : Nat := 118140960795 + 2913358 * 2 ^ 59
def prefixEnd_2913358 : Nat := 4983230072969 + 3 ^ 40 * 2913358 * 2
def baseEnd_2913358 : Nat := 332433993915892823805937

theorem tailTrace_2913358 : CollatzResearch.WordTrace tailWord_2913358 prefixEnd_2913358 332433993915892823805937 := by
  unfold tailWord_2913358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282361972426125347322591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70839263852939335185720485 13282361972426125347322591)
  ·
    refine ⟨19923542958639188020983887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13282361972426125347322591 19923542958639188020983887)
    ·
      refine ⟨29885314437958782031475831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19923542958639188020983887 29885314437958782031475831)
      ·
        refine ⟨44827971656938173047213747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29885314437958782031475831 44827971656938173047213747)
        ·
          refine ⟨67241957485407259570820621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44827971656938173047213747 67241957485407259570820621)
          ·
            refine ⟨25215734057027722339057733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67241957485407259570820621 25215734057027722339057733)
            ·
              refine ⟨4727950135692697938573325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25215734057027722339057733 4727950135692697938573325)
              ·
                refine ⟨1772981300884761726964997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4727950135692697938573325 1772981300884761726964997)
                ·
                  refine ⟨332433993915892823805937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772981300884761726964997 332433993915892823805937)
                  ·
                    rfl

theorem cell22_2913358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_2913358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913358 prefixEnd_2913358 := by exact prefixLift 2913358
  have htrace : WordTrace (prefixWord ++ tailWord_2913358) baseStart_2913358 baseEnd_2913358 := by
    simpa [prefixWord, tailWord_2913358, baseEnd_2913358] using wordTrace_append hprefix tailTrace_2913358
  have hstable : (prefixWord ++ tailWord_2913358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913358).length < 2 ^ (prefixWord ++ tailWord_2913358).sum := by decide
  have hdescent : baseEnd_2913358 < baseStart_2913358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913431 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 7]
def baseStart_2913431 : Nat := 118140960795 + 2913431 * 2 ^ 59
def prefixEnd_2913431 : Nat := 4983230072969 + 3 ^ 40 * 2913431 * 2
def baseEnd_2913431 : Nat := 332442323713176871447529

theorem tailTrace_2913431 : CollatzResearch.WordTrace tailWord_2913431 prefixEnd_2913431 332442323713176871447529 := by
  unfold tailWord_2913431
  simp only [CollatzResearch.WordTrace]
  refine ⟨106261558308144536245988147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70841038872096357497325431 106261558308144536245988147)
  ·
    refine ⟨159392337462216804368982221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106261558308144536245988147 159392337462216804368982221)
    ·
      refine ⟨59772126548331301638368333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159392337462216804368982221 59772126548331301638368333)
      ·
        refine ⟨22414547455624238114388125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59772126548331301638368333 22414547455624238114388125)
        ·
          refine ⟨8405455295859089292895547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22414547455624238114388125 8405455295859089292895547)
          ·
            refine ⟨12608182943788633939343321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8405455295859089292895547 12608182943788633939343321)
            ·
              refine ⟨9456137207841475454507491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12608182943788633939343321 9456137207841475454507491)
              ·
                refine ⟨14184205811762213181761237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456137207841475454507491 14184205811762213181761237)
                ·
                  refine ⟨332442323713176871447529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14184205811762213181761237 332442323713176871447529)
                  ·
                    rfl

theorem cell22_2913431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_2913431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913431 prefixEnd_2913431 := by exact prefixLift 2913431
  have htrace : WordTrace (prefixWord ++ tailWord_2913431) baseStart_2913431 baseEnd_2913431 := by
    simpa [prefixWord, tailWord_2913431, baseEnd_2913431] using wordTrace_append hprefix tailTrace_2913431
  have hstable : (prefixWord ++ tailWord_2913431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913431).length < 2 ^ (prefixWord ++ tailWord_2913431).sum := by decide
  have hdescent : baseEnd_2913431 < baseStart_2913431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913486 : List Nat := [4, 1, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_2913486 : Nat := 118140960795 + 2913486 * 2 ^ 59
def prefixEnd_2913486 : Nat := 4983230072969 + 3 ^ 40 * 2913486 * 2
def baseEnd_2913486 : Nat := 997345798763528804217419

theorem tailTrace_2913486 : CollatzResearch.WordTrace tailWord_2913486 prefixEnd_2913486 997345798763528804217419 := by
  unfold tailWord_2913486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13282945540368160079905039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70842376215296853759493541 13282945540368160079905039)
  ·
    refine ⟨19924418310552240119857559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13282945540368160079905039 19924418310552240119857559)
    ·
      refine ⟨29886627465828360179786339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19924418310552240119857559 29886627465828360179786339)
      ·
        refine ⟨44829941198742540269679509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29886627465828360179786339 44829941198742540269679509)
        ·
          refine ⟨2101403493691056575141227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44829941198742540269679509 2101403493691056575141227)
          ·
            refine ⟨3152105240536584862711841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101403493691056575141227 3152105240536584862711841)
            ·
              refine ⟨2364078930402438647033881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3152105240536584862711841 2364078930402438647033881)
              ·
                refine ⟨1773059197801828985275411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364078930402438647033881 1773059197801828985275411)
                ·
                  refine ⟨2659588796702743477913117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773059197801828985275411 2659588796702743477913117)
                  ·
                    refine ⟨997345798763528804217419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659588796702743477913117 997345798763528804217419)
                    ·
                      rfl

theorem cell22_2913486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_2913486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913486 prefixEnd_2913486 := by exact prefixLift 2913486
  have htrace : WordTrace (prefixWord ++ tailWord_2913486) baseStart_2913486 baseEnd_2913486 := by
    simpa [prefixWord, tailWord_2913486, baseEnd_2913486] using wordTrace_append hprefix tailTrace_2913486
  have hstable : (prefixWord ++ tailWord_2913486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913486).length < 2 ^ (prefixWord ++ tailWord_2913486).sum := by decide
  have hdescent : baseEnd_2913486 < baseStart_2913486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913523 : List Nat := [1, 1, 1, 2, 2, 5, 3, 1, 2, 4]
def baseStart_2913523 : Nat := 118140960795 + 2913523 * 2 ^ 59
def prefixEnd_2913523 : Nat := 4983230072969 + 3 ^ 40 * 2913523 * 2
def baseEnd_2913523 : Nat := 997358464619673041042305

theorem tailTrace_2913523 : CollatzResearch.WordTrace tailWord_2913523 prefixEnd_2913523 997358464619673041042305 := by
  unfold tailWord_2913523
  simp only [CollatzResearch.WordTrace]
  refine ⟨106264913823811235958337223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70843275882540823972224815 106264913823811235958337223)
  ·
    refine ⟨159397370735716853937505835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106264913823811235958337223 159397370735716853937505835)
    ·
      refine ⟨239096056103575280906258753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159397370735716853937505835 239096056103575280906258753)
      ·
        refine ⟨179322042077681460679694065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239096056103575280906258753 179322042077681460679694065)
        ·
          refine ⟨134491531558261095509770549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179322042077681460679694065 134491531558261095509770549)
          ·
            refine ⟨12608581083586977704040989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134491531558261095509770549 12608581083586977704040989)
            ·
              refine ⟨4728217906345116639015371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12608581083586977704040989 4728217906345116639015371)
              ·
                refine ⟨7092326859517674958523057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728217906345116639015371 7092326859517674958523057)
                ·
                  refine ⟨5319245144638256218892293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7092326859517674958523057 5319245144638256218892293)
                  ·
                    refine ⟨997358464619673041042305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5319245144638256218892293 997358464619673041042305)
                    ·
                      rfl

theorem cell22_2913523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_2913523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913523 prefixEnd_2913523 := by exact prefixLift 2913523
  have htrace : WordTrace (prefixWord ++ tailWord_2913523) baseStart_2913523 baseEnd_2913523 := by
    simpa [prefixWord, tailWord_2913523, baseEnd_2913523] using wordTrace_append hprefix tailTrace_2913523
  have hstable : (prefixWord ++ tailWord_2913523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913523).length < 2 ^ (prefixWord ++ tailWord_2913523).sum := by decide
  have hdescent : baseEnd_2913523 < baseStart_2913523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913587 : List Nat := [1, 1, 1, 2, 5, 2, 3, 3, 1, 3]
def baseStart_2913587 : Nat := 118140960795 + 2913587 * 2 ^ 59
def prefixEnd_2913587 : Nat := 4983230072969 + 3 ^ 40 * 2913587 * 2
def baseEnd_2913587 : Nat := 997380373127598207442109

theorem tailTrace_2913587 : CollatzResearch.WordTrace tailWord_2913587 prefixEnd_2913587 997380373127598207442109 := by
  unfold tailWord_2913587
  simp only [CollatzResearch.WordTrace]
  refine ⟨106267248095579374888667015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70844832063719583259111343 106267248095579374888667015)
  ·
    refine ⟨159400872143369062333000523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106267248095579374888667015 159400872143369062333000523)
    ·
      refine ⟨239101308215053593499500785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159400872143369062333000523 239101308215053593499500785)
      ·
        refine ⟨179325981161290195124625589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239101308215053593499500785 179325981161290195124625589)
        ·
          refine ⟨16811810733870955792933649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179325981161290195124625589 16811810733870955792933649)
          ·
            refine ⟨12608858050403216844700237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16811810733870955792933649 12608858050403216844700237)
            ·
              refine ⟨4728321768901206316762589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12608858050403216844700237 4728321768901206316762589)
              ·
                refine ⟨1773120663337952368785971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4728321768901206316762589 1773120663337952368785971)
                ·
                  refine ⟨2659680995006928553178957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773120663337952368785971 2659680995006928553178957)
                  ·
                    refine ⟨997380373127598207442109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659680995006928553178957 997380373127598207442109)
                    ·
                      rfl

theorem cell22_2913587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 3, 1, 3].length) (baseStart_2913587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913587 prefixEnd_2913587 := by exact prefixLift 2913587
  have htrace : WordTrace (prefixWord ++ tailWord_2913587) baseStart_2913587 baseEnd_2913587 := by
    simpa [prefixWord, tailWord_2913587, baseEnd_2913587] using wordTrace_append hprefix tailTrace_2913587
  have hstable : (prefixWord ++ tailWord_2913587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913587).length < 2 ^ (prefixWord ++ tailWord_2913587).sum := by decide
  have hdescent : baseEnd_2913587 < baseStart_2913587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913604 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2913604 : Nat := 118140960795 + 2913604 * 2 ^ 59
def prefixEnd_2913604 : Nat := 4983230072969 + 3 ^ 40 * 2913604 * 2
def baseEnd_2913604 : Nat := 997386192575015829767057

theorem tailTrace_2913604 : CollatzResearch.WordTrace tailWord_2913604 prefixEnd_2913604 997386192575015829767057 := by
  unfold tailWord_2913604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53133934068258893396017933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70845245424345191194690577 53133934068258893396017933)
  ·
    refine ⟨19925225275597085023506725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53133934068258893396017933 19925225275597085023506725)
    ·
      refine ⟨3735979739174453441907511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19925225275597085023506725 3735979739174453441907511)
      ·
        refine ⟨5603969608761680162861267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735979739174453441907511 5603969608761680162861267)
        ·
          refine ⟨8405954413142520244291901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603969608761680162861267 8405954413142520244291901)
          ·
            refine ⟨3152232904928445091609463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8405954413142520244291901 3152232904928445091609463)
            ·
              refine ⟨4728349357392667637414195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152232904928445091609463 4728349357392667637414195)
              ·
                refine ⟨7092524036089001456121293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4728349357392667637414195 7092524036089001456121293)
                ·
                  refine ⟨2659696513533375546045485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7092524036089001456121293 2659696513533375546045485)
                  ·
                    refine ⟨997386192575015829767057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659696513533375546045485 997386192575015829767057)
                    ·
                      rfl

theorem cell22_2913604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2913604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913604 prefixEnd_2913604 := by exact prefixLift 2913604
  have htrace : WordTrace (prefixWord ++ tailWord_2913604) baseStart_2913604 baseEnd_2913604 := by
    simpa [prefixWord, tailWord_2913604, baseEnd_2913604] using wordTrace_append hprefix tailTrace_2913604
  have hstable : (prefixWord ++ tailWord_2913604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913604).length < 2 ^ (prefixWord ++ tailWord_2913604).sum := by decide
  have hdescent : baseEnd_2913604 < baseStart_2913604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913690 : List Nat := [3, 1, 1, 4, 1, 1, 5, 6]
def baseStart_2913690 : Nat := 118140960795 + 2913690 * 2 ^ 59
def prefixEnd_2913690 : Nat := 4983230072969 + 3 ^ 40 * 2913690 * 2
def baseEnd_2913690 : Nat := 110823959125837808012977

theorem tailTrace_2913690 : CollatzResearch.WordTrace tailWord_2913690 prefixEnd_2913690 110823959125837808012977 := by
  unfold tailWord_2913690
  simp only [CollatzResearch.WordTrace]
  refine ⟨26567751203551555869916631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70847336542804148986444349 26567751203551555869916631)
  ·
    refine ⟨39851626805327333804874947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26567751203551555869916631 39851626805327333804874947)
    ·
      refine ⟨59777440207991000707312421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39851626805327333804874947 59777440207991000707312421)
      ·
        refine ⟨11208270038998312632621079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59777440207991000707312421 11208270038998312632621079)
        ·
          refine ⟨16812405058497468948931619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11208270038998312632621079 16812405058497468948931619)
          ·
            refine ⟨25218607587746203423397429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16812405058497468948931619 25218607587746203423397429)
            ·
              refine ⟨2364244461351206570943509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25218607587746203423397429 2364244461351206570943509)
              ·
                refine ⟨110823959125837808012977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2364244461351206570943509 110823959125837808012977)
                ·
                  rfl

theorem cell22_2913690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_2913690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913690 prefixEnd_2913690 := by exact prefixLift 2913690
  have htrace : WordTrace (prefixWord ++ tailWord_2913690) baseStart_2913690 baseEnd_2913690 := by
    simpa [prefixWord, tailWord_2913690, baseEnd_2913690] using wordTrace_append hprefix tailTrace_2913690
  have hstable : (prefixWord ++ tailWord_2913690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913690).length < 2 ^ (prefixWord ++ tailWord_2913690).sum := by decide
  have hdescent : baseEnd_2913690 < baseStart_2913690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913692 : List Nat := [2, 2, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_2913692 : Nat := 118140960795 + 2913692 * 2 ^ 59
def prefixEnd_2913692 : Nat := 4983230072969 + 3 ^ 40 * 2913692 * 2
def baseEnd_2913692 : Nat := 997416316773412933566787

theorem tailTrace_2913692 : CollatzResearch.WordTrace tailWord_2913692 prefixEnd_2913692 997416316773412933566787 := by
  unfold tailWord_2913692
  simp only [CollatzResearch.WordTrace]
  refine ⟨53135538880099488910619665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70847385173465985214159553 53135538880099488910619665)
  ·
    refine ⟨39851654160074616682964749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53135538880099488910619665 39851654160074616682964749)
    ·
      refine ⟨14944370310027981256111781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39851654160074616682964749 14944370310027981256111781)
      ·
        refine ⟨2802069433130246485520959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14944370310027981256111781 2802069433130246485520959)
        ·
          refine ⟨4203104149695369728281439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802069433130246485520959 4203104149695369728281439)
          ·
            refine ⟨6304656224543054592422159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203104149695369728281439 6304656224543054592422159)
            ·
              refine ⟨9456984336814581888633239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304656224543054592422159 9456984336814581888633239)
              ·
                refine ⟨14185476505221872832949859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456984336814581888633239 14185476505221872832949859)
                ·
                  refine ⟨21278214757832809249424789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14185476505221872832949859 21278214757832809249424789)
                  ·
                    refine ⟨997416316773412933566787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21278214757832809249424789 997416316773412933566787)
                    ·
                      rfl

theorem cell22_2913692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_2913692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913692 prefixEnd_2913692 := by exact prefixLift 2913692
  have htrace : WordTrace (prefixWord ++ tailWord_2913692) baseStart_2913692 baseEnd_2913692 := by
    simpa [prefixWord, tailWord_2913692, baseEnd_2913692] using wordTrace_append hprefix tailTrace_2913692
  have hstable : (prefixWord ++ tailWord_2913692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913692).length < 2 ^ (prefixWord ++ tailWord_2913692).sum := by decide
  have hdescent : baseEnd_2913692 < baseStart_2913692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913773 : List Nat := [1, 5, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_2913773 : Nat := 118140960795 + 2913773 * 2 ^ 59
def prefixEnd_2913773 : Nat := 4983230072969 + 3 ^ 40 * 2913773 * 2
def baseEnd_2913773 : Nat := 997444044728755722291539

theorem tailTrace_2913773 : CollatzResearch.WordTrace tailWord_2913773 prefixEnd_2913773 997444044728755722291539 := by
  unfold tailWord_2913773
  simp only [CollatzResearch.WordTrace]
  refine ⟨106274032072905528654937973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70849354715270352436625315 106274032072905528654937973)
  ·
    refine ⟨9963190506834893311400435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106274032072905528654937973 9963190506834893311400435)
    ·
      refine ⟨14944785760252339967100653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9963190506834893311400435 14944785760252339967100653)
      ·
        refine ⟨5604294660094627487662745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14944785760252339967100653 5604294660094627487662745)
        ·
          refine ⟨4203220995070970615747059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5604294660094627487662745 4203220995070970615747059)
          ·
            refine ⟨6304831492606455923620589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203220995070970615747059 6304831492606455923620589)
            ·
              refine ⟨2364311809727420971357721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6304831492606455923620589 2364311809727420971357721)
              ·
                refine ⟨1773233857295565728518291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364311809727420971357721 1773233857295565728518291)
                ·
                  refine ⟨2659850785943348592777437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773233857295565728518291 2659850785943348592777437)
                  ·
                    refine ⟨997444044728755722291539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659850785943348592777437 997444044728755722291539)
                    ·
                      rfl

theorem cell22_2913773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_2913773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913773 prefixEnd_2913773 := by exact prefixLift 2913773
  have htrace : WordTrace (prefixWord ++ tailWord_2913773) baseStart_2913773 baseEnd_2913773 := by
    simpa [prefixWord, tailWord_2913773, baseEnd_2913773] using wordTrace_append hprefix tailTrace_2913773
  have hstable : (prefixWord ++ tailWord_2913773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913773).length < 2 ^ (prefixWord ++ tailWord_2913773).sum := by decide
  have hdescent : baseEnd_2913773 < baseStart_2913773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913795 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 6, 3]
def baseStart_2913795 : Nat := 118140960795 + 2913795 * 2 ^ 59
def prefixEnd_2913795 : Nat := 4983230072969 + 3 ^ 40 * 2913795 * 2
def baseEnd_2913795 : Nat := 997451575778354998241471

theorem tailTrace_2913795 : CollatzResearch.WordTrace tailWord_2913795 prefixEnd_2913795 997451575778354998241471 := by
  unfold tailWord_2913795
  simp only [CollatzResearch.WordTrace]
  refine ⟨106274834478825826412238839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70849889652550550941492559 106274834478825826412238839)
  ·
    refine ⟨159412251718238739618358259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106274834478825826412238839 159412251718238739618358259)
    ·
      refine ⟨239118377577358109427537389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159412251718238739618358259 239118377577358109427537389)
      ·
        refine ⟨89669391591509291035326521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239118377577358109427537389 89669391591509291035326521)
        ·
          refine ⟨67252043693631968276494891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89669391591509291035326521 67252043693631968276494891)
          ·
            refine ⟨100878065540447952414742337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67252043693631968276494891 100878065540447952414742337)
            ·
              refine ⟨75658549155335964311056753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100878065540447952414742337 75658549155335964311056753)
              ·
                refine ⟨56743911866501973233292565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75658549155335964311056753 56743911866501973233292565)
                ·
                  refine ⟨2659870868742279995310589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56743911866501973233292565 2659870868742279995310589)
                  ·
                    refine ⟨997451575778354998241471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2659870868742279995310589 997451575778354998241471)
                    ·
                      rfl

theorem cell22_2913795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 6, 3].length) (baseStart_2913795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913795 prefixEnd_2913795 := by exact prefixLift 2913795
  have htrace : WordTrace (prefixWord ++ tailWord_2913795) baseStart_2913795 baseEnd_2913795 := by
    simpa [prefixWord, tailWord_2913795, baseEnd_2913795] using wordTrace_append hprefix tailTrace_2913795
  have hstable : (prefixWord ++ tailWord_2913795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913795).length < 2 ^ (prefixWord ++ tailWord_2913795).sum := by decide
  have hdescent : baseEnd_2913795 < baseStart_2913795 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913799 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2913799 : Nat := 118140960795 + 2913799 * 2 ^ 59
def prefixEnd_2913799 : Nat := 4983230072969 + 3 ^ 40 * 2913799 * 2
def baseEnd_2913799 : Nat := 997452945060100321141459

theorem tailTrace_2913799 : CollatzResearch.WordTrace tailWord_2913799 prefixEnd_2913799 997452945060100321141459 := by
  unfold tailWord_2913799
  simp only [CollatzResearch.WordTrace]
  refine ⟨106274980370811335095384451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70849986913874223396922967 106274980370811335095384451)
  ·
    refine ⟨159412470556217002643076677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106274980370811335095384451 159412470556217002643076677)
    ·
      refine ⟨29889838229290687995576877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 159412470556217002643076677 29889838229290687995576877)
      ·
        refine ⟨11208689335984007998341329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29889838229290687995576877 11208689335984007998341329)
        ·
          refine ⟨8406517001988005998755997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11208689335984007998341329 8406517001988005998755997)
          ·
            refine ⟨3152443875745502249533499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8406517001988005998755997 3152443875745502249533499)
            ·
              refine ⟨4728665813618253374300249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152443875745502249533499 4728665813618253374300249)
              ·
                refine ⟨3546499360213690030725187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728665813618253374300249 3546499360213690030725187)
                ·
                  refine ⟨5319749040320535046087781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546499360213690030725187 5319749040320535046087781)
                  ·
                    refine ⟨997452945060100321141459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5319749040320535046087781 997452945060100321141459)
                    ·
                      rfl

theorem cell22_2913799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2913799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913799 prefixEnd_2913799 := by exact prefixLift 2913799
  have htrace : WordTrace (prefixWord ++ tailWord_2913799) baseStart_2913799 baseEnd_2913799 := by
    simpa [prefixWord, tailWord_2913799, baseEnd_2913799] using wordTrace_append hprefix tailTrace_2913799
  have hstable : (prefixWord ++ tailWord_2913799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913799).length < 2 ^ (prefixWord ++ tailWord_2913799).sum := by decide
  have hdescent : baseEnd_2913799 < baseStart_2913799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913870 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_2913870 : Nat := 118140960795 + 2913870 * 2 ^ 59
def prefixEnd_2913870 : Nat := 4983230072969 + 3 ^ 40 * 2913870 * 2
def baseEnd_2913870 : Nat := 332492416603693267538747

theorem tailTrace_2913870 : CollatzResearch.WordTrace tailWord_2913870 prefixEnd_2913870 332492416603693267538747 := by
  unfold tailWord_2913870
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284696244194264277652383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70851713302369409480812709 13284696244194264277652383)
  ·
    refine ⟨19927044366291396416478575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13284696244194264277652383 19927044366291396416478575)
    ·
      refine ⟨29890566549437094624717863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19927044366291396416478575 29890566549437094624717863)
      ·
        refine ⟨44835849824155641937076795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29890566549437094624717863 44835849824155641937076795)
        ·
          refine ⟨67253774736233462905615193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44835849824155641937076795 67253774736233462905615193)
          ·
            refine ⟨50440331052175097179211395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67253774736233462905615193 50440331052175097179211395)
            ·
              refine ⟨75660496578262645768817093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50440331052175097179211395 75660496578262645768817093)
              ·
                refine ⟨14186343108424246081653205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75660496578262645768817093 14186343108424246081653205)
                ·
                  refine ⟨332492416603693267538747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14186343108424246081653205 332492416603693267538747)
                  ·
                    rfl

theorem cell22_2913870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_2913870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913870 prefixEnd_2913870 := by exact prefixLift 2913870
  have htrace : WordTrace (prefixWord ++ tailWord_2913870) baseStart_2913870 baseEnd_2913870 := by
    simpa [prefixWord, tailWord_2913870, baseEnd_2913870] using wordTrace_append hprefix tailTrace_2913870
  have hstable : (prefixWord ++ tailWord_2913870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913870).length < 2 ^ (prefixWord ++ tailWord_2913870).sum := by decide
  have hdescent : baseEnd_2913870 < baseStart_2913870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913904 : List Nat := [2, 1, 1, 1, 6, 2, 3, 1, 5]
def baseStart_2913904 : Nat := 118140960795 + 2913904 * 2 ^ 59
def prefixEnd_2913904 : Nat := 4983230072969 + 3 ^ 40 * 2913904 * 2
def baseEnd_2913904 : Nat := 332496296235305015755379

theorem tailTrace_2913904 : CollatzResearch.WordTrace tailWord_2913904 prefixEnd_2913904 332496296235305015755379 := by
  unfold tailWord_2913904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53139405017715469013978383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70852540023620625351971177 53139405017715469013978383)
  ·
    refine ⟨79709107526573203520967575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53139405017715469013978383 79709107526573203520967575)
    ·
      refine ⟨119563661289859805281451363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79709107526573203520967575 119563661289859805281451363)
      ·
        refine ⟨179345491934789707922177045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119563661289859805281451363 179345491934789707922177045)
        ·
          refine ⟨8406819934443267558852049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179345491934789707922177045 8406819934443267558852049)
          ·
            refine ⟨6305114950832450669139037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8406819934443267558852049 6305114950832450669139037)
            ·
              refine ⟨2364418106562169000927139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6305114950832450669139037 2364418106562169000927139)
              ·
                refine ⟨3546627159843253501390709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364418106562169000927139 3546627159843253501390709)
                ·
                  refine ⟨332496296235305015755379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3546627159843253501390709 332496296235305015755379)
                  ·
                    rfl

theorem cell22_2913904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 5].length) (baseStart_2913904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913904 prefixEnd_2913904 := by exact prefixLift 2913904
  have htrace : WordTrace (prefixWord ++ tailWord_2913904) baseStart_2913904 baseEnd_2913904 := by
    simpa [prefixWord, tailWord_2913904, baseEnd_2913904] using wordTrace_append hprefix tailTrace_2913904
  have hstable : (prefixWord ++ tailWord_2913904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913904).length < 2 ^ (prefixWord ++ tailWord_2913904).sum := by decide
  have hdescent : baseEnd_2913904 < baseStart_2913904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913915 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 6]
def baseStart_2913915 : Nat := 118140960795 + 2913915 * 2 ^ 59
def prefixEnd_2913915 : Nat := 4983230072969 + 3 ^ 40 * 2913915 * 2
def baseEnd_2913915 : Nat := 332497551410238228413701

theorem tailTrace_2913915 : CollatzResearch.WordTrace tailWord_2913915 prefixEnd_2913915 332497551410238228413701 := by
  unfold tailWord_2913915
  simp only [CollatzResearch.WordTrace]
  refine ⟨106279211238391086906607199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70852807492260724604404799 106279211238391086906607199)
  ·
    refine ⟨159418816857586630359910799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106279211238391086906607199 159418816857586630359910799)
    ·
      refine ⟨239128225286379945539866199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159418816857586630359910799 239128225286379945539866199)
      ·
        refine ⟨358692337929569918309799299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239128225286379945539866199 358692337929569918309799299)
        ·
          refine ⟨538038506894354877464698949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358692337929569918309799299 538038506894354877464698949)
          ·
            refine ⟨100882220042691539524631053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 538038506894354877464698949 100882220042691539524631053)
            ·
              refine ⟨37830832516009327321736645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100882220042691539524631053 37830832516009327321736645)
              ·
                refine ⟨7093281096751748872825621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37830832516009327321736645 7093281096751748872825621)
                ·
                  refine ⟨332497551410238228413701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7093281096751748872825621 332497551410238228413701)
                  ·
                    rfl

theorem cell22_2913915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_2913915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913915 prefixEnd_2913915 := by exact prefixLift 2913915
  have htrace : WordTrace (prefixWord ++ tailWord_2913915) baseStart_2913915 baseEnd_2913915 := by
    simpa [prefixWord, tailWord_2913915, baseEnd_2913915] using wordTrace_append hprefix tailTrace_2913915
  have hstable : (prefixWord ++ tailWord_2913915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913915).length < 2 ^ (prefixWord ++ tailWord_2913915).sum := by decide
  have hdescent : baseEnd_2913915 < baseStart_2913915 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913934 : List Nat := [4, 1, 1, 3, 1, 2, 2, 3, 1, 4]
def baseStart_2913934 : Nat := 118140960795 + 2913934 * 2 ^ 59
def prefixEnd_2913934 : Nat := 4983230072969 + 3 ^ 40 * 2913934 * 2
def baseEnd_2913934 : Nat := 997499158319004969016045

theorem tailTrace_2913934 : CollatzResearch.WordTrace tailWord_2913934 prefixEnd_2913934 997499158319004969016045 := by
  unfold tailWord_2913934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13284988028165281643943607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70853269483548168767699237 13284988028165281643943607)
  ·
    refine ⟨19927482042247922465915411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13284988028165281643943607 19927482042247922465915411)
    ·
      refine ⟨29891223063371883698873117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19927482042247922465915411 29891223063371883698873117)
      ·
        refine ⟨11209208648764456387077419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29891223063371883698873117 11209208648764456387077419)
        ·
          refine ⟨16813812973146684580616129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11209208648764456387077419 16813812973146684580616129)
          ·
            refine ⟨12610359729860013435462097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16813812973146684580616129 12610359729860013435462097)
            ·
              refine ⟨9457769797395010076596573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12610359729860013435462097 9457769797395010076596573)
              ·
                refine ⟨3546663674023128778723715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9457769797395010076596573 3546663674023128778723715)
                ·
                  refine ⟨5319995511034693168085573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546663674023128778723715 5319995511034693168085573)
                  ·
                    refine ⟨997499158319004969016045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5319995511034693168085573 997499158319004969016045)
                    ·
                      rfl

theorem cell22_2913934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_2913934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913934 prefixEnd_2913934 := by exact prefixLift 2913934
  have htrace : WordTrace (prefixWord ++ tailWord_2913934) baseStart_2913934 baseEnd_2913934 := by
    simpa [prefixWord, tailWord_2913934, baseEnd_2913934] using wordTrace_append hprefix tailTrace_2913934
  have hstable : (prefixWord ++ tailWord_2913934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913934).length < 2 ^ (prefixWord ++ tailWord_2913934).sum := by decide
  have hdescent : baseEnd_2913934 < baseStart_2913934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2913945 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_2913945 : Nat := 118140960795 + 2913945 * 2 ^ 59
def prefixEnd_2913945 : Nat := 4983230072969 + 3 ^ 40 * 2913945 * 2
def baseEnd_2913945 : Nat := 997502923843804606991011

theorem tailTrace_2913945 : CollatzResearch.WordTrace tailWord_2913945 prefixEnd_2913945 997502923843804606991011 := by
  unfold tailWord_2913945
  simp only [CollatzResearch.WordTrace]
  refine ⟨106280305428282402030199289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70853536952188268020132859 106280305428282402030199289)
  ·
    refine ⟨79710229071211801522649467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106280305428282402030199289 79710229071211801522649467)
    ·
      refine ⟨119565343606817702283974201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79710229071211801522649467 119565343606817702283974201)
      ·
        refine ⟨89674007705113276712980651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119565343606817702283974201 89674007705113276712980651)
        ·
          refine ⟨134511011557669915069470977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89674007705113276712980651 134511011557669915069470977)
          ·
            refine ⟨100883258668252436302103233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134511011557669915069470977 100883258668252436302103233)
            ·
              refine ⟨75662444001189327226577425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100883258668252436302103233 75662444001189327226577425)
              ·
                refine ⟨56746833000891995419933069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75662444001189327226577425 56746833000891995419933069)
                ·
                  refine ⟨21280062375334498282474901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56746833000891995419933069 21280062375334498282474901)
                  ·
                    refine ⟨997502923843804606991011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21280062375334498282474901 997502923843804606991011)
                    ·
                      rfl

theorem cell22_2913945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_2913945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2913945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2913945 prefixEnd_2913945 := by exact prefixLift 2913945
  have htrace : WordTrace (prefixWord ++ tailWord_2913945) baseStart_2913945 baseEnd_2913945 := by
    simpa [prefixWord, tailWord_2913945, baseEnd_2913945] using wordTrace_append hprefix tailTrace_2913945
  have hstable : (prefixWord ++ tailWord_2913945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2913945).length < 2 ^ (prefixWord ++ tailWord_2913945).sum := by decide
  have hdescent : baseEnd_2913945 < baseStart_2913945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2913945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914084 : List Nat := [2, 3, 1, 3, 2, 1, 2, 2, 6]
def baseStart_2914084 : Nat := 118140960795 + 2914084 * 2 ^ 59
def prefixEnd_2914084 : Nat := 4983230072969 + 3 ^ 40 * 2914084 * 2
def baseEnd_2914084 : Nat := 332516835461484859255195

theorem tailTrace_2914084 : CollatzResearch.WordTrace tailWord_2914084 prefixEnd_2914084 332516835461484859255195 := by
  unfold tailWord_2914084
  simp only [CollatzResearch.WordTrace]
  refine ⟨53142687587389414384754653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70856916783185885846339537 53142687587389414384754653)
  ·
    refine ⟨19928507845271030394282995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53142687587389414384754653 19928507845271030394282995)
    ·
      refine ⟨29892761767906545591424493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19928507845271030394282995 29892761767906545591424493)
      ·
        refine ⟨11209785662964954596784185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29892761767906545591424493 11209785662964954596784185)
        ·
          refine ⟨8407339247223715947588139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11209785662964954596784185 8407339247223715947588139)
          ·
            refine ⟨12611008870835573921382209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8407339247223715947588139 12611008870835573921382209)
            ·
              refine ⟨9458256653126680441036657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12611008870835573921382209 9458256653126680441036657)
              ·
                refine ⟨7093692489845010330777493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9458256653126680441036657 7093692489845010330777493)
                ·
                  refine ⟨332516835461484859255195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7093692489845010330777493 332516835461484859255195)
                  ·
                    rfl

theorem cell22_2914084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_2914084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914084 prefixEnd_2914084 := by exact prefixLift 2914084
  have htrace : WordTrace (prefixWord ++ tailWord_2914084) baseStart_2914084 baseEnd_2914084 := by
    simpa [prefixWord, tailWord_2914084, baseEnd_2914084] using wordTrace_append hprefix tailTrace_2914084
  have hstable : (prefixWord ++ tailWord_2914084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914084).length < 2 ^ (prefixWord ++ tailWord_2914084).sum := by decide
  have hdescent : baseEnd_2914084 < baseStart_2914084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914118 : List Nat := [6, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2914118 : Nat := 118140960795 + 2914118 * 2 ^ 59
def prefixEnd_2914118 : Nat := 4983230072969 + 3 ^ 40 * 2914118 * 2
def baseEnd_2914118 : Nat := 332520715093096607471827

theorem tailTrace_2914118 : CollatzResearch.WordTrace tailWord_2914118 prefixEnd_2914118 332520715093096607471827 := by
  unfold tailWord_2914118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321456726770489143007719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70857743504437101717498005 3321456726770489143007719)
  ·
    refine ⟨4982185090155733714511579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3321456726770489143007719 4982185090155733714511579)
    ·
      refine ⟨7473277635233600571767369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982185090155733714511579 7473277635233600571767369)
      ·
        refine ⟨5604958226425200428825527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7473277635233600571767369 5604958226425200428825527)
        ·
          refine ⟨8407437339637800643238291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604958226425200428825527 8407437339637800643238291)
          ·
            refine ⟨12611156009456700964857437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8407437339637800643238291 12611156009456700964857437)
            ·
              refine ⟨4729183503546262861821539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12611156009456700964857437 4729183503546262861821539)
              ·
                refine ⟨7093775255319394292732309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729183503546262861821539 7093775255319394292732309)
                ·
                  refine ⟨332520715093096607471827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7093775255319394292732309 332520715093096607471827)
                  ·
                    rfl

theorem cell22_2914118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2914118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914118 prefixEnd_2914118 := by exact prefixLift 2914118
  have htrace : WordTrace (prefixWord ++ tailWord_2914118) baseStart_2914118 baseEnd_2914118 := by
    simpa [prefixWord, tailWord_2914118, baseEnd_2914118] using wordTrace_append hprefix tailTrace_2914118
  have hstable : (prefixWord ++ tailWord_2914118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914118).length < 2 ^ (prefixWord ++ tailWord_2914118).sum := by decide
  have hdescent : baseEnd_2914118 < baseStart_2914118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914129 : List Nat := [1, 2, 2, 1, 5, 2, 2, 7]
def baseStart_2914129 : Nat := 118140960795 + 2914129 * 2 ^ 59
def prefixEnd_2914129 : Nat := 4983230072969 + 3 ^ 40 * 2914129 * 2
def baseEnd_2914129 : Nat := 110840656756009940043383

theorem tailTrace_2914129 : CollatzResearch.WordTrace tailWord_2914129 prefixEnd_2914129 110840656756009940043383 := by
  unfold tailWord_2914129
  simp only [CollatzResearch.WordTrace]
  refine ⟨106287016459615801454897441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70858010973077200969931627 106287016459615801454897441)
  ·
    refine ⟨79715262344711851091173081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106287016459615801454897441 79715262344711851091173081)
    ·
      refine ⟨59786446758533888318379811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79715262344711851091173081 59786446758533888318379811)
      ·
        refine ⟨89679670137800832477569717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59786446758533888318379811 89679670137800832477569717)
        ·
          refine ⟨8407469075418828044772161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89679670137800832477569717 8407469075418828044772161)
          ·
            refine ⟨6305601806564121033579121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8407469075418828044772161 6305601806564121033579121)
            ·
              refine ⟨4729201354923090775184341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305601806564121033579121 4729201354923090775184341)
              ·
                refine ⟨110840656756009940043383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4729201354923090775184341 110840656756009940043383)
                ·
                  rfl

theorem cell22_2914129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 7].length) (baseStart_2914129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914129 prefixEnd_2914129 := by exact prefixLift 2914129
  have htrace : WordTrace (prefixWord ++ tailWord_2914129) baseStart_2914129 baseEnd_2914129 := by
    simpa [prefixWord, tailWord_2914129, baseEnd_2914129] using wordTrace_append hprefix tailTrace_2914129
  have hstable : (prefixWord ++ tailWord_2914129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914129).length < 2 ^ (prefixWord ++ tailWord_2914129).sum := by decide
  have hdescent : baseEnd_2914129 < baseStart_2914129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914133 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 2, 3]
def baseStart_2914133 : Nat := 118140960795 + 2914133 * 2 ^ 59
def prefixEnd_2914133 : Nat := 4983230072969 + 3 ^ 40 * 2914133 * 2
def baseEnd_2914133 : Nat := 997567280085834783290435

theorem tailTrace_2914133 : CollatzResearch.WordTrace tailWord_2914133 prefixEnd_2914133 997567280085834783290435 := by
  unfold tailWord_2914133
  simp only [CollatzResearch.WordTrace]
  refine ⟨106287162351601310138043053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70858108234400873425362035 106287162351601310138043053)
  ·
    refine ⟨39857685881850491301766145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106287162351601310138043053 39857685881850491301766145)
    ·
      refine ⟨29893264411387868476324609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39857685881850491301766145 29893264411387868476324609)
      ·
        refine ⟨22419948308540901357243457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29893264411387868476324609 22419948308540901357243457)
        ·
          refine ⟨16814961231405676017932593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22419948308540901357243457 16814961231405676017932593)
          ·
            refine ⟨12611220923554257013449445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16814961231405676017932593 12611220923554257013449445)
            ·
              refine ⟨2364603923166423190021771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12611220923554257013449445 2364603923166423190021771)
              ·
                refine ⟨3546905884749634785032657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364603923166423190021771 3546905884749634785032657)
                ·
                  refine ⟨2660179413562226088774493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3546905884749634785032657 2660179413562226088774493)
                  ·
                    refine ⟨997567280085834783290435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660179413562226088774493 997567280085834783290435)
                    ·
                      rfl

theorem cell22_2914133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_2914133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914133 prefixEnd_2914133 := by exact prefixLift 2914133
  have htrace : WordTrace (prefixWord ++ tailWord_2914133) baseStart_2914133 baseEnd_2914133 := by
    simpa [prefixWord, tailWord_2914133, baseEnd_2914133] using wordTrace_append hprefix tailTrace_2914133
  have hstable : (prefixWord ++ tailWord_2914133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914133).length < 2 ^ (prefixWord ++ tailWord_2914133).sum := by decide
  have hdescent : baseEnd_2914133 < baseStart_2914133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914249 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_2914249 : Nat := 118140960795 + 2914249 * 2 ^ 59
def prefixEnd_2914249 : Nat := 4983230072969 + 3 ^ 40 * 2914249 * 2
def baseEnd_2914249 : Nat := 997606989256449147390079

theorem tailTrace_2914249 : CollatzResearch.WordTrace tailWord_2914249 prefixEnd_2914249 997606989256449147390079 := by
  unfold tailWord_2914249
  simp only [CollatzResearch.WordTrace]
  refine ⟨106291393219181061949265801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70860928812787374632843867 106291393219181061949265801)
  ·
    refine ⟨79718544914385796461949351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106291393219181061949265801 79718544914385796461949351)
    ·
      refine ⟨119577817371578694692924027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79718544914385796461949351 119577817371578694692924027)
      ·
        refine ⟨179366726057368042039386041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119577817371578694692924027 179366726057368042039386041)
        ·
          refine ⟨134525044543026031529539531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179366726057368042039386041 134525044543026031529539531)
          ·
            refine ⟨201787566814539047294309297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134525044543026031529539531 201787566814539047294309297)
            ·
              refine ⟨151340675110904285470731973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201787566814539047294309297 151340675110904285470731973)
              ·
                refine ⟨28376376583294553525762245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151340675110904285470731973 28376376583294553525762245)
                ·
                  refine ⟨5320570609367728786080421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28376376583294553525762245 5320570609367728786080421)
                  ·
                    refine ⟨997606989256449147390079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320570609367728786080421 997606989256449147390079)
                    ·
                      rfl

theorem cell22_2914249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_2914249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914249 prefixEnd_2914249 := by exact prefixLift 2914249
  have htrace : WordTrace (prefixWord ++ tailWord_2914249) baseStart_2914249 baseEnd_2914249 := by
    simpa [prefixWord, tailWord_2914249, baseEnd_2914249] using wordTrace_append hprefix tailTrace_2914249
  have hstable : (prefixWord ++ tailWord_2914249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914249).length < 2 ^ (prefixWord ++ tailWord_2914249).sum := by decide
  have hdescent : baseEnd_2914249 < baseStart_2914249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914264 : List Nat := [2, 1, 2, 2, 2, 2, 3, 8]
def baseStart_2914264 : Nat := 118140960795 + 2914264 * 2 ^ 59
def prefixEnd_2914264 : Nat := 4983230072969 + 3 ^ 40 * 2914264 * 2
def baseEnd_2914264 : Nat := 110845791562554900918337

theorem tailTrace_2914264 : CollatzResearch.WordTrace tailWord_2914264 prefixEnd_2914264 110845791562554900918337 := by
  unfold tailWord_2914264
  simp only [CollatzResearch.WordTrace]
  refine ⟨53145970157063359755530923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70861293542751146340707897 53145970157063359755530923)
  ·
    refine ⟨79718955235595039633296385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53145970157063359755530923 79718955235595039633296385)
    ·
      refine ⟨59789216426696279724972289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79718955235595039633296385 59789216426696279724972289)
      ·
        refine ⟨44841912320022209793729217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59789216426696279724972289 44841912320022209793729217)
        ·
          refine ⟨33631434240016657345296913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44841912320022209793729217 33631434240016657345296913)
          ·
            refine ⟨25223575680012493008972685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33631434240016657345296913 25223575680012493008972685)
            ·
              refine ⟨9458840880004684878364757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25223575680012493008972685 9458840880004684878364757)
              ·
                refine ⟨110845791562554900918337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9458840880004684878364757 110845791562554900918337)
                ·
                  rfl

theorem cell22_2914264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 8].length) (baseStart_2914264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914264 prefixEnd_2914264 := by exact prefixLift 2914264
  have htrace : WordTrace (prefixWord ++ tailWord_2914264) baseStart_2914264 baseEnd_2914264 := by
    simpa [prefixWord, tailWord_2914264, baseEnd_2914264] using wordTrace_append hprefix tailTrace_2914264
  have hstable : (prefixWord ++ tailWord_2914264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914264).length < 2 ^ (prefixWord ++ tailWord_2914264).sum := by decide
  have hdescent : baseEnd_2914264 < baseStart_2914264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914302 : List Nat := [4, 2, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2914302 : Nat := 118140960795 + 2914302 * 2 ^ 59
def prefixEnd_2914302 : Nat := 4983230072969 + 3 ^ 40 * 2914302 * 2
def baseEnd_2914302 : Nat := 997625132239574675814917

theorem tailTrace_2914302 : CollatzResearch.WordTrace tailWord_2914302 prefixEnd_2914302 997625132239574675814917 := by
  unfold tailWord_2914302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286665785998631500118145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70862217525326034667296773 13286665785998631500118145)
  ·
    refine ⟨9964999339498973625088609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13286665785998631500118145 9964999339498973625088609)
    ·
      refine ⟨7473749504624230218816457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9964999339498973625088609 7473749504624230218816457)
      ·
        refine ⟨5605312128468172664112343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7473749504624230218816457 5605312128468172664112343)
        ·
          refine ⟨8407968192702258996168515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605312128468172664112343 8407968192702258996168515)
          ·
            refine ⟨12611952289053388494252773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8407968192702258996168515 12611952289053388494252773)
            ·
              refine ⟨2364741054197510342672395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12611952289053388494252773 2364741054197510342672395)
              ·
                refine ⟨3547111581296265514008593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364741054197510342672395 3547111581296265514008593)
                ·
                  refine ⟨2660333685972199135506445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3547111581296265514008593 2660333685972199135506445)
                  ·
                    refine ⟨997625132239574675814917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660333685972199135506445 997625132239574675814917)
                    ·
                      rfl

theorem cell22_2914302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2914302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914302 prefixEnd_2914302 := by exact prefixLift 2914302
  have htrace : WordTrace (prefixWord ++ tailWord_2914302) baseStart_2914302 baseEnd_2914302 := by
    simpa [prefixWord, tailWord_2914302, baseEnd_2914302] using wordTrace_append hprefix tailTrace_2914302
  have hstable : (prefixWord ++ tailWord_2914302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914302).length < 2 ^ (prefixWord ++ tailWord_2914302).sum := by decide
  have hdescent : baseEnd_2914302 < baseStart_2914302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914358 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2914358 : Nat := 118140960795 + 2914358 * 2 ^ 59
def prefixEnd_2914358 : Nat := 4983230072969 + 3 ^ 40 * 2914358 * 2
def baseEnd_2914358 : Nat := 997644302184009196414745

theorem tailTrace_2914358 : CollatzResearch.WordTrace tailWord_2914358 prefixEnd_2914358 997644302184009196414745 := by
  unfold tailWord_2914358
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643460548486635847811483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70863579183857449043322485 6643460548486635847811483)
  ·
    refine ⟨9965190822729953771717225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6643460548486635847811483 9965190822729953771717225)
    ·
      refine ⟨7473893117047465328787919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9965190822729953771717225 7473893117047465328787919)
      ·
        refine ⟨11210839675571197993181879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473893117047465328787919 11210839675571197993181879)
        ·
          refine ⟨16816259513356796989772819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11210839675571197993181879 16816259513356796989772819)
          ·
            refine ⟨25224389270035195484659229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16816259513356796989772819 25224389270035195484659229)
            ·
              refine ⟨9459145976263198306747211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25224389270035195484659229 9459145976263198306747211)
              ·
                refine ⟨14188718964394797460120817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9459145976263198306747211 14188718964394797460120817)
                ·
                  refine ⟨10641539223296098095090613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14188718964394797460120817 10641539223296098095090613)
                  ·
                    refine ⟨997644302184009196414745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10641539223296098095090613 997644302184009196414745)
                    ·
                      rfl

theorem cell22_2914358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2914358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914358 prefixEnd_2914358 := by exact prefixLift 2914358
  have htrace : WordTrace (prefixWord ++ tailWord_2914358) baseStart_2914358 baseEnd_2914358 := by
    simpa [prefixWord, tailWord_2914358, baseEnd_2914358] using wordTrace_append hprefix tailTrace_2914358
  have hstable : (prefixWord ++ tailWord_2914358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914358).length < 2 ^ (prefixWord ++ tailWord_2914358).sum := by decide
  have hdescent : baseEnd_2914358 < baseStart_2914358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914401 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2914401 : Nat := 118140960795 + 2914401 * 2 ^ 59
def prefixEnd_2914401 : Nat := 4983230072969 + 3 ^ 40 * 2914401 * 2
def baseEnd_2914401 : Nat := 997659021962771417589613

theorem tailTrace_2914401 : CollatzResearch.WordTrace tailWord_2914401 prefixEnd_2914401 997659021962771417589613 := by
  unfold tailWord_2914401
  simp only [CollatzResearch.WordTrace]
  refine ⟨106296937114630391908799057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70864624743086927939199371 106296937114630391908799057)
  ·
    refine ⟨79722702835972793931599293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106296937114630391908799057 79722702835972793931599293)
    ·
      refine ⟨29896013563489797724349735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79722702835972793931599293 29896013563489797724349735)
      ·
        refine ⟨44844020345234696586524603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29896013563489797724349735 44844020345234696586524603)
        ·
          refine ⟨67266030517852044879786905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44844020345234696586524603 67266030517852044879786905)
          ·
            refine ⟨50449522888389033659840179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67266030517852044879786905 50449522888389033659840179)
            ·
              refine ⟨75674284332583550489760269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50449522888389033659840179 75674284332583550489760269)
              ·
                refine ⟨28377856624718831433660101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75674284332583550489760269 28377856624718831433660101)
                ·
                  refine ⟨5320848117134780893811269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28377856624718831433660101 5320848117134780893811269)
                  ·
                    refine ⟨997659021962771417589613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320848117134780893811269 997659021962771417589613)
                    ·
                      rfl

theorem cell22_2914401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2914401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914401 prefixEnd_2914401 := by exact prefixLift 2914401
  have htrace : WordTrace (prefixWord ++ tailWord_2914401) baseStart_2914401 baseEnd_2914401 := by
    simpa [prefixWord, tailWord_2914401, baseEnd_2914401] using wordTrace_append hprefix tailTrace_2914401
  have hstable : (prefixWord ++ tailWord_2914401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914401).length < 2 ^ (prefixWord ++ tailWord_2914401).sum := by decide
  have hdescent : baseEnd_2914401 < baseStart_2914401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914433 : List Nat := [1, 2, 4, 2, 3, 1, 1, 8]
def baseStart_2914433 : Nat := 118140960795 + 2914433 * 2 ^ 59
def prefixEnd_2914433 : Nat := 4983230072969 + 3 ^ 40 * 2914433 * 2
def baseEnd_2914433 : Nat := 110852219579637111198835

theorem tailTrace_2914433 : CollatzResearch.WordTrace tailWord_2914433 prefixEnd_2914433 110852219579637111198835 := by
  unfold tailWord_2914433
  simp only [CollatzResearch.WordTrace]
  refine ⟨106298104250514461373963953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70865402833676307582642635 106298104250514461373963953)
  ·
    refine ⟨79723578187885846030472965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106298104250514461373963953 79723578187885846030472965)
    ·
      refine ⟨14948170910228596130713681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79723578187885846030472965 14948170910228596130713681)
      ·
        refine ⟨11211128182671447098035261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14948170910228596130713681 11211128182671447098035261)
        ·
          refine ⟨4204173068501792661763223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11211128182671447098035261 4204173068501792661763223)
          ·
            refine ⟨6306259602752688992644835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204173068501792661763223 6306259602752688992644835)
            ·
              refine ⟨9459389404129033488967253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306259602752688992644835 9459389404129033488967253)
              ·
                refine ⟨110852219579637111198835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9459389404129033488967253 110852219579637111198835)
                ·
                  rfl

theorem cell22_2914433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 8].length) (baseStart_2914433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914433 prefixEnd_2914433 := by exact prefixLift 2914433
  have htrace : WordTrace (prefixWord ++ tailWord_2914433) baseStart_2914433 baseEnd_2914433 := by
    simpa [prefixWord, tailWord_2914433, baseEnd_2914433] using wordTrace_append hprefix tailTrace_2914433
  have hstable : (prefixWord ++ tailWord_2914433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914433).length < 2 ^ (prefixWord ++ tailWord_2914433).sum := by decide
  have hdescent : baseEnd_2914433 < baseStart_2914433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914452 : List Nat := [2, 4, 2, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2914452 : Nat := 118140960795 + 2914452 * 2 ^ 59
def prefixEnd_2914452 : Nat := 4983230072969 + 3 ^ 40 * 2914452 * 2
def baseEnd_2914452 : Nat := 997676480305024284564457

theorem tailTrace_2914452 : CollatzResearch.WordTrace tailWord_2914452 prefixEnd_2914452 997676480305024284564457 := by
  unfold tailWord_2914452
  simp only [CollatzResearch.WordTrace]
  refine ⟨53149398618722813809452805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70865864824963751745937073 53149398618722813809452805)
  ·
    refine ⟨9965512241010527589272401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53149398618722813809452805 9965512241010527589272401)
    ·
      refine ⟨7474134180757895691954301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9965512241010527589272401 7474134180757895691954301)
      ·
        refine ⟨2802800317784210884482863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7474134180757895691954301 2802800317784210884482863)
        ·
          refine ⟨4204200476676316326724295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802800317784210884482863 4204200476676316326724295)
          ·
            refine ⟨6306300715014474490086443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204200476676316326724295 6306300715014474490086443)
            ·
              refine ⟨9459451072521711735129665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306300715014474490086443 9459451072521711735129665)
              ·
                refine ⟨7094588304391283801347249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9459451072521711735129665 7094588304391283801347249)
                ·
                  refine ⟨5320941228293462851010437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7094588304391283801347249 5320941228293462851010437)
                  ·
                    refine ⟨997676480305024284564457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320941228293462851010437 997676480305024284564457)
                    ·
                      rfl

theorem cell22_2914452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2914452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914452 prefixEnd_2914452 := by exact prefixLift 2914452
  have htrace : WordTrace (prefixWord ++ tailWord_2914452) baseStart_2914452 baseEnd_2914452 := by
    simpa [prefixWord, tailWord_2914452, baseEnd_2914452] using wordTrace_append hprefix tailTrace_2914452
  have hstable : (prefixWord ++ tailWord_2914452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914452).length < 2 ^ (prefixWord ++ tailWord_2914452).sum := by decide
  have hdescent : baseEnd_2914452 < baseStart_2914452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914465 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 3, 3]
def baseStart_2914465 : Nat := 118140960795 + 2914465 * 2 ^ 59
def prefixEnd_2914465 : Nat := 4983230072969 + 3 ^ 40 * 2914465 * 2
def baseEnd_2914465 : Nat := 997680930470696583989417

theorem tailTrace_2914465 : CollatzResearch.WordTrace tailWord_2914465 prefixEnd_2914465 997680930470696583989417 := by
  unfold tailWord_2914465
  simp only [CollatzResearch.WordTrace]
  refine ⟨106299271386398530839128849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70866180924265687226085899 106299271386398530839128849)
  ·
    refine ⟨79724453539798898129346637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106299271386398530839128849 79724453539798898129346637)
    ·
      refine ⟨29896670077424586798504989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79724453539798898129346637 29896670077424586798504989)
      ·
        refine ⟨11211251279034220049439371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29896670077424586798504989 11211251279034220049439371)
        ·
          refine ⟨16816876918551330074159057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11211251279034220049439371 16816876918551330074159057)
          ·
            refine ⟨12612657688913497555619293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16816876918551330074159057 12612657688913497555619293)
            ·
              refine ⟨4729746633342561583357235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12612657688913497555619293 4729746633342561583357235)
              ·
                refine ⟨7094619950013842375035853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729746633342561583357235 7094619950013842375035853)
                ·
                  refine ⟨2660482481255190890638445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7094619950013842375035853 2660482481255190890638445)
                  ·
                    refine ⟨997680930470696583989417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660482481255190890638445 997680930470696583989417)
                    ·
                      rfl

theorem cell22_2914465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_2914465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914465 prefixEnd_2914465 := by exact prefixLift 2914465
  have htrace : WordTrace (prefixWord ++ tailWord_2914465) baseStart_2914465 baseEnd_2914465 := by
    simpa [prefixWord, tailWord_2914465, baseEnd_2914465] using wordTrace_append hprefix tailTrace_2914465
  have hstable : (prefixWord ++ tailWord_2914465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914465).length < 2 ^ (prefixWord ++ tailWord_2914465).sum := by decide
  have hdescent : baseEnd_2914465 < baseStart_2914465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914471 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2914471 : Nat := 118140960795 + 2914471 * 2 ^ 59
def prefixEnd_2914471 : Nat := 4983230072969 + 3 ^ 40 * 2914471 * 2
def baseEnd_2914471 : Nat := 997682984393314568339399

theorem tailTrace_2914471 : CollatzResearch.WordTrace tailWord_2914471 prefixEnd_2914471 997682984393314568339399 := by
  unfold tailWord_2914471
  simp only [CollatzResearch.WordTrace]
  refine ⟨106299490224376793863847267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70866326816251195909231511 106299490224376793863847267)
  ·
    refine ⟨159449235336565190795770901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106299490224376793863847267 159449235336565190795770901)
    ·
      refine ⟨7474182906401493318551761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159449235336565190795770901 7474182906401493318551761)
      ·
        refine ⟨5605637179801119988913821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7474182906401493318551761 5605637179801119988913821)
        ·
          refine ⟨2102113942425419995842683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5605637179801119988913821 2102113942425419995842683)
          ·
            refine ⟨3153170913638129993764025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102113942425419995842683 3153170913638129993764025)
            ·
              refine ⟨2364878185228597495323019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153170913638129993764025 2364878185228597495323019)
              ·
                refine ⟨3547317277842896242984529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364878185228597495323019 3547317277842896242984529)
                ·
                  refine ⟨2660487958382172182238397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3547317277842896242984529 2660487958382172182238397)
                  ·
                    refine ⟨997682984393314568339399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660487958382172182238397 997682984393314568339399)
                    ·
                      rfl

theorem cell22_2914471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2914471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914471 prefixEnd_2914471 := by exact prefixLift 2914471
  have htrace : WordTrace (prefixWord ++ tailWord_2914471) baseStart_2914471 baseEnd_2914471 := by
    simpa [prefixWord, tailWord_2914471, baseEnd_2914471] using wordTrace_append hprefix tailTrace_2914471
  have hstable : (prefixWord ++ tailWord_2914471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914471).length < 2 ^ (prefixWord ++ tailWord_2914471).sum := by decide
  have hdescent : baseEnd_2914471 < baseStart_2914471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914476 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_2914476 : Nat := 118140960795 + 2914476 * 2 ^ 59
def prefixEnd_2914476 : Nat := 4983230072969 + 3 ^ 40 * 2914476 * 2
def baseEnd_2914476 : Nat := 997684695995496221964383

theorem tailTrace_2914476 : CollatzResearch.WordTrace tailWord_2914476 prefixEnd_2914476 997684695995496221964383 := by
  unfold tailWord_2914476
  simp only [CollatzResearch.WordTrace]
  refine ⟨53149836294679339858889641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70866448392905786478519521 53149836294679339858889641)
  ·
    refine ⟨39862377221009504894167231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53149836294679339858889641 39862377221009504894167231)
    ·
      refine ⟨59793565831514257341250847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39862377221009504894167231 59793565831514257341250847)
      ·
        refine ⟨89690348747271386011876271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59793565831514257341250847 89690348747271386011876271)
        ·
          refine ⟨134535523120907079017814407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89690348747271386011876271 134535523120907079017814407)
          ·
            refine ⟨201803284681360618526721611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134535523120907079017814407 201803284681360618526721611)
            ·
              refine ⟨302704927022040927790082417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201803284681360618526721611 302704927022040927790082417)
              ·
                refine ⟨227028695266530695842561813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 302704927022040927790082417 227028695266530695842561813)
                ·
                  refine ⟨10641970090618626367620085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 227028695266530695842561813 10641970090618626367620085)
                  ·
                    refine ⟨997684695995496221964383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10641970090618626367620085 997684695995496221964383)
                    ·
                      rfl

theorem cell22_2914476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_2914476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914476 prefixEnd_2914476 := by exact prefixLift 2914476
  have htrace : WordTrace (prefixWord ++ tailWord_2914476) baseStart_2914476 baseEnd_2914476 := by
    simpa [prefixWord, tailWord_2914476, baseEnd_2914476] using wordTrace_append hprefix tailTrace_2914476
  have hstable : (prefixWord ++ tailWord_2914476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914476).length < 2 ^ (prefixWord ++ tailWord_2914476).sum := by decide
  have hdescent : baseEnd_2914476 < baseStart_2914476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914525 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2914525 : Nat := 118140960795 + 2914525 * 2 ^ 59
def prefixEnd_2914525 : Nat := 4983230072969 + 3 ^ 40 * 2914525 * 2
def baseEnd_2914525 : Nat := 997701469696876427489233

theorem tailTrace_2914525 : CollatzResearch.WordTrace tailWord_2914525 prefixEnd_2914525 997701469696876427489233 := by
  unfold tailWord_2914525
  simp only [CollatzResearch.WordTrace]
  refine ⟨106301459766181161086313029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70867639844120774057542019 106301459766181161086313029)
  ·
    refine ⟨19931523706158967703683693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106301459766181161086313029 19931523706158967703683693)
    ·
      refine ⟨7474321389809612888881385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19931523706158967703683693 7474321389809612888881385)
      ·
        refine ⟨5605741042357209666661039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7474321389809612888881385 5605741042357209666661039)
        ·
          refine ⟨8408611563535814499991559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605741042357209666661039 8408611563535814499991559)
          ·
            refine ⟨12612917345303721749987339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408611563535814499991559 12612917345303721749987339)
            ·
              refine ⟨18919376017955582624981009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12612917345303721749987339 18919376017955582624981009)
              ·
                refine ⟨14189532013466686968735757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18919376017955582624981009 14189532013466686968735757)
                ·
                  refine ⟨5321074505050007613275909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14189532013466686968735757 5321074505050007613275909)
                  ·
                    refine ⟨997701469696876427489233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321074505050007613275909 997701469696876427489233)
                    ·
                      rfl

theorem cell22_2914525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2914525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914525 prefixEnd_2914525 := by exact prefixLift 2914525
  have htrace : WordTrace (prefixWord ++ tailWord_2914525) baseStart_2914525 baseEnd_2914525 := by
    simpa [prefixWord, tailWord_2914525, baseEnd_2914525] using wordTrace_append hprefix tailTrace_2914525
  have hstable : (prefixWord ++ tailWord_2914525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914525).length < 2 ^ (prefixWord ++ tailWord_2914525).sum := by decide
  have hdescent : baseEnd_2914525 < baseStart_2914525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914553 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_2914553 : Nat := 118140960795 + 2914553 * 2 ^ 59
def prefixEnd_2914553 : Nat := 4983230072969 + 3 ^ 40 * 2914553 * 2
def baseEnd_2914553 : Nat := 997711054669093687789147

theorem tailTrace_2914553 : CollatzResearch.WordTrace tailWord_2914553 prefixEnd_2914553 997711054669093687789147 := by
  unfold tailWord_2914553
  simp only [CollatzResearch.WordTrace]
  refine ⟨106302481010079721868332313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70868320673386481245554875 106302481010079721868332313)
  ·
    refine ⟨79726860757559791401249235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106302481010079721868332313 79726860757559791401249235)
    ·
      refine ⟨119590291136339687101873853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79726860757559791401249235 119590291136339687101873853)
      ·
        refine ⟨44846359176127382663202695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119590291136339687101873853 44846359176127382663202695)
        ·
          refine ⟨67269538764191073994804043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44846359176127382663202695 67269538764191073994804043)
          ·
            refine ⟨100904308146286610992206065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67269538764191073994804043 100904308146286610992206065)
            ·
              refine ⟨75678231109714958244154549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100904308146286610992206065 75678231109714958244154549)
              ·
                refine ⟨7094834166535777335389489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75678231109714958244154549 7094834166535777335389489)
                ·
                  refine ⟨5321125624901833001542117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7094834166535777335389489 5321125624901833001542117)
                  ·
                    refine ⟨997711054669093687789147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321125624901833001542117 997711054669093687789147)
                    ·
                      rfl

theorem cell22_2914553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_2914553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914553 prefixEnd_2914553 := by exact prefixLift 2914553
  have htrace : WordTrace (prefixWord ++ tailWord_2914553) baseStart_2914553 baseEnd_2914553 := by
    simpa [prefixWord, tailWord_2914553, baseEnd_2914553] using wordTrace_append hprefix tailTrace_2914553
  have hstable : (prefixWord ++ tailWord_2914553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914553).length < 2 ^ (prefixWord ++ tailWord_2914553).sum := by decide
  have hdescent : baseEnd_2914553 < baseStart_2914553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914568 : List Nat := [2, 1, 3, 2, 3, 2, 9]
def baseStart_2914568 : Nat := 118140960795 + 2914568 * 2 ^ 59
def prefixEnd_2914568 : Nat := 4983230072969 + 3 ^ 40 * 2914568 * 2
def baseEnd_2914568 : Nat := 36952451462060690691263

theorem tailTrace_2914568 : CollatzResearch.WordTrace tailWord_2914568 prefixEnd_2914568 36952451462060690691263 := by
  unfold tailWord_2914568
  simp only [CollatzResearch.WordTrace]
  refine ⟨53151514052512689715064179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70868685403350252953418905 53151514052512689715064179)
  ·
    refine ⟨79727271078769034572596269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53151514052512689715064179 79727271078769034572596269)
    ·
      refine ⟨29897726654538387964723601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79727271078769034572596269 29897726654538387964723601)
      ·
        refine ⟨22423294990903790973542701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29897726654538387964723601 22423294990903790973542701)
        ·
          refine ⟨8408735621588921615078513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22423294990903790973542701 8408735621588921615078513)
          ·
            refine ⟨6306551716191691211308885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8408735621588921615078513 6306551716191691211308885)
            ·
              refine ⟨36952451462060690691263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6306551716191691211308885 36952451462060690691263)
              ·
                rfl

theorem cell22_2914568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 9].length) (baseStart_2914568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914568 prefixEnd_2914568 := by exact prefixLift 2914568
  have htrace : WordTrace (prefixWord ++ tailWord_2914568) baseStart_2914568 baseEnd_2914568 := by
    simpa [prefixWord, tailWord_2914568, baseEnd_2914568] using wordTrace_append hprefix tailTrace_2914568
  have hstable : (prefixWord ++ tailWord_2914568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914568).length < 2 ^ (prefixWord ++ tailWord_2914568).sum := by decide
  have hdescent : baseEnd_2914568 < baseStart_2914568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914589 : List Nat := [1, 4, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_2914589 : Nat := 118140960795 + 2914589 * 2 ^ 59
def prefixEnd_2914589 : Nat := 4983230072969 + 3 ^ 40 * 2914589 * 2
def baseEnd_2914589 : Nat := 997723378204801593889037

theorem tailTrace_2914589 : CollatzResearch.WordTrace tailWord_2914589 prefixEnd_2914589 997723378204801593889037 := by
  unfold tailWord_2914589
  simp only [CollatzResearch.WordTrace]
  refine ⟨106303794037949300016642821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70869196025299533344428547 106303794037949300016642821)
  ·
    refine ⟨19931961382115493753120529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106303794037949300016642821 19931961382115493753120529)
    ·
      refine ⟨14948971036586620314840397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19931961382115493753120529 14948971036586620314840397)
      ·
        refine ⟨5605864138719982618065149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14948971036586620314840397 5605864138719982618065149)
        ·
          refine ⟨2102199052019993481774431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5605864138719982618065149 2102199052019993481774431)
          ·
            refine ⟨3153298578029990222661647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102199052019993481774431 3153298578029990222661647)
            ·
              refine ⟨4729947867044985333992471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153298578029990222661647 4729947867044985333992471)
              ·
                refine ⟨7094921800567478000988707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729947867044985333992471 7094921800567478000988707)
                ·
                  refine ⟨10642382700851217001483061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094921800567478000988707 10642382700851217001483061)
                  ·
                    refine ⟨997723378204801593889037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10642382700851217001483061 997723378204801593889037)
                    ·
                      rfl

theorem cell22_2914589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_2914589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914589 prefixEnd_2914589 := by exact prefixLift 2914589
  have htrace : WordTrace (prefixWord ++ tailWord_2914589) baseStart_2914589 baseEnd_2914589 := by
    simpa [prefixWord, tailWord_2914589, baseEnd_2914589] using wordTrace_append hprefix tailTrace_2914589
  have hstable : (prefixWord ++ tailWord_2914589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914589).length < 2 ^ (prefixWord ++ tailWord_2914589).sum := by decide
  have hdescent : baseEnd_2914589 < baseStart_2914589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914613 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 9]
def baseStart_2914613 : Nat := 118140960795 + 2914613 * 2 ^ 59
def prefixEnd_2914613 : Nat := 4983230072969 + 3 ^ 40 * 2914613 * 2
def baseEnd_2914613 : Nat := 332577197965091177096321

theorem tailTrace_2914613 : CollatzResearch.WordTrace tailWord_2914613 prefixEnd_2914613 332577197965091177096321 := by
  unfold tailWord_2914613
  simp only [CollatzResearch.WordTrace]
  refine ⟨106304669389862352115516493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70869779593241568077010995 106304669389862352115516493)
  ·
    refine ⟨39864251021198382043318685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106304669389862352115516493 39864251021198382043318685)
    ·
      refine ⟨14949094132949393266244507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39864251021198382043318685 14949094132949393266244507)
      ·
        refine ⟨22423641199424089899366761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14949094132949393266244507 22423641199424089899366761)
        ·
          refine ⟨16817730899568067424525071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22423641199424089899366761 16817730899568067424525071)
          ·
            refine ⟨25226596349352101136787607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16817730899568067424525071 25226596349352101136787607)
            ·
              refine ⟨37839894524028151705181411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25226596349352101136787607 37839894524028151705181411)
              ·
                refine ⟨56759841786042227557772117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37839894524028151705181411 56759841786042227557772117)
                ·
                  refine ⟨332577197965091177096321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56759841786042227557772117 332577197965091177096321)
                  ·
                    rfl

theorem cell22_2914613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_2914613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914613 prefixEnd_2914613 := by exact prefixLift 2914613
  have htrace : WordTrace (prefixWord ++ tailWord_2914613) baseStart_2914613 baseEnd_2914613 := by
    simpa [prefixWord, tailWord_2914613, baseEnd_2914613] using wordTrace_append hprefix tailTrace_2914613
  have hstable : (prefixWord ++ tailWord_2914613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914613).length < 2 ^ (prefixWord ++ tailWord_2914613).sum := by decide
  have hdescent : baseEnd_2914613 < baseStart_2914613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914660 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2914660 : Nat := 118140960795 + 2914660 * 2 ^ 59
def prefixEnd_2914660 : Nat := 4983230072969 + 3 ^ 40 * 2914660 * 2
def baseEnd_2914660 : Nat := 997747682955781075363819

theorem tailTrace_2914660 : CollatzResearch.WordTrace tailWord_2914660 prefixEnd_2914660 997747682955781075363819 := by
  unfold tailWord_2914660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53153191810346039571238717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70870922413794719428318289 53153191810346039571238717)
  ·
    refine ⟨19932446928879764839214519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53153191810346039571238717 19932446928879764839214519)
    ·
      refine ⟨29898670393319647258821779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19932446928879764839214519 29898670393319647258821779)
      ·
        refine ⟨44848005589979470888232669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29898670393319647258821779 44848005589979470888232669)
        ·
          refine ⟨16818002096242301583087251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44848005589979470888232669 16818002096242301583087251)
          ·
            refine ⟨25227003144363452374630877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16818002096242301583087251 25227003144363452374630877)
            ·
              refine ⟨9460126179136294640486579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25227003144363452374630877 9460126179136294640486579)
              ·
                refine ⟨14190189268704441960729869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460126179136294640486579 14190189268704441960729869)
                ·
                  refine ⟨5321320975764165735273701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14190189268704441960729869 5321320975764165735273701)
                  ·
                    refine ⟨997747682955781075363819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321320975764165735273701 997747682955781075363819)
                    ·
                      rfl

theorem cell22_2914660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2914660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914660 prefixEnd_2914660 := by exact prefixLift 2914660
  have htrace : WordTrace (prefixWord ++ tailWord_2914660) baseStart_2914660 baseEnd_2914660 := by
    simpa [prefixWord, tailWord_2914660, baseEnd_2914660] using wordTrace_append hprefix tailTrace_2914660
  have hstable : (prefixWord ++ tailWord_2914660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914660).length < 2 ^ (prefixWord ++ tailWord_2914660).sum := by decide
  have hdescent : baseEnd_2914660 < baseStart_2914660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914688 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 5, 6]
def baseStart_2914688 : Nat := 118140960795 + 2914688 * 2 ^ 59
def prefixEnd_2914688 : Nat := 4983230072969 + 3 ^ 40 * 2914688 * 2
def baseEnd_2914688 : Nat := 997757267927998335663733

theorem tailTrace_2914688 : CollatzResearch.WordTrace tailWord_2914688 prefixEnd_2914688 997757267927998335663733 := by
  unfold tailWord_2914688
  simp only [CollatzResearch.WordTrace]
  refine ⟨53153702432295319962248359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70871603243060426616331145 53153702432295319962248359)
  ·
    refine ⟨79730553648442979943372539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53153702432295319962248359 79730553648442979943372539)
    ·
      refine ⟨119595830472664469915058809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79730553648442979943372539 119595830472664469915058809)
      ·
        refine ⟨89696872854498352436294107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119595830472664469915058809 89696872854498352436294107)
        ·
          refine ⟨134545309281747528654441161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89696872854498352436294107 134545309281747528654441161)
          ·
            refine ⟨100908981961310646490830871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134545309281747528654441161 100908981961310646490830871)
            ·
              refine ⟨151363472941965969736246307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100908981961310646490830871 151363472941965969736246307)
              ·
                refine ⟨227045209412948954604369461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151363472941965969736246307 227045209412948954604369461)
                ·
                  refine ⟨21285488382463964494159637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 227045209412948954604369461 21285488382463964494159637)
                  ·
                    refine ⟨997757267927998335663733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21285488382463964494159637 997757267927998335663733)
                    ·
                      rfl

theorem cell22_2914688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_2914688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914688 prefixEnd_2914688 := by exact prefixLift 2914688
  have htrace : WordTrace (prefixWord ++ tailWord_2914688) baseStart_2914688 baseEnd_2914688 := by
    simpa [prefixWord, tailWord_2914688, baseEnd_2914688] using wordTrace_append hprefix tailTrace_2914688
  have hstable : (prefixWord ++ tailWord_2914688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914688).length < 2 ^ (prefixWord ++ tailWord_2914688).sum := by decide
  have hdescent : baseEnd_2914688 < baseStart_2914688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914692 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 4]
def baseStart_2914692 : Nat := 118140960795 + 2914692 * 2 ^ 59
def prefixEnd_2914692 : Nat := 4983230072969 + 3 ^ 40 * 2914692 * 2
def baseEnd_2914692 : Nat := 332586212403247886187907

theorem tailTrace_2914692 : CollatzResearch.WordTrace tailWord_2914692 prefixEnd_2914692 332586212403247886187907 := by
  unfold tailWord_2914692
  simp only [CollatzResearch.WordTrace]
  refine ⟨53153775378288074303821165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70871700504384099071761553 53153775378288074303821165)
  ·
    refine ⟨19932665766858027863932937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53153775378288074303821165 19932665766858027863932937)
    ·
      refine ⟨14949499325143520897949703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19932665766858027863932937 14949499325143520897949703)
      ·
        refine ⟨22424248987715281346924555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14949499325143520897949703 22424248987715281346924555)
        ·
          refine ⟨33636373481572922020386833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22424248987715281346924555 33636373481572922020386833)
          ·
            refine ⟨25227280111179691515290125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33636373481572922020386833 25227280111179691515290125)
            ·
              refine ⟨9460230041692384318233797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25227280111179691515290125 9460230041692384318233797)
              ·
                refine ⟨1773793132817322059668837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9460230041692384318233797 1773793132817322059668837)
                ·
                  refine ⟨332586212403247886187907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773793132817322059668837 332586212403247886187907)
                  ·
                    rfl

theorem cell22_2914692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_2914692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914692 prefixEnd_2914692 := by exact prefixLift 2914692
  have htrace : WordTrace (prefixWord ++ tailWord_2914692) baseStart_2914692 baseEnd_2914692 := by
    simpa [prefixWord, tailWord_2914692, baseEnd_2914692] using wordTrace_append hprefix tailTrace_2914692
  have hstable : (prefixWord ++ tailWord_2914692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914692).length < 2 ^ (prefixWord ++ tailWord_2914692).sum := by decide
  have hdescent : baseEnd_2914692 < baseStart_2914692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914741 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2914741 : Nat := 118140960795 + 2914741 * 2 ^ 59
def prefixEnd_2914741 : Nat := 4983230072969 + 3 ^ 40 * 2914741 * 2
def baseEnd_2914741 : Nat := 997775410911123864088571

theorem tailTrace_2914741 : CollatzResearch.WordTrace tailWord_2914741 prefixEnd_2914741 997775410911123864088571 := by
  unfold tailWord_2914741
  simp only [CollatzResearch.WordTrace]
  refine ⟨106309337933398629976176077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70872891955599086650784051 106309337933398629976176077)
  ·
    refine ⟨39866001725024486241066029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106309337933398629976176077 39866001725024486241066029)
    ·
      refine ⟨14949750646884182340399761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39866001725024486241066029 14949750646884182340399761)
      ·
        refine ⟨11212312985163136755299821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14949750646884182340399761 11212312985163136755299821)
        ·
          refine ⟨4204617369436176283237433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11212312985163136755299821 4204617369436176283237433)
          ·
            refine ⟨3153463027077132212428075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204617369436176283237433 3153463027077132212428075)
            ·
              refine ⟨4730194540615698318642113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153463027077132212428075 4730194540615698318642113)
              ·
                refine ⟨3547645905461773738981585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4730194540615698318642113 3547645905461773738981585)
                ·
                  refine ⟨2660734429096330304236189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3547645905461773738981585 2660734429096330304236189)
                  ·
                    refine ⟨997775410911123864088571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660734429096330304236189 997775410911123864088571)
                    ·
                      rfl

theorem cell22_2914741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2914741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914741 prefixEnd_2914741 := by exact prefixLift 2914741
  have htrace : WordTrace (prefixWord ++ tailWord_2914741) baseStart_2914741 baseEnd_2914741 := by
    simpa [prefixWord, tailWord_2914741, baseEnd_2914741] using wordTrace_append hprefix tailTrace_2914741
  have hstable : (prefixWord ++ tailWord_2914741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914741).length < 2 ^ (prefixWord ++ tailWord_2914741).sum := by decide
  have hdescent : baseEnd_2914741 < baseStart_2914741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914750 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_2914750 : Nat := 118140960795 + 2914750 * 2 ^ 59
def prefixEnd_2914750 : Nat := 4983230072969 + 3 ^ 40 * 2914750 * 2
def baseEnd_2914750 : Nat := 997778491795050840613543

theorem tailTrace_2914750 : CollatzResearch.WordTrace tailWord_2914750 prefixEnd_2914750 997778491795050840613543 := by
  unfold tailWord_2914750
  simp only [CollatzResearch.WordTrace]
  refine ⟨13288708273795753064156713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70873110793577349675502469 13288708273795753064156713)
  ·
    refine ⟨9966531205346814798117535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13288708273795753064156713 9966531205346814798117535)
    ·
      refine ⟨14949796808020222197176303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9966531205346814798117535 14949796808020222197176303)
      ·
        refine ⟨22424695212030333295764455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14949796808020222197176303 22424695212030333295764455)
        ·
          refine ⟨33637042818045499943646683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22424695212030333295764455 33637042818045499943646683)
          ·
            refine ⟨50455564227068249915470025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33637042818045499943646683 50455564227068249915470025)
            ·
              refine ⟨37841673170301187436602519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50455564227068249915470025 37841673170301187436602519)
              ·
                refine ⟨56762509755451781154903779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37841673170301187436602519 56762509755451781154903779)
                ·
                  refine ⟨85143764633177671732355669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56762509755451781154903779 85143764633177671732355669)
                  ·
                    refine ⟨997778491795050840613543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85143764633177671732355669 997778491795050840613543)
                    ·
                      rfl

theorem cell22_2914750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_2914750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914750 prefixEnd_2914750 := by exact prefixLift 2914750
  have htrace : WordTrace (prefixWord ++ tailWord_2914750) baseStart_2914750 baseEnd_2914750 := by
    simpa [prefixWord, tailWord_2914750, baseEnd_2914750] using wordTrace_append hprefix tailTrace_2914750
  have hstable : (prefixWord ++ tailWord_2914750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914750).length < 2 ^ (prefixWord ++ tailWord_2914750).sum := by decide
  have hdescent : baseEnd_2914750 < baseStart_2914750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914810 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 6]
def baseStart_2914810 : Nat := 118140960795 + 2914810 * 2 ^ 59
def prefixEnd_2914810 : Nat := 4983230072969 + 3 ^ 40 * 2914810 * 2
def baseEnd_2914810 : Nat := 332599677007076894704453

theorem tailTrace_2914810 : CollatzResearch.WordTrace tailWord_2914810 prefixEnd_2914810 332599677007076894704453 := by
  unfold tailWord_2914810
  simp only [CollatzResearch.WordTrace]
  refine ⟨26577963642537163690109471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70874569713432436506958589 26577963642537163690109471)
  ·
    refine ⟨39866945463805745535164207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26577963642537163690109471 39866945463805745535164207)
    ·
      refine ⟨59800418195708618302746311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39866945463805745535164207 59800418195708618302746311)
      ·
        refine ⟨89700627293562927454119467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59800418195708618302746311 89700627293562927454119467)
        ·
          refine ⟨134550940940344391181179201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89700627293562927454119467 134550940940344391181179201)
          ·
            refine ⟨100913205705258293385884401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134550940940344391181179201 100913205705258293385884401)
            ·
              refine ⟨75684904278943720039413301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100913205705258293385884401 75684904278943720039413301)
              ·
                refine ⟨7095459776150973753694997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75684904278943720039413301 7095459776150973753694997)
                ·
                  refine ⟨332599677007076894704453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7095459776150973753694997 332599677007076894704453)
                  ·
                    rfl

theorem cell22_2914810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 6].length) (baseStart_2914810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914810 prefixEnd_2914810 := by exact prefixLift 2914810
  have htrace : WordTrace (prefixWord ++ tailWord_2914810) baseStart_2914810 baseEnd_2914810 := by
    simpa [prefixWord, tailWord_2914810, baseEnd_2914810] using wordTrace_append hprefix tailTrace_2914810
  have hstable : (prefixWord ++ tailWord_2914810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914810).length < 2 ^ (prefixWord ++ tailWord_2914810).sum := by decide
  have hdescent : baseEnd_2914810 < baseStart_2914810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914842 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 6, 3]
def baseStart_2914842 : Nat := 118140960795 + 2914842 * 2 ^ 59
def prefixEnd_2914842 : Nat := 4983230072969 + 3 ^ 40 * 2914842 * 2
def baseEnd_2914842 : Nat := 997809985275193267313261

theorem tailTrace_2914842 : CollatzResearch.WordTrace tailWord_2914842 prefixEnd_2914842 997809985275193267313261 := by
  unfold tailWord_2914842
  simp only [CollatzResearch.WordTrace]
  refine ⟨26578255426508181056400695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70875347804021816150401853 26578255426508181056400695)
  ·
    refine ⟨39867383139762271584601043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26578255426508181056400695 39867383139762271584601043)
    ·
      refine ⟨59801074709643407376901565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39867383139762271584601043 59801074709643407376901565)
      ·
        refine ⟨22425403016116277766338087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59801074709643407376901565 22425403016116277766338087)
        ·
          refine ⟨33638104524174416649507131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22425403016116277766338087 33638104524174416649507131)
          ·
            refine ⟨50457156786261624974260697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33638104524174416649507131 50457156786261624974260697)
            ·
              refine ⟨37842867589696218730695523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50457156786261624974260697 37842867589696218730695523)
              ·
                refine ⟨56764301384544328096043285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37842867589696218730695523 56764301384544328096043285)
                ·
                  refine ⟨2660826627400515379502029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56764301384544328096043285 2660826627400515379502029)
                  ·
                    refine ⟨997809985275193267313261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660826627400515379502029 997809985275193267313261)
                    ·
                      rfl

theorem cell22_2914842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 6, 3].length) (baseStart_2914842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914842 prefixEnd_2914842 := by exact prefixLift 2914842
  have htrace : WordTrace (prefixWord ++ tailWord_2914842) baseStart_2914842 baseEnd_2914842 := by
    simpa [prefixWord, tailWord_2914842, baseEnd_2914842] using wordTrace_append hprefix tailTrace_2914842
  have hstable : (prefixWord ++ tailWord_2914842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914842).length < 2 ^ (prefixWord ++ tailWord_2914842).sum := by decide
  have hdescent : baseEnd_2914842 < baseStart_2914842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914910 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_2914910 : Nat := 118140960795 + 2914910 * 2 ^ 59
def prefixEnd_2914910 : Nat := 4983230072969 + 3 ^ 40 * 2914910 * 2
def baseEnd_2914910 : Nat := 997833263064863756613053

theorem tailTrace_2914910 : CollatzResearch.WordTrace tailWord_2914910 prefixEnd_2914910 997833263064863756613053 := by
  unfold tailWord_2914910
  simp only [CollatzResearch.WordTrace]
  refine ⟨13289437733723296479884773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70877001246524247892718789 13289437733723296479884773)
  ·
    refine ⟨2491769575073118089978395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13289437733723296479884773 2491769575073118089978395)
    ·
      refine ⟨3737654362609677134967593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491769575073118089978395 3737654362609677134967593)
      ·
        refine ⟨2803240771957257851225695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737654362609677134967593 2803240771957257851225695)
        ·
          refine ⟨4204861157935886776838543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803240771957257851225695 4204861157935886776838543)
          ·
            refine ⟨6307291736903830165257815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204861157935886776838543 6307291736903830165257815)
            ·
              refine ⟨9460937605355745247886723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6307291736903830165257815 9460937605355745247886723)
              ·
                refine ⟨14191406408033617871830085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9460937605355745247886723 14191406408033617871830085)
                ·
                  refine ⟨2660888701506303350968141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14191406408033617871830085 2660888701506303350968141)
                  ·
                    refine ⟨997833263064863756613053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2660888701506303350968141 997833263064863756613053)
                    ·
                      rfl

theorem cell22_2914910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_2914910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914910 prefixEnd_2914910 := by exact prefixLift 2914910
  have htrace : WordTrace (prefixWord ++ tailWord_2914910) baseStart_2914910 baseEnd_2914910 := by
    simpa [prefixWord, tailWord_2914910, baseEnd_2914910] using wordTrace_append hprefix tailTrace_2914910
  have hstable : (prefixWord ++ tailWord_2914910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914910).length < 2 ^ (prefixWord ++ tailWord_2914910).sum := by decide
  have hdescent : baseEnd_2914910 < baseStart_2914910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914947 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_2914947 : Nat := 118140960795 + 2914947 * 2 ^ 59
def prefixEnd_2914947 : Nat := 4983230072969 + 3 ^ 40 * 2914947 * 2
def baseEnd_2914947 : Nat := 997845928921007993437939

theorem tailTrace_2914947 : CollatzResearch.WordTrace tailWord_2914947 prefixEnd_2914947 997845928921007993437939 := by
  unfold tailWord_2914947
  simp only [CollatzResearch.WordTrace]
  refine ⟨106316851370652327158175095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70877900913768218105450063 106316851370652327158175095)
  ·
    refine ⟨159475277055978490737262643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106316851370652327158175095 159475277055978490737262643)
    ·
      refine ⟨239212915583967736105893965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159475277055978490737262643 239212915583967736105893965)
      ·
        refine ⟨89704843343987901039710237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239212915583967736105893965 89704843343987901039710237)
        ·
          refine ⟨33639316253995462889891339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89704843343987901039710237 33639316253995462889891339)
          ·
            refine ⟨50458974380993194334837009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33639316253995462889891339 50458974380993194334837009)
            ·
              refine ⟨37844230785744895751127757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50458974380993194334837009 37844230785744895751127757)
              ·
                refine ⟨14191586544654335906672909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37844230785744895751127757 14191586544654335906672909)
                ·
                  refine ⟨5321844954245375965002341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14191586544654335906672909 5321844954245375965002341)
                  ·
                    refine ⟨997845928921007993437939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321844954245375965002341 997845928921007993437939)
                    ·
                      rfl

theorem cell22_2914947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_2914947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914947 prefixEnd_2914947 := by exact prefixLift 2914947
  have htrace : WordTrace (prefixWord ++ tailWord_2914947) baseStart_2914947 baseEnd_2914947 := by
    simpa [prefixWord, tailWord_2914947, baseEnd_2914947] using wordTrace_append hprefix tailTrace_2914947
  have hstable : (prefixWord ++ tailWord_2914947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914947).length < 2 ^ (prefixWord ++ tailWord_2914947).sum := by decide
  have hdescent : baseEnd_2914947 < baseStart_2914947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914992 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 6, 4]
def baseStart_2914992 : Nat := 118140960795 + 2914992 * 2 ^ 59
def prefixEnd_2914992 : Nat := 4983230072969 + 3 ^ 40 * 2914992 * 2
def baseEnd_2914992 : Nat := 997861333340642876062801

theorem tailTrace_2914992 : CollatzResearch.WordTrace tailWord_2914992 prefixEnd_2914992 997861333340642876062801 := by
  unfold tailWord_2914992
  simp only [CollatzResearch.WordTrace]
  refine ⟨53159246327744649921781615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70878995103659533229042153 53159246327744649921781615)
  ·
    refine ⟨79738869491616974882672423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53159246327744649921781615 79738869491616974882672423)
    ·
      refine ⟨119608304237425462324008635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79738869491616974882672423 119608304237425462324008635)
      ·
        refine ⟨179412456356138193486012953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119608304237425462324008635 179412456356138193486012953)
        ·
          refine ⟨134559342267103645114509715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179412456356138193486012953 134559342267103645114509715)
          ·
            refine ⟨201839013400655467671764573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134559342267103645114509715 201839013400655467671764573)
            ·
              refine ⟨75689630025245800376911715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201839013400655467671764573 75689630025245800376911715)
              ·
                refine ⟨113534445037868700565367573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75689630025245800376911715 113534445037868700565367573)
                ·
                  refine ⟨5321927111150095339001605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 113534445037868700565367573 5321927111150095339001605)
                  ·
                    refine ⟨997861333340642876062801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321927111150095339001605 997861333340642876062801)
                    ·
                      rfl

theorem cell22_2914992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 6, 4].length) (baseStart_2914992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914992 prefixEnd_2914992 := by exact prefixLift 2914992
  have htrace : WordTrace (prefixWord ++ tailWord_2914992) baseStart_2914992 baseEnd_2914992 := by
    simpa [prefixWord, tailWord_2914992, baseEnd_2914992] using wordTrace_append hprefix tailTrace_2914992
  have hstable : (prefixWord ++ tailWord_2914992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914992).length < 2 ^ (prefixWord ++ tailWord_2914992).sum := by decide
  have hdescent : baseEnd_2914992 < baseStart_2914992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2914998 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 3, 4]
def baseStart_2914998 : Nat := 118140960795 + 2914998 * 2 ^ 59
def prefixEnd_2914998 : Nat := 4983230072969 + 3 ^ 40 * 2914998 * 2
def baseEnd_2914998 : Nat := 997863387263260860412783

theorem tailTrace_2914998 : CollatzResearch.WordTrace tailWord_2914998 prefixEnd_2914998 997863387263260860412783 := by
  unfold tailWord_2914998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644919468341722679267603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70879140995645041912187765 6644919468341722679267603)
  ·
    refine ⟨9967379202512584018901405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644919468341722679267603 9967379202512584018901405)
    ·
      refine ⟨3737767200942219007088027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9967379202512584018901405 3737767200942219007088027)
      ·
        refine ⟨5606650801413328510632041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737767200942219007088027 5606650801413328510632041)
        ·
          refine ⟨4204988101059996382974031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606650801413328510632041 4204988101059996382974031)
          ·
            refine ⟨6307482151589994574461047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204988101059996382974031 6307482151589994574461047)
            ·
              refine ⟨9461223227384991861691571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6307482151589994574461047 9461223227384991861691571)
              ·
                refine ⟨14191834841077487792537357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9461223227384991861691571 14191834841077487792537357)
                ·
                  refine ⟨5321938065404057922201509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14191834841077487792537357 5321938065404057922201509)
                  ·
                    refine ⟨997863387263260860412783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5321938065404057922201509 997863387263260860412783)
                    ·
                      rfl

theorem cell22_2914998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_2914998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2914998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2914998 prefixEnd_2914998 := by exact prefixLift 2914998
  have htrace : WordTrace (prefixWord ++ tailWord_2914998) baseStart_2914998 baseEnd_2914998 := by
    simpa [prefixWord, tailWord_2914998, baseEnd_2914998] using wordTrace_append hprefix tailTrace_2914998
  have hstable : (prefixWord ++ tailWord_2914998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2914998).length < 2 ^ (prefixWord ++ tailWord_2914998).sum := by decide
  have hdescent : baseEnd_2914998 < baseStart_2914998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2914998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915007 : List Nat := [1, 1, 2, 2, 2, 4, 2, 8]
def baseStart_2915007 : Nat := 118140960795 + 2915007 * 2 ^ 59
def prefixEnd_2915007 : Nat := 4983230072969 + 3 ^ 40 * 2915007 * 2
def baseEnd_2915007 : Nat := 110874052016354204104195

theorem tailTrace_2915007 : CollatzResearch.WordTrace tailWord_2915007 prefixEnd_2915007 110874052016354204104195 := by
  unfold tailWord_2915007
  simp only [CollatzResearch.WordTrace]
  refine ⟨106319039750434957405359275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70879359833623304936906183 106319039750434957405359275)
  ·
    refine ⟨159478559625652436108038913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106319039750434957405359275 159478559625652436108038913)
    ·
      refine ⟨119608919719239327081029185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159478559625652436108038913 119608919719239327081029185)
      ·
        refine ⟨89706689789429495310771889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119608919719239327081029185 89706689789429495310771889)
        ·
          refine ⟨67280017342072121483078917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89706689789429495310771889 67280017342072121483078917)
          ·
            refine ⟨12615003251638522778077297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67280017342072121483078917 12615003251638522778077297)
            ·
              refine ⟨9461252438728892083557973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12615003251638522778077297 9461252438728892083557973)
              ·
                refine ⟨110874052016354204104195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9461252438728892083557973 110874052016354204104195)
                ·
                  rfl

theorem cell22_2915007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 8].length) (baseStart_2915007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915007 prefixEnd_2915007 := by exact prefixLift 2915007
  have htrace : WordTrace (prefixWord ++ tailWord_2915007) baseStart_2915007 baseEnd_2915007 := by
    simpa [prefixWord, tailWord_2915007, baseEnd_2915007] using wordTrace_append hprefix tailTrace_2915007
  have hstable : (prefixWord ++ tailWord_2915007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915007).length < 2 ^ (prefixWord ++ tailWord_2915007).sum := by decide
  have hdescent : baseEnd_2915007 < baseStart_2915007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915052 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 9]
def baseStart_2915052 : Nat := 118140960795 + 2915052 * 2 ^ 59
def prefixEnd_2915052 : Nat := 4983230072969 + 3 ^ 40 * 2915052 * 2
def baseEnd_2915052 : Nat := 332627290855607573187539

theorem tailTrace_2915052 : CollatzResearch.WordTrace tailWord_2915052 prefixEnd_2915052 332627290855607573187539 := by
  unfold tailWord_2915052
  simp only [CollatzResearch.WordTrace]
  refine ⟨53160340517635965045373705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70880454023514620060498273 53160340517635965045373705)
  ·
    refine ⟨39870255388226973784030279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53160340517635965045373705 39870255388226973784030279)
    ·
      refine ⟨59805383082340460676045419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39870255388226973784030279 59805383082340460676045419)
      ·
        refine ⟨89708074623510691014068129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59805383082340460676045419 89708074623510691014068129)
        ·
          refine ⟨67281055967633018260551097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89708074623510691014068129 67281055967633018260551097)
          ·
            refine ⟨50460791975724763695413323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67281055967633018260551097 50460791975724763695413323)
            ·
              refine ⟨75691187963587145543119985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50460791975724763695413323 75691187963587145543119985)
              ·
                refine ⟨56768390972690359157339989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75691187963587145543119985 56768390972690359157339989)
                ·
                  refine ⟨332627290855607573187539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56768390972690359157339989 332627290855607573187539)
                  ·
                    rfl

theorem cell22_2915052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_2915052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915052 prefixEnd_2915052 := by exact prefixLift 2915052
  have htrace : WordTrace (prefixWord ++ tailWord_2915052) baseStart_2915052 baseEnd_2915052 := by
    simpa [prefixWord, tailWord_2915052, baseEnd_2915052] using wordTrace_append hprefix tailTrace_2915052
  have hstable : (prefixWord ++ tailWord_2915052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915052).length < 2 ^ (prefixWord ++ tailWord_2915052).sum := by decide
  have hdescent : baseEnd_2915052 < baseStart_2915052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915090 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2915090 : Nat := 118140960795 + 2915090 * 2 ^ 59
def prefixEnd_2915090 : Nat := 4983230072969 + 3 ^ 40 * 2915090 * 2
def baseEnd_2915090 : Nat := 997894880743403287112501

theorem tailTrace_2915090 : CollatzResearch.WordTrace tailWord_2915090 prefixEnd_2915090 997894880743403287112501 := by
  unfold tailWord_2915090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26580516752283565645157681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70881378006089508387087149 26580516752283565645157681)
  ·
    refine ⟨19935387564212674233868261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26580516752283565645157681 19935387564212674233868261)
    ·
      refine ⟨3737885168289876418850299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19935387564212674233868261 3737885168289876418850299)
      ·
        refine ⟨5606827752434814628275449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3737885168289876418850299 5606827752434814628275449)
        ·
          refine ⟨4205120814326110971206587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5606827752434814628275449 4205120814326110971206587)
          ·
            refine ⟨6307681221489166456809881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205120814326110971206587 6307681221489166456809881)
            ·
              refine ⟨4730760916116874842607411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6307681221489166456809881 4730760916116874842607411)
              ·
                refine ⟨7096141374175312263911117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730760916116874842607411 7096141374175312263911117)
                ·
                  refine ⟨2661053015315742098966669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7096141374175312263911117 2661053015315742098966669)
                  ·
                    refine ⟨997894880743403287112501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661053015315742098966669 997894880743403287112501)
                    ·
                      rfl

theorem cell22_2915090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2915090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915090 prefixEnd_2915090 := by exact prefixLift 2915090
  have htrace : WordTrace (prefixWord ++ tailWord_2915090) baseStart_2915090 baseEnd_2915090 := by
    simpa [prefixWord, tailWord_2915090, baseEnd_2915090] using wordTrace_append hprefix tailTrace_2915090
  have hstable : (prefixWord ++ tailWord_2915090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915090).length < 2 ^ (prefixWord ++ tailWord_2915090).sum := by decide
  have hdescent : baseEnd_2915090 < baseStart_2915090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915116 : List Nat := [2, 2, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_2915116 : Nat := 118140960795 + 2915116 * 2 ^ 59
def prefixEnd_2915116 : Nat := 4983230072969 + 3 ^ 40 * 2915116 * 2
def baseEnd_2915116 : Nat := 997903781074747885962421

theorem tailTrace_2915116 : CollatzResearch.WordTrace tailWord_2915116 prefixEnd_2915116 997903781074747885962421 := by
  unfold tailWord_2915116
  simp only [CollatzResearch.WordTrace]
  refine ⟨53161507653520034510538601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70882010204693379347384801 53161507653520034510538601)
  ·
    refine ⟨39871130740140025882903951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53161507653520034510538601 39871130740140025882903951)
    ·
      refine ⟨59806696110210038824355927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39871130740140025882903951 59806696110210038824355927)
      ·
        refine ⟨89710044165315058236533891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59806696110210038824355927 89710044165315058236533891)
        ·
          refine ⟨134565066247972587354800837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89710044165315058236533891 134565066247972587354800837)
          ·
            refine ⟨25230949921494860129025157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134565066247972587354800837 25230949921494860129025157)
            ·
              refine ⟨4730803110280286274192217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25230949921494860129025157 4730803110280286274192217)
              ·
                refine ⟨3548102332710214705644163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4730803110280286274192217 3548102332710214705644163)
                ·
                  refine ⟨5322153499065322058466245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548102332710214705644163 5322153499065322058466245)
                  ·
                    refine ⟨997903781074747885962421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322153499065322058466245 997903781074747885962421)
                    ·
                      rfl

theorem cell22_2915116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_2915116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915116 prefixEnd_2915116 := by exact prefixLift 2915116
  have htrace : WordTrace (prefixWord ++ tailWord_2915116) baseStart_2915116 baseEnd_2915116 := by
    simpa [prefixWord, tailWord_2915116, baseEnd_2915116] using wordTrace_append hprefix tailTrace_2915116
  have hstable : (prefixWord ++ tailWord_2915116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915116).length < 2 ^ (prefixWord ++ tailWord_2915116).sum := by decide
  have hdescent : baseEnd_2915116 < baseStart_2915116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915124 : List Nat := [2, 5, 1, 1, 4, 1, 1, 3, 1, 3]
def baseStart_2915124 : Nat := 118140960795 + 2915124 * 2 ^ 59
def prefixEnd_2915124 : Nat := 4983230072969 + 3 ^ 40 * 2915124 * 2
def baseEnd_2915124 : Nat := 997906519638238531762397

theorem tailTrace_2915124 : CollatzResearch.WordTrace tailWord_2915124 prefixEnd_2915124 997906519638238531762397 := by
  unfold tailWord_2915124
  simp only [CollatzResearch.WordTrace]
  refine ⟨53161653545505543193684213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70882204727340724258245617 53161653545505543193684213)
  ·
    refine ⟨4983905019891144674407895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53161653545505543193684213 4983905019891144674407895)
    ·
      refine ⟨7475857529836717011611843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4983905019891144674407895 7475857529836717011611843)
      ·
        refine ⟨11213786294755075517417765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475857529836717011611843 11213786294755075517417765)
        ·
          refine ⟨2102584930266576659515831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11213786294755075517417765 2102584930266576659515831)
          ·
            refine ⟨3153877395399864989273747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102584930266576659515831 3153877395399864989273747)
            ·
              refine ⟨4730816093099797483910621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3153877395399864989273747 4730816093099797483910621)
              ·
                refine ⟨1774056034912424056466483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4730816093099797483910621 1774056034912424056466483)
                ·
                  refine ⟨2661084052368636084699725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774056034912424056466483 2661084052368636084699725)
                  ·
                    refine ⟨997906519638238531762397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661084052368636084699725 997906519638238531762397)
                    ·
                      rfl

theorem cell22_2915124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_2915124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915124 prefixEnd_2915124 := by exact prefixLift 2915124
  have htrace : WordTrace (prefixWord ++ tailWord_2915124) baseStart_2915124 baseEnd_2915124 := by
    simpa [prefixWord, tailWord_2915124, baseEnd_2915124] using wordTrace_append hprefix tailTrace_2915124
  have hstable : (prefixWord ++ tailWord_2915124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915124).length < 2 ^ (prefixWord ++ tailWord_2915124).sum := by decide
  have hdescent : baseEnd_2915124 < baseStart_2915124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915159 : List Nat := [1, 1, 3, 2, 4, 1, 1, 9]
def baseStart_2915159 : Nat := 118140960795 + 2915159 * 2 ^ 59
def prefixEnd_2915159 : Nat := 4983230072969 + 3 ^ 40 * 2915159 * 2
def baseEnd_2915159 : Nat := 110879833428167789681921

theorem tailTrace_2915159 : CollatzResearch.WordTrace tailWord_2915159 prefixEnd_2915159 110879833428167789681921 := by
  unfold tailWord_2915159
  simp only [CollatzResearch.WordTrace]
  refine ⟨106324583645884287364892531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70883055763922858243261687 106324583645884287364892531)
  ·
    refine ⟨159486875468826431047338797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106324583645884287364892531 159486875468826431047338797)
    ·
      refine ⟨59807578300809911642752049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159486875468826431047338797 59807578300809911642752049)
      ·
        refine ⟨44855683725607433732064037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59807578300809911642752049 44855683725607433732064037)
        ·
          refine ⟨8410440698551393824762007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44855683725607433732064037 8410440698551393824762007)
          ·
            refine ⟨12615661047827090737143011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8410440698551393824762007 12615661047827090737143011)
            ·
              refine ⟨18923491571740636105714517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12615661047827090737143011 18923491571740636105714517)
              ·
                refine ⟨110879833428167789681921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18923491571740636105714517 110879833428167789681921)
                ·
                  rfl

theorem cell22_2915159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 9].length) (baseStart_2915159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915159 prefixEnd_2915159 := by exact prefixLift 2915159
  have htrace : WordTrace (prefixWord ++ tailWord_2915159) baseStart_2915159 baseEnd_2915159 := by
    simpa [prefixWord, tailWord_2915159, baseEnd_2915159] using wordTrace_append hprefix tailTrace_2915159
  have hstable : (prefixWord ++ tailWord_2915159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915159).length < 2 ^ (prefixWord ++ tailWord_2915159).sum := by decide
  have hdescent : baseEnd_2915159 < baseStart_2915159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915221 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 5]
def baseStart_2915221 : Nat := 118140960795 + 2915221 * 2 ^ 59
def prefixEnd_2915221 : Nat := 4983230072969 + 3 ^ 40 * 2915221 * 2
def baseEnd_2915221 : Nat := 332646574906854204029033

theorem tailTrace_2915221 : CollatzResearch.WordTrace tailWord_2915221 prefixEnd_2915221 332646574906854204029033 := by
  unfold tailWord_2915221
  simp only [CollatzResearch.WordTrace]
  refine ⟨106326844971659671953649517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70884563314439781302433011 106326844971659671953649517)
  ·
    refine ⟨39872566864372376982618569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106326844971659671953649517 39872566864372376982618569)
    ·
      refine ⟨29904425148279282736963927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39872566864372376982618569 29904425148279282736963927)
      ·
        refine ⟨44856637722418924105445891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29904425148279282736963927 44856637722418924105445891)
        ·
          refine ⟨67284956583628386158168837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44856637722418924105445891 67284956583628386158168837)
          ·
            refine ⟨12615929359430322404656657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67284956583628386158168837 12615929359430322404656657)
            ·
              refine ⟨9461947019572741803492493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12615929359430322404656657 9461947019572741803492493)
              ·
                refine ⟨3548230132339778176309685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9461947019572741803492493 3548230132339778176309685)
                ·
                  refine ⟨332646574906854204029033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3548230132339778176309685 332646574906854204029033)
                  ·
                    rfl

theorem cell22_2915221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_2915221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915221 prefixEnd_2915221 := by exact prefixLift 2915221
  have htrace : WordTrace (prefixWord ++ tailWord_2915221) baseStart_2915221 baseEnd_2915221 := by
    simpa [prefixWord, tailWord_2915221, baseEnd_2915221] using wordTrace_append hprefix tailTrace_2915221
  have hstable : (prefixWord ++ tailWord_2915221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915221).length < 2 ^ (prefixWord ++ tailWord_2915221).sum := by decide
  have hdescent : baseEnd_2915221 < baseStart_2915221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915285 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 1, 4]
def baseStart_2915285 : Nat := 118140960795 + 2915285 * 2 ^ 59
def prefixEnd_2915285 : Nat := 4983230072969 + 3 ^ 40 * 2915285 * 2
def baseEnd_2915285 : Nat := 997961633228487778486903

theorem tailTrace_2915285 : CollatzResearch.WordTrace tailWord_2915285 prefixEnd_2915285 997961633228487778486903 := by
  unfold tailWord_2915285
  simp only [CollatzResearch.WordTrace]
  refine ⟨106329179243427810883979309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70886119495618540589319539 106329179243427810883979309)
  ·
    refine ⟨39873442216285429081492241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106329179243427810883979309 39873442216285429081492241)
    ·
      refine ⟨29905081662214071811119181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39873442216285429081492241 29905081662214071811119181)
      ·
        refine ⟨11214405623330276929169693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29905081662214071811119181 11214405623330276929169693)
        ·
          refine ⟨4205402108748853848438635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11214405623330276929169693 4205402108748853848438635)
          ·
            refine ⟨6308103163123280772657953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205402108748853848438635 6308103163123280772657953)
            ·
              refine ⟨4731077372342460579493465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6308103163123280772657953 4731077372342460579493465)
              ·
                refine ⟨3548308029256845434620099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4731077372342460579493465 3548308029256845434620099)
                ·
                  refine ⟨5322462043885268151930149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548308029256845434620099 5322462043885268151930149)
                  ·
                    refine ⟨997961633228487778486903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322462043885268151930149 997961633228487778486903)
                    ·
                      rfl

theorem cell22_2915285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_2915285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915285 prefixEnd_2915285 := by exact prefixLift 2915285
  have htrace : WordTrace (prefixWord ++ tailWord_2915285) baseStart_2915285 baseEnd_2915285 := by
    simpa [prefixWord, tailWord_2915285, baseEnd_2915285] using wordTrace_append hprefix tailTrace_2915285
  have hstable : (prefixWord ++ tailWord_2915285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915285).length < 2 ^ (prefixWord ++ tailWord_2915285).sum := by decide
  have hdescent : baseEnd_2915285 < baseStart_2915285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915311 : List Nat := [1, 1, 2, 1, 4, 5, 8]
def baseStart_2915311 : Nat := 118140960795 + 2915311 * 2 ^ 59
def prefixEnd_2915311 : Nat := 4983230072969 + 3 ^ 40 * 2915311 * 2
def baseEnd_2915311 : Nat := 36961871613327125086549

theorem tailTrace_2915311 : CollatzResearch.WordTrace tailWord_2915311 prefixEnd_2915311 36961871613327125086549 := by
  unfold tailWord_2915311
  simp only [CollatzResearch.WordTrace]
  refine ⟨106330127541333617324425787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70886751694222411549617191 106330127541333617324425787)
  ·
    refine ⟨159495191312000425986638681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106330127541333617324425787 159495191312000425986638681)
    ·
      refine ⟨119621393484000319489979011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159495191312000425986638681 119621393484000319489979011)
      ·
        refine ⟨179432090226000479234968517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119621393484000319489979011 179432090226000479234968517)
        ·
          refine ⟨33643516917375089856556597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179432090226000479234968517 33643516917375089856556597)
          ·
            refine ⟨3154079711003914674052181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33643516917375089856556597 3154079711003914674052181)
            ·
              refine ⟨36961871613327125086549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3154079711003914674052181 36961871613327125086549)
              ·
                rfl

theorem cell22_2915311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 8].length) (baseStart_2915311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915311 prefixEnd_2915311 := by exact prefixLift 2915311
  have htrace : WordTrace (prefixWord ++ tailWord_2915311) baseStart_2915311 baseEnd_2915311 := by
    simpa [prefixWord, tailWord_2915311, baseEnd_2915311] using wordTrace_append hprefix tailTrace_2915311
  have hstable : (prefixWord ++ tailWord_2915311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915311).length < 2 ^ (prefixWord ++ tailWord_2915311).sum := by decide
  have hdescent : baseEnd_2915311 < baseStart_2915311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915313 : List Nat := [1, 2, 2, 2, 4, 2, 1, 2, 2, 4]
def baseStart_2915313 : Nat := 118140960795 + 2915313 * 2 ^ 59
def prefixEnd_2915313 : Nat := 4983230072969 + 3 ^ 40 * 2915313 * 2
def baseEnd_2915313 : Nat := 997971218200705038786817

theorem tailTrace_2915313 : CollatzResearch.WordTrace tailWord_2915313 prefixEnd_2915313 997971218200705038786817 := by
  unfold tailWord_2915313
  simp only [CollatzResearch.WordTrace]
  refine ⟨106330200487326371665998593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70886800324884247777332395 106330200487326371665998593)
  ·
    refine ⟨79747650365494778749498945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106330200487326371665998593 79747650365494778749498945)
    ·
      refine ⟨59810737774121084062124209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79747650365494778749498945 59810737774121084062124209)
      ·
        refine ⟨44858053330590813046593157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59810737774121084062124209 44858053330590813046593157)
        ·
          refine ⟨8410884999485777446236217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44858053330590813046593157 8410884999485777446236217)
          ·
            refine ⟨6308163749614333084677163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8410884999485777446236217 6308163749614333084677163)
            ·
              refine ⟨9462245624421499627015745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308163749614333084677163 9462245624421499627015745)
              ·
                refine ⟨7096684218316124720261809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462245624421499627015745 7096684218316124720261809)
                ·
                  refine ⟨5322513163737093540196357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096684218316124720261809 5322513163737093540196357)
                  ·
                    refine ⟨997971218200705038786817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322513163737093540196357 997971218200705038786817)
                    ·
                      rfl

theorem cell22_2915313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_2915313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915313 prefixEnd_2915313 := by exact prefixLift 2915313
  have htrace : WordTrace (prefixWord ++ tailWord_2915313) baseStart_2915313 baseEnd_2915313 := by
    simpa [prefixWord, tailWord_2915313, baseEnd_2915313] using wordTrace_append hprefix tailTrace_2915313
  have hstable : (prefixWord ++ tailWord_2915313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915313).length < 2 ^ (prefixWord ++ tailWord_2915313).sum := by decide
  have hdescent : baseEnd_2915313 < baseStart_2915313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915317 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 6]
def baseStart_2915317 : Nat := 118140960795 + 2915317 * 2 ^ 59
def prefixEnd_2915317 : Nat := 4983230072969 + 3 ^ 40 * 2915317 * 2
def baseEnd_2915317 : Nat := 332657529160816787228935

theorem tailTrace_2915317 : CollatzResearch.WordTrace tailWord_2915317 prefixEnd_2915317 332657529160816787228935 := by
  unfold tailWord_2915317
  simp only [CollatzResearch.WordTrace]
  refine ⟨106330346379311880349144205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70886897586207920232762803 106330346379311880349144205)
  ·
    refine ⟨39873879892241955130929077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106330346379311880349144205 39873879892241955130929077)
    ·
      refine ⟨3738176239897683293524601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39873879892241955130929077 3738176239897683293524601)
      ·
        refine ⟨2803632179923262470143451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3738176239897683293524601 2803632179923262470143451)
        ·
          refine ⟨4205448269884893705215177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803632179923262470143451 4205448269884893705215177)
          ·
            refine ⟨3154086202413670278911383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4205448269884893705215177 3154086202413670278911383)
            ·
              refine ⟨4731129303620505418367075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154086202413670278911383 4731129303620505418367075)
              ·
                refine ⟨7096693955430758127550613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731129303620505418367075 7096693955430758127550613)
                ·
                  refine ⟨332657529160816787228935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7096693955430758127550613 332657529160816787228935)
                  ·
                    rfl

theorem cell22_2915317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 6].length) (baseStart_2915317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915317 prefixEnd_2915317 := by exact prefixLift 2915317
  have htrace : WordTrace (prefixWord ++ tailWord_2915317) baseStart_2915317 baseEnd_2915317 := by
    simpa [prefixWord, tailWord_2915317, baseEnd_2915317] using wordTrace_append hprefix tailTrace_2915317
  have hstable : (prefixWord ++ tailWord_2915317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915317).length < 2 ^ (prefixWord ++ tailWord_2915317).sum := by decide
  have hdescent : baseEnd_2915317 < baseStart_2915317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915371 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 2, 5]
def baseStart_2915371 : Nat := 118140960795 + 2915371 * 2 ^ 59
def prefixEnd_2915371 : Nat := 4983230072969 + 3 ^ 40 * 2915371 * 2
def baseEnd_2915371 : Nat := 997991072786012220836639

theorem tailTrace_2915371 : CollatzResearch.WordTrace tailWord_2915371 prefixEnd_2915371 997991072786012220836639 := by
  unfold tailWord_2915371
  simp only [CollatzResearch.WordTrace]
  refine ⟨106332315921116247571609967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70888210614077498381073311 106332315921116247571609967)
  ·
    refine ⟨159498473881674371357414951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106332315921116247571609967 159498473881674371357414951)
    ·
      refine ⟨239247710822511557036122427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159498473881674371357414951 239247710822511557036122427)
      ·
        refine ⟨358871566233767335554183641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239247710822511557036122427 358871566233767335554183641)
        ·
          refine ⟨269153674675325501665637731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 358871566233767335554183641 269153674675325501665637731)
          ·
            refine ⟨403730512012988252498456597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269153674675325501665637731 403730512012988252498456597)
            ·
              refine ⟨18924867750608824335865153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 403730512012988252498456597 18924867750608824335865153)
              ·
                refine ⟨14193650812956618251898865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18924867750608824335865153 14193650812956618251898865)
                ·
                  refine ⟨10645238109717463688924149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14193650812956618251898865 10645238109717463688924149)
                  ·
                    refine ⟨997991072786012220836639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10645238109717463688924149 997991072786012220836639)
                    ·
                      rfl

theorem cell22_2915371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_2915371 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915371 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915371 prefixEnd_2915371 := by exact prefixLift 2915371
  have htrace : WordTrace (prefixWord ++ tailWord_2915371) baseStart_2915371 baseEnd_2915371 := by
    simpa [prefixWord, tailWord_2915371, baseEnd_2915371] using wordTrace_append hprefix tailTrace_2915371
  have hstable : (prefixWord ++ tailWord_2915371).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915371).length < 2 ^ (prefixWord ++ tailWord_2915371).sum := by decide
  have hdescent : baseEnd_2915371 < baseStart_2915371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915388 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2915388 : Nat := 118140960795 + 2915388 * 2 ^ 59
def prefixEnd_2915388 : Nat := 4983230072969 + 3 ^ 40 * 2915388 * 2
def baseEnd_2915388 : Nat := 997996892233429843161587

theorem tailTrace_2915388 : CollatzResearch.WordTrace tailWord_2915388 prefixEnd_2915388 997996892233429843161587 := by
  unfold tailWord_2915388
  simp only [CollatzResearch.WordTrace]
  refine ⟨53166467981027329737489409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70888623974703106316652545 53166467981027329737489409)
  ·
    refine ⟨39874850985770497303117057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53166467981027329737489409 39874850985770497303117057)
    ·
      refine ⟨29906138239327872977337793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39874850985770497303117057 29906138239327872977337793)
      ·
        refine ⟨22429603679495904733003345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29906138239327872977337793 22429603679495904733003345)
        ·
          refine ⟨16822202759621928549752509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22429603679495904733003345 16822202759621928549752509)
          ·
            refine ⟨6308326034858223206157191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16822202759621928549752509 6308326034858223206157191)
            ·
              refine ⟨9462489052287334809235787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308326034858223206157191 9462489052287334809235787)
              ·
                refine ⟨14193733578431002213853681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9462489052287334809235787 14193733578431002213853681)
                ·
                  refine ⟨10645300183823251660390261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14193733578431002213853681 10645300183823251660390261)
                  ·
                    refine ⟨997996892233429843161587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10645300183823251660390261 997996892233429843161587)
                    ·
                      rfl

theorem cell22_2915388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2915388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915388 prefixEnd_2915388 := by exact prefixLift 2915388
  have htrace : WordTrace (prefixWord ++ tailWord_2915388) baseStart_2915388 baseEnd_2915388 := by
    simpa [prefixWord, tailWord_2915388, baseEnd_2915388] using wordTrace_append hprefix tailTrace_2915388
  have hstable : (prefixWord ++ tailWord_2915388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915388).length < 2 ^ (prefixWord ++ tailWord_2915388).sum := by decide
  have hdescent : baseEnd_2915388 < baseStart_2915388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915390 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2915390 : Nat := 118140960795 + 2915390 * 2 ^ 59
def prefixEnd_2915390 : Nat := 4983230072969 + 3 ^ 40 * 2915390 * 2
def baseEnd_2915390 : Nat := 332665858958100834870527

theorem tailTrace_2915390 : CollatzResearch.WordTrace tailWord_2915390 prefixEnd_2915390 332665858958100834870527 := by
  unfold tailWord_2915390
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291626113505926727068953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70888672605364942544367749 13291626113505926727068953)
  ·
    refine ⟨9968719585129445045301715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13291626113505926727068953 9968719585129445045301715)
    ·
      refine ⟨14953079377694167567952573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968719585129445045301715 14953079377694167567952573)
      ·
        refine ⟨5607404766635312837982215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14953079377694167567952573 5607404766635312837982215)
        ·
          refine ⟨8411107149952969256973323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607404766635312837982215 8411107149952969256973323)
          ·
            refine ⟨12616660724929453885459985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411107149952969256973323 12616660724929453885459985)
            ·
              refine ⟨9462495543697090414094989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12616660724929453885459985 9462495543697090414094989)
              ·
                refine ⟨3548435828886408905285621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9462495543697090414094989 3548435828886408905285621)
                ·
                  refine ⟨332665858958100834870527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3548435828886408905285621 332665858958100834870527)
                  ·
                    rfl

theorem cell22_2915390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2915390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915390 prefixEnd_2915390 := by exact prefixLift 2915390
  have htrace : WordTrace (prefixWord ++ tailWord_2915390) baseStart_2915390 baseEnd_2915390 := by
    simpa [prefixWord, tailWord_2915390, baseEnd_2915390] using wordTrace_append hprefix tailTrace_2915390
  have hstable : (prefixWord ++ tailWord_2915390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915390).length < 2 ^ (prefixWord ++ tailWord_2915390).sum := by decide
  have hdescent : baseEnd_2915390 < baseStart_2915390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915420 : List Nat := [2, 2, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2915420 : Nat := 118140960795 + 2915420 * 2 ^ 59
def prefixEnd_2915420 : Nat := 4983230072969 + 3 ^ 40 * 2915420 * 2
def baseEnd_2915420 : Nat := 998007846487392426361489

theorem tailTrace_2915420 : CollatzResearch.WordTrace tailWord_2915420 prefixEnd_2915420 998007846487392426361489 := by
  unfold tailWord_2915420
  simp only [CollatzResearch.WordTrace]
  refine ⟨53167051548969364470071857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70889402065292485960095809 53167051548969364470071857)
  ·
    refine ⟨39875288661727023352553893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53167051548969364470071857 39875288661727023352553893)
    ·
      refine ⟨7476616624073816878603855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39875288661727023352553893 7476616624073816878603855)
      ·
        refine ⟨11214924936110725317905783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476616624073816878603855 11214924936110725317905783)
        ·
          refine ⟨16822387404166087976858675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11214924936110725317905783 16822387404166087976858675)
          ·
            refine ⟨25233581106249131965288013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16822387404166087976858675 25233581106249131965288013)
            ·
              refine ⟨9462592914843424486983005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25233581106249131965288013 9462592914843424486983005)
              ·
                refine ⟨3548472343066284182618627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9462592914843424486983005 3548472343066284182618627)
                ·
                  refine ⟨5322708514599426273927941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3548472343066284182618627 5322708514599426273927941)
                  ·
                    refine ⟨998007846487392426361489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322708514599426273927941 998007846487392426361489)
                    ·
                      rfl

theorem cell22_2915420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2915420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915420 prefixEnd_2915420 := by exact prefixLift 2915420
  have htrace : WordTrace (prefixWord ++ tailWord_2915420) baseStart_2915420 baseEnd_2915420 := by
    simpa [prefixWord, tailWord_2915420, baseEnd_2915420] using wordTrace_append hprefix tailTrace_2915420
  have hstable : (prefixWord ++ tailWord_2915420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915420).length < 2 ^ (prefixWord ++ tailWord_2915420).sum := by decide
  have hdescent : baseEnd_2915420 < baseStart_2915420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915422 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 2, 5]
def baseStart_2915422 : Nat := 118140960795 + 2915422 * 2 ^ 59
def prefixEnd_2915422 : Nat := 4983230072969 + 3 ^ 40 * 2915422 * 2
def baseEnd_2915422 : Nat := 998008531128265087811483

theorem tailTrace_2915422 : CollatzResearch.WordTrace tailWord_2915422 prefixEnd_2915422 998008531128265087811483 := by
  unfold tailWord_2915422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13291772005491435410214565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70889450695954322187811013 13291772005491435410214565)
  ·
    refine ⟨2492207251029644139415231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13291772005491435410214565 2492207251029644139415231)
    ·
      refine ⟨3738310876544466209122847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2492207251029644139415231 3738310876544466209122847)
      ·
        refine ⟨5607466314816699313684271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738310876544466209122847 5607466314816699313684271)
        ·
          refine ⟨8411199472225048970526407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607466314816699313684271 8411199472225048970526407)
          ·
            refine ⟨12616799208337573455789611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411199472225048970526407 12616799208337573455789611)
            ·
              refine ⟨18925198812506360183684417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12616799208337573455789611 18925198812506360183684417)
              ·
                refine ⟨14193899109379770137763313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18925198812506360183684417 14193899109379770137763313)
                ·
                  refine ⟨10645424332034827603322485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14193899109379770137763313 10645424332034827603322485)
                  ·
                    refine ⟨998008531128265087811483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10645424332034827603322485 998008531128265087811483)
                    ·
                      rfl

theorem cell22_2915422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_2915422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915422 prefixEnd_2915422 := by exact prefixLift 2915422
  have htrace : WordTrace (prefixWord ++ tailWord_2915422) baseStart_2915422 baseEnd_2915422 := by
    simpa [prefixWord, tailWord_2915422, baseEnd_2915422] using wordTrace_append hprefix tailTrace_2915422
  have hstable : (prefixWord ++ tailWord_2915422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915422).length < 2 ^ (prefixWord ++ tailWord_2915422).sum := by decide
  have hdescent : baseEnd_2915422 < baseStart_2915422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915501 : List Nat := [1, 5, 2, 1, 3, 2, 2, 1, 2, 3]
def baseStart_2915501 : Nat := 118140960795 + 2915501 * 2 ^ 59
def prefixEnd_2915501 : Nat := 4983230072969 + 3 ^ 40 * 2915501 * 2
def baseEnd_2915501 : Nat := 998035574442735215086241

theorem tailTrace_2915501 : CollatzResearch.WordTrace tailWord_2915501 prefixEnd_2915501 998035574442735215086241 := by
  unfold tailWord_2915501
  simp only [CollatzResearch.WordTrace]
  refine ⟨106337057410645279773842357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70891371607096853182561571 106337057410645279773842357)
  ·
    refine ⟨9969099132247994978797721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106337057410645279773842357 9969099132247994978797721)
    ·
      refine ⟨7476824349185996234098291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9969099132247994978797721 7476824349185996234098291)
      ·
        refine ⟨11215236523778994351147437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476824349185996234098291 11215236523778994351147437)
        ·
          refine ⟨4205713696417122881680289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11215236523778994351147437 4205713696417122881680289)
          ·
            refine ⟨3154285272312842161260217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4205713696417122881680289 3154285272312842161260217)
            ·
              refine ⟨2365713954234631620945163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3154285272312842161260217 2365713954234631620945163)
              ·
                refine ⟨3548570931351947431417745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365713954234631620945163 3548570931351947431417745)
                ·
                  refine ⟨2661428198513960573563309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548570931351947431417745 2661428198513960573563309)
                  ·
                    refine ⟨998035574442735215086241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661428198513960573563309 998035574442735215086241)
                    ·
                      rfl

theorem cell22_2915501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_2915501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915501 prefixEnd_2915501 := by exact prefixLift 2915501
  have htrace : WordTrace (prefixWord ++ tailWord_2915501) baseStart_2915501 baseEnd_2915501 := by
    simpa [prefixWord, tailWord_2915501, baseEnd_2915501] using wordTrace_append hprefix tailTrace_2915501
  have hstable : (prefixWord ++ tailWord_2915501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915501).length < 2 ^ (prefixWord ++ tailWord_2915501).sum := by decide
  have hdescent : baseEnd_2915501 < baseStart_2915501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915585 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 1, 5]
def baseStart_2915585 : Nat := 118140960795 + 2915585 * 2 ^ 59
def prefixEnd_2915585 : Nat := 4983230072969 + 3 ^ 40 * 2915585 * 2
def baseEnd_2915585 : Nat := 998064329359386995985983

theorem tailTrace_2915585 : CollatzResearch.WordTrace tailWord_2915585 prefixEnd_2915585 998064329359386995985983 := by
  unfold tailWord_2915585
  simp only [CollatzResearch.WordTrace]
  refine ⟨106340121142340962119900209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70893414094893974746600139 106340121142340962119900209)
  ·
    refine ⟨79755090856755721589925157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106340121142340962119900209 79755090856755721589925157)
    ·
      refine ⟨14954079535641697798110967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79755090856755721589925157 14954079535641697798110967)
      ·
        refine ⟨22431119303462546697166451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14954079535641697798110967 22431119303462546697166451)
        ·
          refine ⟨33646678955193820045749677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22431119303462546697166451 33646678955193820045749677)
          ·
            refine ⟨12617504608197682517156129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33646678955193820045749677 12617504608197682517156129)
            ·
              refine ⟨9463128456148261887867097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12617504608197682517156129 9463128456148261887867097)
              ·
                refine ⟨7097346342111196415900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463128456148261887867097 7097346342111196415900323)
                ·
                  refine ⟨10646019513166794623850485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097346342111196415900323 10646019513166794623850485)
                  ·
                    refine ⟨998064329359386995985983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10646019513166794623850485 998064329359386995985983)
                    ·
                      rfl

theorem cell22_2915585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_2915585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915585 prefixEnd_2915585 := by exact prefixLift 2915585
  have htrace : WordTrace (prefixWord ++ tailWord_2915585) baseStart_2915585 baseEnd_2915585 := by
    simpa [prefixWord, tailWord_2915585, baseEnd_2915585] using wordTrace_append hprefix tailTrace_2915585
  have hstable : (prefixWord ++ tailWord_2915585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915585).length < 2 ^ (prefixWord ++ tailWord_2915585).sum := by decide
  have hdescent : baseEnd_2915585 < baseStart_2915585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915587 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 4]
def baseStart_2915587 : Nat := 118140960795 + 2915587 * 2 ^ 59
def prefixEnd_2915587 : Nat := 4983230072969 + 3 ^ 40 * 2915587 * 2
def baseEnd_2915587 : Nat := 332688338000086552478659

theorem tailTrace_2915587 : CollatzResearch.WordTrace tailWord_2915587 prefixEnd_2915587 332688338000086552478659 := by
  unfold tailWord_2915587
  simp only [CollatzResearch.WordTrace]
  refine ⟨106340194088333716461473015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70893462725555810974315343 106340194088333716461473015)
  ·
    refine ⟨159510291132500574692209523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106340194088333716461473015 159510291132500574692209523)
    ·
      refine ⟨239265436698750862038314285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159510291132500574692209523 239265436698750862038314285)
      ·
        refine ⟨89724538762031573264367857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 239265436698750862038314285 89724538762031573264367857)
        ·
          refine ⟨67293404071523679948275893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89724538762031573264367857 67293404071523679948275893)
          ·
            refine ⟨6308756631705344995150865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67293404071523679948275893 6308756631705344995150865)
            ·
              refine ⟨4731567473779008746363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6308756631705344995150865 4731567473779008746363149)
              ·
                refine ⟨1774337802667128279886181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731567473779008746363149 1774337802667128279886181)
                ·
                  refine ⟨332688338000086552478659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774337802667128279886181 332688338000086552478659)
                  ·
                    rfl

theorem cell22_2915587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 4].length) (baseStart_2915587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915587 prefixEnd_2915587 := by exact prefixLift 2915587
  have htrace : WordTrace (prefixWord ++ tailWord_2915587) baseStart_2915587 baseEnd_2915587 := by
    simpa [prefixWord, tailWord_2915587, baseEnd_2915587] using wordTrace_append hprefix tailTrace_2915587
  have hstable : (prefixWord ++ tailWord_2915587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915587).length < 2 ^ (prefixWord ++ tailWord_2915587).sum := by decide
  have hdescent : baseEnd_2915587 < baseStart_2915587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915619 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 2, 3]
def baseStart_2915619 : Nat := 118140960795 + 2915619 * 2 ^ 59
def prefixEnd_2915619 : Nat := 4983230072969 + 3 ^ 40 * 2915619 * 2
def baseEnd_2915619 : Nat := 998075968254222240635879

theorem tailTrace_2915619 : CollatzResearch.WordTrace tailWord_2915619 prefixEnd_2915619 998075968254222240635879 := by
  unfold tailWord_2915619
  simp only [CollatzResearch.WordTrace]
  refine ⟨106341361224217785926637911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70894240816145190617758607 106341361224217785926637911)
  ·
    refine ⟨159512041836326678889956867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106341361224217785926637911 159512041836326678889956867)
    ·
      refine ⟨239268062754490018334935301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159512041836326678889956867 239268062754490018334935301)
      ·
        refine ⟨44862761766466878437800369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 239268062754490018334935301 44862761766466878437800369)
        ·
          refine ⟨33647071324850158828350277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44862761766466878437800369 33647071324850158828350277)
          ·
            refine ⟨6308825873409404780315677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33647071324850158828350277 6308825873409404780315677)
            ·
              refine ⟨2365809702528526792618379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6308825873409404780315677 2365809702528526792618379)
              ·
                refine ⟨3548714553792790188927569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365809702528526792618379 3548714553792790188927569)
                ·
                  refine ⟨2661535915344592641695677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548714553792790188927569 2661535915344592641695677)
                  ·
                    refine ⟨998075968254222240635879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661535915344592641695677 998075968254222240635879)
                    ·
                      rfl

theorem cell22_2915619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 2, 3].length) (baseStart_2915619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915619 prefixEnd_2915619 := by exact prefixLift 2915619
  have htrace : WordTrace (prefixWord ++ tailWord_2915619) baseStart_2915619 baseEnd_2915619 := by
    simpa [prefixWord, tailWord_2915619, baseEnd_2915619] using wordTrace_append hprefix tailTrace_2915619
  have hstable : (prefixWord ++ tailWord_2915619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915619).length < 2 ^ (prefixWord ++ tailWord_2915619).sum := by decide
  have hdescent : baseEnd_2915619 < baseStart_2915619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915638 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 4]
def baseStart_2915638 : Nat := 118140960795 + 2915638 * 2 ^ 59
def prefixEnd_2915638 : Nat := 4983230072969 + 3 ^ 40 * 2915638 * 2
def baseEnd_2915638 : Nat := 332694157447504174803607

theorem tailTrace_2915638 : CollatzResearch.WordTrace tailWord_2915638 prefixEnd_2915638 332694157447504174803607 := by
  unfold tailWord_2915638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646378388196809510723723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70894702807432634781053045 6646378388196809510723723)
  ·
    refine ⟨9969567582295214266085585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6646378388196809510723723 9969567582295214266085585)
    ·
      refine ⟨7477175686721410699564189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9969567582295214266085585 7477175686721410699564189)
      ·
        refine ⟨2803940882520529012336571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7477175686721410699564189 2803940882520529012336571)
        ·
          refine ⟨4205911323780793518504857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803940882520529012336571 4205911323780793518504857)
          ·
            refine ⟨3154433492835595138878643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4205911323780793518504857 3154433492835595138878643)
            ·
              refine ⟨4731650239253392708317965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154433492835595138878643 4731650239253392708317965)
              ·
                refine ⟨1774368839720022265619237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731650239253392708317965 1774368839720022265619237)
                ·
                  refine ⟨332694157447504174803607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774368839720022265619237 332694157447504174803607)
                  ·
                    rfl

theorem cell22_2915638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_2915638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915638 prefixEnd_2915638 := by exact prefixLift 2915638
  have htrace : WordTrace (prefixWord ++ tailWord_2915638) baseStart_2915638 baseEnd_2915638 := by
    simpa [prefixWord, tailWord_2915638, baseEnd_2915638] using wordTrace_append hprefix tailTrace_2915638
  have hstable : (prefixWord ++ tailWord_2915638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915638).length < 2 ^ (prefixWord ++ tailWord_2915638).sum := by decide
  have hdescent : baseEnd_2915638 < baseStart_2915638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915660 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 7]
def baseStart_2915660 : Nat := 118140960795 + 2915660 * 2 ^ 59
def prefixEnd_2915660 : Nat := 4983230072969 + 3 ^ 40 * 2915660 * 2
def baseEnd_2915660 : Nat := 332696667797370600120251

theorem tailTrace_2915660 : CollatzResearch.WordTrace tailWord_2915660 prefixEnd_2915660 332696667797370600120251 := by
  unfold tailWord_2915660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53171428308534624964440217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70895237744712833285920289 53171428308534624964440217)
  ·
    refine ⟨39878571231400968723330163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53171428308534624964440217 39878571231400968723330163)
    ·
      refine ⟨59817856847101453084995245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39878571231400968723330163 59817856847101453084995245)
      ·
        refine ⟨22431696317663044906873217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59817856847101453084995245 22431696317663044906873217)
        ·
          refine ⟨16823772238247283680154913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22431696317663044906873217 16823772238247283680154913)
          ·
            refine ⟨12617829178685462760116185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16823772238247283680154913 12617829178685462760116185)
            ·
              refine ⟨9463371884014097070087139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12617829178685462760116185 9463371884014097070087139)
              ·
                refine ⟨14195057826021145605130709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463371884014097070087139 14195057826021145605130709)
                ·
                  refine ⟨332696667797370600120251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14195057826021145605130709 332696667797370600120251)
                  ·
                    rfl

theorem cell22_2915660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_2915660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915660 prefixEnd_2915660 := by exact prefixLift 2915660
  have htrace : WordTrace (prefixWord ++ tailWord_2915660) baseStart_2915660 baseEnd_2915660 := by
    simpa [prefixWord, tailWord_2915660, baseEnd_2915660] using wordTrace_append hprefix tailTrace_2915660
  have hstable : (prefixWord ++ tailWord_2915660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915660).length < 2 ^ (prefixWord ++ tailWord_2915660).sum := by decide
  have hdescent : baseEnd_2915660 < baseStart_2915660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915670 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 2, 3]
def baseStart_2915670 : Nat := 118140960795 + 2915670 * 2 ^ 59
def prefixEnd_2915670 : Nat := 4983230072969 + 3 ^ 40 * 2915670 * 2
def baseEnd_2915670 : Nat := 998093426596475107610723

theorem tailTrace_2915670 : CollatzResearch.WordTrace tailWord_2915670 prefixEnd_2915670 998093426596475107610723 := by
  unfold tailWord_2915670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646451334189563852296529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70895480898022014424496309 6646451334189563852296529)
  ·
    refine ⟨4984838500642172889222397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6646451334189563852296529 4984838500642172889222397)
    ·
      refine ⟨1869314437740814833458399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4984838500642172889222397 1869314437740814833458399)
      ·
        refine ⟨2803971656611222250187599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869314437740814833458399 2803971656611222250187599)
        ·
          refine ⟨4205957484916833375281399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2803971656611222250187599 4205957484916833375281399)
          ·
            refine ⟨6308936227375250062922099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205957484916833375281399 6308936227375250062922099)
            ·
              refine ⟨9463404341062875094383149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308936227375250062922099 9463404341062875094383149)
              ·
                refine ⟨3548776627898578160393681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9463404341062875094383149 3548776627898578160393681)
                ·
                  refine ⟨2661582470923933620295261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3548776627898578160393681 2661582470923933620295261)
                  ·
                    refine ⟨998093426596475107610723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661582470923933620295261 998093426596475107610723)
                    ·
                      rfl

theorem cell22_2915670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_2915670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915670 prefixEnd_2915670 := by exact prefixLift 2915670
  have htrace : WordTrace (prefixWord ++ tailWord_2915670) baseStart_2915670 baseEnd_2915670 := by
    simpa [prefixWord, tailWord_2915670, baseEnd_2915670] using wordTrace_append hprefix tailTrace_2915670
  have hstable : (prefixWord ++ tailWord_2915670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915670).length < 2 ^ (prefixWord ++ tailWord_2915670).sum := by decide
  have hdescent : baseEnd_2915670 < baseStart_2915670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915735 : List Nat := [1, 1, 3, 3, 1, 1, 1, 4, 1, 6]
def baseStart_2915735 : Nat := 118140960795 + 2915735 * 2 ^ 59
def prefixEnd_2915735 : Nat := 4983230072969 + 3 ^ 40 * 2915735 * 2
def baseEnd_2915735 : Nat := 998115677424836604735523

theorem tailTrace_2915735 : CollatzResearch.WordTrace tailWord_2915735 prefixEnd_2915735 998115677424836604735523 := by
  unfold tailWord_2915735
  simp only [CollatzResearch.WordTrace]
  refine ⟨106345592091797537737860659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70897061394531691825240439 106345592091797537737860659)
  ·
    refine ⟨159518388137696306606790989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106345592091797537737860659 159518388137696306606790989)
    ·
      refine ⟨59819395551636114977546621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159518388137696306606790989 59819395551636114977546621)
      ·
        refine ⟨22432273331863543116579983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59819395551636114977546621 22432273331863543116579983)
        ·
          refine ⟨33648409997795314674869975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22432273331863543116579983 33648409997795314674869975)
          ·
            refine ⟨50472614996692972012304963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33648409997795314674869975 50472614996692972012304963)
            ·
              refine ⟨75708922495039458018457445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50472614996692972012304963 75708922495039458018457445)
              ·
                refine ⟨14195422967819898378460771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75708922495039458018457445 14195422967819898378460771)
                ·
                  refine ⟨21293134451729847567691157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14195422967819898378460771 21293134451729847567691157)
                  ·
                    refine ⟨998115677424836604735523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21293134451729847567691157 998115677424836604735523)
                    ·
                      rfl

theorem cell22_2915735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_2915735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915735 prefixEnd_2915735 := by exact prefixLift 2915735
  have htrace : WordTrace (prefixWord ++ tailWord_2915735) baseStart_2915735 baseEnd_2915735 := by
    simpa [prefixWord, tailWord_2915735, baseEnd_2915735] using wordTrace_append hprefix tailTrace_2915735
  have hstable : (prefixWord ++ tailWord_2915735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915735).length < 2 ^ (prefixWord ++ tailWord_2915735).sum := by decide
  have hdescent : baseEnd_2915735 < baseStart_2915735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915737 : List Nat := [1, 2, 1, 2, 1, 6, 2, 1, 1, 5]
def baseStart_2915737 : Nat := 118140960795 + 2915737 * 2 ^ 59
def prefixEnd_2915737 : Nat := 4983230072969 + 3 ^ 40 * 2915737 * 2
def baseEnd_2915737 : Nat := 998116362065709266185517

theorem tailTrace_2915737 : CollatzResearch.WordTrace tailWord_2915737 prefixEnd_2915737 998116362065709266185517 := by
  unfold tailWord_2915737
  simp only [CollatzResearch.WordTrace]
  refine ⟨106345665037790292079433465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70897110025193528052955643 106345665037790292079433465)
  ·
    refine ⟨79759248778342719059575099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106345665037790292079433465 79759248778342719059575099)
    ·
      refine ⟨119638873167514078589362649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79759248778342719059575099 119638873167514078589362649)
      ·
        refine ⟨89729154875635558942021987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119638873167514078589362649 89729154875635558942021987)
        ·
          refine ⟨134593732313453338413032981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89729154875635558942021987 134593732313453338413032981)
          ·
            refine ⟨6309081202193125238110921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134593732313453338413032981 6309081202193125238110921)
            ·
              refine ⟨4731810901644843928583191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309081202193125238110921 4731810901644843928583191)
              ·
                refine ⟨7097716352467265892874787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731810901644843928583191 7097716352467265892874787)
                ·
                  refine ⟨10646574528700898839312181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7097716352467265892874787 10646574528700898839312181)
                  ·
                    refine ⟨998116362065709266185517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10646574528700898839312181 998116362065709266185517)
                    ·
                      rfl

theorem cell22_2915737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_2915737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915737 prefixEnd_2915737 := by exact prefixLift 2915737
  have htrace : WordTrace (prefixWord ++ tailWord_2915737) baseStart_2915737 baseEnd_2915737 := by
    simpa [prefixWord, tailWord_2915737, baseEnd_2915737] using wordTrace_append hprefix tailTrace_2915737
  have hstable : (prefixWord ++ tailWord_2915737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915737).length < 2 ^ (prefixWord ++ tailWord_2915737).sum := by decide
  have hdescent : baseEnd_2915737 < baseStart_2915737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915829 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 7]
def baseStart_2915829 : Nat := 118140960795 + 2915829 * 2 ^ 59
def prefixEnd_2915829 : Nat := 4983230072969 + 3 ^ 40 * 2915829 * 2
def baseEnd_2915829 : Nat := 332715951848617230961745

theorem tailTrace_2915829 : CollatzResearch.WordTrace tailWord_2915829 prefixEnd_2915829 332715951848617230961745 := by
  unfold tailWord_2915829
  simp only [CollatzResearch.WordTrace]
  refine ⟨106349020553456991791782541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70899347035637994527855027 106349020553456991791782541)
  ·
    refine ⟨39880882707546371921918453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106349020553456991791782541 39880882707546371921918453)
    ·
      refine ⟨3738832753832472367679855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39880882707546371921918453 3738832753832472367679855)
      ·
        refine ⟨5608249130748708551519783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738832753832472367679855 5608249130748708551519783)
        ·
          refine ⟨8412373696123062827279675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608249130748708551519783 8412373696123062827279675)
          ·
            refine ⟨12618560544184594240919513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412373696123062827279675 12618560544184594240919513)
            ·
              refine ⟨9463920408138445680689635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12618560544184594240919513 9463920408138445680689635)
              ·
                refine ⟨14195880612207668521034453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463920408138445680689635 14195880612207668521034453)
                ·
                  refine ⟨332715951848617230961745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14195880612207668521034453 332715951848617230961745)
                  ·
                    rfl

theorem cell22_2915829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_2915829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915829 prefixEnd_2915829 := by exact prefixLift 2915829
  have htrace : WordTrace (prefixWord ++ tailWord_2915829) baseStart_2915829 baseEnd_2915829 := by
    simpa [prefixWord, tailWord_2915829, baseEnd_2915829] using wordTrace_append hprefix tailTrace_2915829
  have hstable : (prefixWord ++ tailWord_2915829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915829).length < 2 ^ (prefixWord ++ tailWord_2915829).sum := by decide
  have hdescent : baseEnd_2915829 < baseStart_2915829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915859 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 1, 4]
def baseStart_2915859 : Nat := 118140960795 + 2915859 * 2 ^ 59
def prefixEnd_2915859 : Nat := 4983230072969 + 3 ^ 40 * 2915859 * 2
def baseEnd_2915859 : Nat := 998158125158941614635143

theorem tailTrace_2915859 : CollatzResearch.WordTrace tailWord_2915859 prefixEnd_2915859 998158125158941614635143 := by
  unfold tailWord_2915859
  simp only [CollatzResearch.WordTrace]
  refine ⟨106350114743348306915374631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70900076495565537943583087 106350114743348306915374631)
  ·
    refine ⟨159525172115022460373061947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106350114743348306915374631 159525172115022460373061947)
    ·
      refine ⟨239287758172533690559592921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159525172115022460373061947 239287758172533690559592921)
      ·
        refine ⟨179465818629400267919694691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239287758172533690559592921 179465818629400267919694691)
        ·
          refine ⟨269198727944100401879542037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179465818629400267919694691 269198727944100401879542037)
          ·
            refine ⟨12618690372379706338103533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 269198727944100401879542037 12618690372379706338103533)
            ·
              refine ⟨4732008889642389876788825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12618690372379706338103533 4732008889642389876788825)
              ·
                refine ⟨3549006667231792407591619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732008889642389876788825 3549006667231792407591619)
                ·
                  refine ⟨5323510000847688611387429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549006667231792407591619 5323510000847688611387429)
                  ·
                    refine ⟨998158125158941614635143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323510000847688611387429 998158125158941614635143)
                    ·
                      rfl

theorem cell22_2915859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 1, 4].length) (baseStart_2915859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915859 prefixEnd_2915859 := by exact prefixLift 2915859
  have htrace : WordTrace (prefixWord ++ tailWord_2915859) baseStart_2915859 baseEnd_2915859 := by
    simpa [prefixWord, tailWord_2915859, baseEnd_2915859] using wordTrace_append hprefix tailTrace_2915859
  have hstable : (prefixWord ++ tailWord_2915859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915859).length < 2 ^ (prefixWord ++ tailWord_2915859).sum := by decide
  have hdescent : baseEnd_2915859 < baseStart_2915859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915891 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 4]
def baseStart_2915891 : Nat := 118140960795 + 2915891 * 2 ^ 59
def prefixEnd_2915891 : Nat := 4983230072969 + 3 ^ 40 * 2915891 * 2
def baseEnd_2915891 : Nat := 332723026470968065945015

theorem tailTrace_2915891 : CollatzResearch.WordTrace tailWord_2915891 prefixEnd_2915891 332723026470968065945015 := by
  unfold tailWord_2915891
  simp only [CollatzResearch.WordTrace]
  refine ⟨106351281879232376380539527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70900854586154917587026351 106351281879232376380539527)
  ·
    refine ⟨159526922818848564570809291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106351281879232376380539527 159526922818848564570809291)
    ·
      refine ⟨239290384228272846856213937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159526922818848564570809291 239290384228272846856213937)
      ·
        refine ⟨179467788171204635142160453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239290384228272846856213937 179467788171204635142160453)
        ·
          refine ⟨33650210282100869089155085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179467788171204635142160453 33650210282100869089155085)
          ·
            refine ⟨12618828855787825908433157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33650210282100869089155085 12618828855787825908433157)
            ·
              refine ⟨2366030410460217357831217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12618828855787825908433157 2366030410460217357831217)
              ·
                refine ⟨1774522807845163018373413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366030410460217357831217 1774522807845163018373413)
                ·
                  refine ⟨332723026470968065945015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774522807845163018373413 332723026470968065945015)
                  ·
                    rfl

theorem cell22_2915891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 4].length) (baseStart_2915891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915891 prefixEnd_2915891 := by exact prefixLift 2915891
  have htrace : WordTrace (prefixWord ++ tailWord_2915891) baseStart_2915891 baseEnd_2915891 := by
    simpa [prefixWord, tailWord_2915891, baseEnd_2915891] using wordTrace_append hprefix tailTrace_2915891
  have hstable : (prefixWord ++ tailWord_2915891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915891).length < 2 ^ (prefixWord ++ tailWord_2915891).sum := by decide
  have hdescent : baseEnd_2915891 < baseStart_2915891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2915962 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 7]
def baseStart_2915962 : Nat := 118140960795 + 2915962 * 2 ^ 59
def prefixEnd_2915962 : Nat := 4983230072969 + 3 ^ 40 * 2915962 * 2
def baseEnd_2915962 : Nat := 998193384163883679309827

theorem tailTrace_2915962 : CollatzResearch.WordTrace tailWord_2915962 prefixEnd_2915962 998193384163883679309827 := by
  unfold tailWord_2915962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26588467865493788876593535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70902580974650103670916093 26588467865493788876593535)
  ·
    refine ⟨39882701798240683314890303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26588467865493788876593535 39882701798240683314890303)
    ·
      refine ⟨59824052697361024972335455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39882701798240683314890303 59824052697361024972335455)
      ·
        refine ⟨89736079046041537458503183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59824052697361024972335455 89736079046041537458503183)
        ·
          refine ⟨134604118569062306187754775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89736079046041537458503183 134604118569062306187754775)
          ·
            refine ⟨201906177853593459281632163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134604118569062306187754775 201906177853593459281632163)
            ·
              refine ⟨302859266780390188922448245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201906177853593459281632163 302859266780390188922448245)
              ·
                refine ⟨28393056260661580211479523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302859266780390188922448245 28393056260661580211479523)
                ·
                  refine ⟨42589584390992370317219285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28393056260661580211479523 42589584390992370317219285)
                  ·
                    refine ⟨998193384163883679309827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42589584390992370317219285 998193384163883679309827)
                    ·
                      rfl

theorem cell22_2915962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_2915962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2915962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2915962 prefixEnd_2915962 := by exact prefixLift 2915962
  have htrace : WordTrace (prefixWord ++ tailWord_2915962) baseStart_2915962 baseEnd_2915962 := by
    simpa [prefixWord, tailWord_2915962, baseEnd_2915962] using wordTrace_append hprefix tailTrace_2915962
  have hstable : (prefixWord ++ tailWord_2915962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2915962).length < 2 ^ (prefixWord ++ tailWord_2915962).sum := by decide
  have hdescent : baseEnd_2915962 < baseStart_2915962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2915962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916002 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_2916002 : Nat := 118140960795 + 2916002 * 2 ^ 59
def prefixEnd_2916002 : Nat := 4983230072969 + 3 ^ 40 * 2916002 * 2
def baseEnd_2916002 : Nat := 998207076981336908309705

theorem tailTrace_2916002 : CollatzResearch.WordTrace tailWord_2916002 prefixEnd_2916002 998207076981336908309705 := by
  unfold tailWord_2916002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26588832595457560584457565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70903553587886828225220173 26588832595457560584457565)
  ·
    refine ⟨9970812223296585219171587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26588832595457560584457565 9970812223296585219171587)
    ·
      refine ⟨14956218334944877828757381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9970812223296585219171587 14956218334944877828757381)
      ·
        refine ⟨2804290937802164592892009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14956218334944877828757381 2804290937802164592892009)
        ·
          refine ⟨2103218203351623444669007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2804290937802164592892009 2103218203351623444669007)
          ·
            refine ⟨3154827305027435167003511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103218203351623444669007 3154827305027435167003511)
            ·
              refine ⟨4732240957541152750505267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154827305027435167003511 4732240957541152750505267)
              ·
                refine ⟨7098361436311729125757901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732240957541152750505267 7098361436311729125757901)
                ·
                  refine ⟨2661885538616898422159213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7098361436311729125757901 2661885538616898422159213)
                  ·
                    refine ⟨998207076981336908309705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661885538616898422159213 998207076981336908309705)
                    ·
                      rfl

theorem cell22_2916002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_2916002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916002 prefixEnd_2916002 := by exact prefixLift 2916002
  have htrace : WordTrace (prefixWord ++ tailWord_2916002) baseStart_2916002 baseEnd_2916002 := by
    simpa [prefixWord, tailWord_2916002, baseEnd_2916002] using wordTrace_append hprefix tailTrace_2916002
  have hstable : (prefixWord ++ tailWord_2916002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916002).length < 2 ^ (prefixWord ++ tailWord_2916002).sum := by decide
  have hdescent : baseEnd_2916002 < baseStart_2916002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916028 : List Nat := [2, 2, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_2916028 : Nat := 118140960795 + 2916028 * 2 ^ 59
def prefixEnd_2916028 : Nat := 4983230072969 + 3 ^ 40 * 2916028 * 2
def baseEnd_2916028 : Nat := 998215977312681507159625

theorem tailTrace_2916028 : CollatzResearch.WordTrace tailWord_2916028 prefixEnd_2916028 998215977312681507159625 := by
  unfold tailWord_2916028
  simp only [CollatzResearch.WordTrace]
  refine ⟨53178139339868024389138369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70904185786490699185517825 53178139339868024389138369)
  ·
    refine ⟨39883604504901018291853777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53178139339868024389138369 39883604504901018291853777)
    ·
      refine ⟨29912703378675763718890333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39883604504901018291853777 29912703378675763718890333)
      ·
        refine ⟨11217263767003411394583875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29912703378675763718890333 11217263767003411394583875)
        ·
          refine ⟨16825895650505117091875813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11217263767003411394583875 16825895650505117091875813)
          ·
            refine ⟨3154855434469709454726715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16825895650505117091875813 3154855434469709454726715)
            ·
              refine ⟨4732283151704564182090073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154855434469709454726715 4732283151704564182090073)
              ·
                refine ⟨3549212363778423136567555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732283151704564182090073 3549212363778423136567555)
                ·
                  refine ⟨5323818545667634704851333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549212363778423136567555 5323818545667634704851333)
                  ·
                    refine ⟨998215977312681507159625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323818545667634704851333 998215977312681507159625)
                    ·
                      rfl

theorem cell22_2916028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_2916028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916028 prefixEnd_2916028 := by exact prefixLift 2916028
  have htrace : WordTrace (prefixWord ++ tailWord_2916028) baseStart_2916028 baseEnd_2916028 := by
    simpa [prefixWord, tailWord_2916028, baseEnd_2916028] using wordTrace_append hprefix tailTrace_2916028
  have hstable : (prefixWord ++ tailWord_2916028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916028).length < 2 ^ (prefixWord ++ tailWord_2916028).sum := by decide
  have hdescent : baseEnd_2916028 < baseStart_2916028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916058 : List Nat := [3, 1, 1, 2, 2, 4, 2, 2, 2, 3]
def baseStart_2916058 : Nat := 118140960795 + 2916058 * 2 ^ 59
def prefixEnd_2916058 : Nat := 4983230072969 + 3 ^ 40 * 2916058 * 2
def baseEnd_2916058 : Nat := 998226246925771428909533

theorem tailTrace_2916058 : CollatzResearch.WordTrace tailWord_2916058 prefixEnd_2916058 998226246925771428909533 := by
  unfold tailWord_2916058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26589343217406840975467207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70904915246418242601245885 26589343217406840975467207)
  ·
    refine ⟨39884014826110261463200811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26589343217406840975467207 39884014826110261463200811)
    ·
      refine ⟨59826022239165392194801217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39884014826110261463200811 59826022239165392194801217)
      ·
        refine ⟨44869516679374044146100913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59826022239165392194801217 44869516679374044146100913)
        ·
          refine ⟨33652137509530533109575685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44869516679374044146100913 33652137509530533109575685)
          ·
            refine ⟨6309775783036974958045441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33652137509530533109575685 6309775783036974958045441)
            ·
              refine ⟨4732331837277731218534081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6309775783036974958045441 4732331837277731218534081)
              ·
                refine ⟨3549248877958298413900561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732331837277731218534081 3549248877958298413900561)
                ·
                  refine ⟨2661936658468723810425421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549248877958298413900561 2661936658468723810425421)
                  ·
                    refine ⟨998226246925771428909533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661936658468723810425421 998226246925771428909533)
                    ·
                      rfl

theorem cell22_2916058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 2, 2, 3].length) (baseStart_2916058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916058 prefixEnd_2916058 := by exact prefixLift 2916058
  have htrace : WordTrace (prefixWord ++ tailWord_2916058) baseStart_2916058 baseEnd_2916058 := by
    simpa [prefixWord, tailWord_2916058, baseEnd_2916058] using wordTrace_append hprefix tailTrace_2916058
  have hstable : (prefixWord ++ tailWord_2916058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916058).length < 2 ^ (prefixWord ++ tailWord_2916058).sum := by decide
  have hdescent : baseEnd_2916058 < baseStart_2916058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916060 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 4]
def baseStart_2916060 : Nat := 118140960795 + 2916060 * 2 ^ 59
def prefixEnd_2916060 : Nat := 4983230072969 + 3 ^ 40 * 2916060 * 2
def baseEnd_2916060 : Nat := 332742310522214696786509

theorem tailTrace_2916060 : CollatzResearch.WordTrace tailWord_2916060 prefixEnd_2916060 332742310522214696786509 := by
  unfold tailWord_2916060
  simp only [CollatzResearch.WordTrace]
  refine ⟨53178722907810059121720817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70904963877080078828961089 53178722907810059121720817)
  ·
    refine ⟨39884042180857544341290613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53178722907810059121720817 39884042180857544341290613)
    ·
      refine ⟨3739128954455394781995995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39884042180857544341290613 3739128954455394781995995)
      ·
        refine ⟨5608693431683092172993993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739128954455394781995995 5608693431683092172993993)
        ·
          refine ⟨4206520073762319129745495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5608693431683092172993993 4206520073762319129745495)
          ·
            refine ⟨6309780110643478694618243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206520073762319129745495 6309780110643478694618243)
            ·
              refine ⟨9464670165965218041927365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309780110643478694618243 9464670165965218041927365)
              ·
                refine ⟨1774625656118478382861381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9464670165965218041927365 1774625656118478382861381)
                ·
                  refine ⟨332742310522214696786509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774625656118478382861381 332742310522214696786509)
                  ·
                    rfl

theorem cell22_2916060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 4].length) (baseStart_2916060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916060 prefixEnd_2916060 := by exact prefixLift 2916060
  have htrace : WordTrace (prefixWord ++ tailWord_2916060) baseStart_2916060 baseEnd_2916060 := by
    simpa [prefixWord, tailWord_2916060, baseEnd_2916060] using wordTrace_append hprefix tailTrace_2916060
  have hstable : (prefixWord ++ tailWord_2916060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916060).length < 2 ^ (prefixWord ++ tailWord_2916060).sum := by decide
  have hdescent : baseEnd_2916060 < baseStart_2916060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916109 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_2916109 : Nat := 118140960795 + 2916109 * 2 ^ 59
def prefixEnd_2916109 : Nat := 4983230072969 + 3 ^ 40 * 2916109 * 2
def baseEnd_2916109 : Nat := 998243705268024295884377

theorem tailTrace_2916109 : CollatzResearch.WordTrace tailWord_2916109 prefixEnd_2916109 998243705268024295884377 := by
  unfold tailWord_2916109
  simp only [CollatzResearch.WordTrace]
  refine ⟨106359232992442599611975381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70906155328295066407983587 106359232992442599611975381)
  ·
    refine ⟨2492794523260373428405673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 106359232992442599611975381 2492794523260373428405673)
    ·
      refine ⟨1869595892445280071304255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2492794523260373428405673 1869595892445280071304255)
      ·
        refine ⟨2804393838667920106956383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869595892445280071304255 2804393838667920106956383)
        ·
          refine ⟨4206590758001880160434575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804393838667920106956383 4206590758001880160434575)
          ·
            refine ⟨6309886137002820240651863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206590758001880160434575 6309886137002820240651863)
            ·
              refine ⟨9464829205504230360977795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309886137002820240651863 9464829205504230360977795)
              ·
                refine ⟨14197243808256345541466693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9464829205504230360977795 14197243808256345541466693)
                ·
                  refine ⟨2661983214048064789025005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14197243808256345541466693 2661983214048064789025005)
                  ·
                    refine ⟨998243705268024295884377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661983214048064789025005 998243705268024295884377)
                    ·
                      rfl

theorem cell22_2916109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_2916109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916109 prefixEnd_2916109 := by exact prefixLift 2916109
  have htrace : WordTrace (prefixWord ++ tailWord_2916109) baseStart_2916109 baseEnd_2916109 := by
    simpa [prefixWord, tailWord_2916109, baseEnd_2916109] using wordTrace_append hprefix tailTrace_2916109
  have hstable : (prefixWord ++ tailWord_2916109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916109).length < 2 ^ (prefixWord ++ tailWord_2916109).sum := by decide
  have hdescent : baseEnd_2916109 < baseStart_2916109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916133 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 5]
def baseStart_2916133 : Nat := 118140960795 + 2916133 * 2 ^ 59
def prefixEnd_2916133 : Nat := 4983230072969 + 3 ^ 40 * 2916133 * 2
def baseEnd_2916133 : Nat := 332750640319498744428101

theorem tailTrace_2916133 : CollatzResearch.WordTrace tailWord_2916133 prefixEnd_2916133 332750640319498744428101 := by
  unfold tailWord_2916133
  simp only [CollatzResearch.WordTrace]
  refine ⟨106360108344355651710849053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70906738896237101140566035 106360108344355651710849053)
  ·
    refine ⟨39885040629133369391568395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106360108344355651710849053 39885040629133369391568395)
    ·
      refine ⟨59827560943700054087352593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39885040629133369391568395 59827560943700054087352593)
      ·
        refine ⟨44870670707775040565514445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59827560943700054087352593 44870670707775040565514445)
        ·
          refine ⟨16826501515415640212067917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44870670707775040565514445 16826501515415640212067917)
          ·
            refine ⟨6309938068280865079525469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16826501515415640212067917 6309938068280865079525469)
            ·
              refine ⟨2366226775605324404822051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6309938068280865079525469 2366226775605324404822051)
              ·
                refine ⟨3549340163407986607233077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366226775605324404822051 3549340163407986607233077)
                ·
                  refine ⟨332750640319498744428101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549340163407986607233077 332750640319498744428101)
                  ·
                    rfl

theorem cell22_2916133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_2916133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916133 prefixEnd_2916133 := by exact prefixLift 2916133
  have htrace : WordTrace (prefixWord ++ tailWord_2916133) baseStart_2916133 baseEnd_2916133 := by
    simpa [prefixWord, tailWord_2916133, baseEnd_2916133] using wordTrace_append hprefix tailTrace_2916133
  have hstable : (prefixWord ++ tailWord_2916133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916133).length < 2 ^ (prefixWord ++ tailWord_2916133).sum := by decide
  have hdescent : baseEnd_2916133 < baseStart_2916133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916178 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 6]
def baseStart_2916178 : Nat := 118140960795 + 2916178 * 2 ^ 59
def prefixEnd_2916178 : Nat := 4983230072969 + 3 ^ 40 * 2916178 * 2
def baseEnd_2916178 : Nat := 332755775126043705303055

theorem tailTrace_2916178 : CollatzResearch.WordTrace tailWord_2916178 prefixEnd_2916178 332755775126043705303055 := by
  unfold tailWord_2916178
  simp only [CollatzResearch.WordTrace]
  refine ⟨26590437407298156099059297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70907833086128416264158125 26590437407298156099059297)
  ·
    refine ⟨19942828055473617074294473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26590437407298156099059297 19942828055473617074294473)
    ·
      refine ⟨14957121041605212805720855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19942828055473617074294473 14957121041605212805720855)
      ·
        refine ⟨22435681562407819208581283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957121041605212805720855 22435681562407819208581283)
        ·
          refine ⟨33653522343611728812871925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22435681562407819208581283 33653522343611728812871925)
          ·
            refine ⟨3155017719713599576206743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33653522343611728812871925 3155017719713599576206743)
            ·
              refine ⟨4732526579570399364310115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155017719713599576206743 4732526579570399364310115)
              ·
                refine ⟨7098789869355599046465173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732526579570399364310115 7098789869355599046465173)
                ·
                  refine ⟨332755775126043705303055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7098789869355599046465173 332755775126043705303055)
                  ·
                    rfl

theorem cell22_2916178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_2916178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916178 prefixEnd_2916178 := by exact prefixLift 2916178
  have htrace : WordTrace (prefixWord ++ tailWord_2916178) baseStart_2916178 baseEnd_2916178 := by
    simpa [prefixWord, tailWord_2916178, baseEnd_2916178] using wordTrace_append hprefix tailTrace_2916178
  have hstable : (prefixWord ++ tailWord_2916178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916178).length < 2 ^ (prefixWord ++ tailWord_2916178).sum := by decide
  have hdescent : baseEnd_2916178 < baseStart_2916178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916193 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 2, 3]
def baseStart_2916193 : Nat := 118140960795 + 2916193 * 2 ^ 59
def prefixEnd_2916193 : Nat := 4983230072969 + 3 ^ 40 * 2916193 * 2
def baseEnd_2916193 : Nat := 998272460184676076784119

theorem tailTrace_2916193 : CollatzResearch.WordTrace tailWord_2916193 prefixEnd_2916193 998272460184676076784119 := by
  unfold tailWord_2916193
  simp only [CollatzResearch.WordTrace]
  refine ⟨106362296724138281958033233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70908197816092187972022155 106362296724138281958033233)
  ·
    refine ⟨79771722543103711468524925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106362296724138281958033233 79771722543103711468524925)
    ·
      refine ⟨29914395953663891800696847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79771722543103711468524925 29914395953663891800696847)
      ·
        refine ⟨44871593930495837701045271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29914395953663891800696847 44871593930495837701045271)
        ·
          refine ⟨67307390895743756551567907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44871593930495837701045271 67307390895743756551567907)
          ·
            refine ⟨100961086343615634827351861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67307390895743756551567907 100961086343615634827351861)
            ·
              refine ⟨9465101844713965765064237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100961086343615634827351861 9465101844713965765064237)
              ·
                refine ⟨3549413191767737161899089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9465101844713965765064237 3549413191767737161899089)
                ·
                  refine ⟨2662059893825802871424317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549413191767737161899089 2662059893825802871424317)
                  ·
                    refine ⟨998272460184676076784119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662059893825802871424317 998272460184676076784119)
                    ·
                      rfl

theorem cell22_2916193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_2916193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916193 prefixEnd_2916193 := by exact prefixLift 2916193
  have htrace : WordTrace (prefixWord ++ tailWord_2916193) baseStart_2916193 baseEnd_2916193 := by
    simpa [prefixWord, tailWord_2916193, baseEnd_2916193] using wordTrace_append hprefix tailTrace_2916193
  have hstable : (prefixWord ++ tailWord_2916193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916193).length < 2 ^ (prefixWord ++ tailWord_2916193).sum := by decide
  have hdescent : baseEnd_2916193 < baseStart_2916193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916255 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 3, 3]
def baseStart_2916255 : Nat := 118140960795 + 2916255 * 2 ^ 59
def prefixEnd_2916255 : Nat := 4983230072969 + 3 ^ 40 * 2916255 * 2
def baseEnd_2916255 : Nat := 998293684051728581733929

theorem tailTrace_2916255 : CollatzResearch.WordTrace tailWord_2916255 prefixEnd_2916255 998293684051728581733929 := by
  unfold tailWord_2916255
  simp only [CollatzResearch.WordTrace]
  refine ⟨106364558049913666546790219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70909705366609111031193479 106364558049913666546790219)
  ·
    refine ⟨159546837074870499820185329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106364558049913666546790219 159546837074870499820185329)
    ·
      refine ⟨119660127806152874865138997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159546837074870499820185329 119660127806152874865138997)
      ·
        refine ⟨11218136981826832018606781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119660127806152874865138997 11218136981826832018606781)
        ·
          refine ⟨4206801368185062006977543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11218136981826832018606781 4206801368185062006977543)
          ·
            refine ⟨6310202052277593010466315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206801368185062006977543 6310202052277593010466315)
            ·
              refine ⟨9465303078416389515699473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310202052277593010466315 9465303078416389515699473)
              ·
                refine ⟨7098977308812292136774605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9465303078416389515699473 7098977308812292136774605)
                ·
                  refine ⟨2662116490804609551290477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7098977308812292136774605 2662116490804609551290477)
                  ·
                    refine ⟨998293684051728581733929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662116490804609551290477 998293684051728581733929)
                    ·
                      rfl

theorem cell22_2916255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 3, 3].length) (baseStart_2916255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916255 prefixEnd_2916255 := by exact prefixLift 2916255
  have htrace : WordTrace (prefixWord ++ tailWord_2916255) baseStart_2916255 baseEnd_2916255 := by
    simpa [prefixWord, tailWord_2916255, baseEnd_2916255] using wordTrace_append hprefix tailTrace_2916255
  have hstable : (prefixWord ++ tailWord_2916255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916255).length < 2 ^ (prefixWord ++ tailWord_2916255).sum := by decide
  have hdescent : baseEnd_2916255 < baseStart_2916255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916285 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 5]
def baseStart_2916285 : Nat := 118140960795 + 2916285 * 2 ^ 59
def prefixEnd_2916285 : Nat := 4983230072969 + 3 ^ 40 * 2916285 * 2
def baseEnd_2916285 : Nat := 332767984554939501161279

theorem tailTrace_2916285 : CollatzResearch.WordTrace tailWord_2916285 prefixEnd_2916285 332767984554939501161279 := by
  unfold tailWord_2916285
  simp only [CollatzResearch.WordTrace]
  refine ⟨106365652239804981670382309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70910434826536654446921539 106365652239804981670382309)
  ·
    refine ⟨19943559794963434063196683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106365652239804981670382309 19943559794963434063196683)
    ·
      refine ⟨29915339692445151094795025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19943559794963434063196683 29915339692445151094795025)
      ·
        refine ⟨22436504769333863321096269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29915339692445151094795025 22436504769333863321096269)
        ·
          refine ⟨8413689288500198745411101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22436504769333863321096269 8413689288500198745411101)
          ·
            refine ⟨3155133483187574529529163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8413689288500198745411101 3155133483187574529529163)
            ·
              refine ⟨4732700224781361794293745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155133483187574529529163 4732700224781361794293745)
              ·
                refine ⟨3549525168586021345720309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732700224781361794293745 3549525168586021345720309)
                ·
                  refine ⟨332767984554939501161279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549525168586021345720309 332767984554939501161279)
                  ·
                    rfl

theorem cell22_2916285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_2916285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916285 prefixEnd_2916285 := by exact prefixLift 2916285
  have htrace : WordTrace (prefixWord ++ tailWord_2916285) baseStart_2916285 baseEnd_2916285 := by
    simpa [prefixWord, tailWord_2916285, baseEnd_2916285] using wordTrace_append hprefix tailTrace_2916285
  have hstable : (prefixWord ++ tailWord_2916285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916285).length < 2 ^ (prefixWord ++ tailWord_2916285).sum := by decide
  have hdescent : baseEnd_2916285 < baseStart_2916285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916362 : List Nat := [3, 1, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_2916362 : Nat := 118140960795 + 2916362 * 2 ^ 59
def prefixEnd_2916362 : Nat := 4983230072969 + 3 ^ 40 * 2916362 * 2
def baseEnd_2916362 : Nat := 998330312338415969308601

theorem tailTrace_2916362 : CollatzResearch.WordTrace tailWord_2916362 prefixEnd_2916362 998330312338415969308601 := by
  unfold tailWord_2916362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26592115165131505955233835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70912307107017349213956893 26592115165131505955233835)
  ·
    refine ⟨39888172747697258932850753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26592115165131505955233835 39888172747697258932850753)
    ·
      refine ⟨29916129560772944199638065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39888172747697258932850753 29916129560772944199638065)
      ·
        refine ⟨22437097170579708149728549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29916129560772944199638065 22437097170579708149728549)
        ·
          refine ⟨4206955719483695278074103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22437097170579708149728549 4206955719483695278074103)
          ·
            refine ⟨6310433579225542917111155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206955719483695278074103 6310433579225542917111155)
            ·
              refine ⟨9465650368838314375666733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6310433579225542917111155 9465650368838314375666733)
              ·
                refine ⟨3549618888314367890875025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9465650368838314375666733 3549618888314367890875025)
                ·
                  refine ⟨2662214166235775918156269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549618888314367890875025 2662214166235775918156269)
                  ·
                    refine ⟨998330312338415969308601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662214166235775918156269 998330312338415969308601)
                    ·
                      rfl

theorem cell22_2916362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_2916362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916362 prefixEnd_2916362 := by exact prefixLift 2916362
  have htrace : WordTrace (prefixWord ++ tailWord_2916362) baseStart_2916362 baseEnd_2916362 := by
    simpa [prefixWord, tailWord_2916362, baseEnd_2916362] using wordTrace_append hprefix tailTrace_2916362
  have hstable : (prefixWord ++ tailWord_2916362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916362).length < 2 ^ (prefixWord ++ tailWord_2916362).sum := by decide
  have hdescent : baseEnd_2916362 < baseStart_2916362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916403 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 5]
def baseStart_2916403 : Nat := 118140960795 + 2916403 * 2 ^ 59
def prefixEnd_2916403 : Nat := 4983230072969 + 3 ^ 40 * 2916403 * 2
def baseEnd_2916403 : Nat := 332781449158768509677825

theorem tailTrace_2916403 : CollatzResearch.WordTrace tailWord_2916403 prefixEnd_2916403 332781449158768509677825 := by
  unfold tailWord_2916403
  simp only [CollatzResearch.WordTrace]
  refine ⟨106369956053377487823177863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70913304035584991882118575 106369956053377487823177863)
  ·
    refine ⟨159554934080066231734766795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106369956053377487823177863 159554934080066231734766795)
    ·
      refine ⟨239332401120099347602150193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159554934080066231734766795 239332401120099347602150193)
      ·
        refine ⟨179499300840074510701612645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 239332401120099347602150193 179499300840074510701612645)
        ·
          refine ⟨33656118907513970756552371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179499300840074510701612645 33656118907513970756552371)
          ·
            refine ⟨50484178361270956134828557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33656118907513970756552371 50484178361270956134828557)
            ·
              refine ⟨18931566885476608550560709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50484178361270956134828557 18931566885476608550560709)
              ·
                refine ⟨3549668791026864103230133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18931566885476608550560709 3549668791026864103230133)
                ·
                  refine ⟨332781449158768509677825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549668791026864103230133 332781449158768509677825)
                  ·
                    rfl

theorem cell22_2916403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 5].length) (baseStart_2916403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916403 prefixEnd_2916403 := by exact prefixLift 2916403
  have htrace : WordTrace (prefixWord ++ tailWord_2916403) baseStart_2916403 baseEnd_2916403 := by
    simpa [prefixWord, tailWord_2916403, baseEnd_2916403] using wordTrace_append hprefix tailTrace_2916403
  have hstable : (prefixWord ++ tailWord_2916403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916403).length < 2 ^ (prefixWord ++ tailWord_2916403).sum := by decide
  have hdescent : baseEnd_2916403 < baseStart_2916403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916465 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 4]
def baseStart_2916465 : Nat := 118140960795 + 2916465 * 2 ^ 59
def prefixEnd_2916465 : Nat := 4983230072969 + 3 ^ 40 * 2916465 * 2
def baseEnd_2916465 : Nat := 332788523781119344661095

theorem tailTrace_2916465 : CollatzResearch.WordTrace tailWord_2916465 prefixEnd_2916465 332788523781119344661095 := by
  unfold tailWord_2916465
  simp only [CollatzResearch.WordTrace]
  refine ⟨106372217379152872411934849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70914811586101914941289899 106372217379152872411934849)
  ·
    refine ⟨79779163034364654308951137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106372217379152872411934849 79779163034364654308951137)
    ·
      refine ⟨59834372275773490731713353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79779163034364654308951137 59834372275773490731713353)
      ·
        refine ⟨44875779206830118048785015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59834372275773490731713353 44875779206830118048785015)
        ·
          refine ⟨67313668810245177073177523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44875779206830118048785015 67313668810245177073177523)
          ·
            refine ⟨100970503215367765609766285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67313668810245177073177523 100970503215367765609766285)
            ·
              refine ⟨37863938705762912103662357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100970503215367765609766285 37863938705762912103662357)
              ·
                refine ⟨1774872126832636504859173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37863938705762912103662357 1774872126832636504859173)
                ·
                  refine ⟨332788523781119344661095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774872126832636504859173 332788523781119344661095)
                  ·
                    rfl

theorem cell22_2916465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 4].length) (baseStart_2916465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916465 prefixEnd_2916465 := by exact prefixLift 2916465
  have htrace : WordTrace (prefixWord ++ tailWord_2916465) baseStart_2916465 baseEnd_2916465 := by
    simpa [prefixWord, tailWord_2916465, baseEnd_2916465] using wordTrace_append hprefix tailTrace_2916465
  have hstable : (prefixWord ++ tailWord_2916465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916465).length < 2 ^ (prefixWord ++ tailWord_2916465).sum := by decide
  have hdescent : baseEnd_2916465 < baseStart_2916465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916546 : List Nat := [3, 5, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2916546 : Nat := 118140960795 + 2916546 * 2 ^ 59
def prefixEnd_2916546 : Nat := 4983230072969 + 3 ^ 40 * 2916546 * 2
def baseEnd_2916546 : Nat := 998393299298700822708037

theorem tailTrace_2916546 : CollatzResearch.WordTrace tailWord_2916546 prefixEnd_2916546 998393299298700822708037 := by
  unfold tailWord_2916546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26593792922964855811408373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70916781127906282163755661 26593792922964855811408373)
  ·
    refine ⟨2493168086527955232319535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26593792922964855811408373 2493168086527955232319535)
    ·
      refine ⟨3739752129791932848479303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493168086527955232319535 3739752129791932848479303)
      ·
        refine ⟨5609628194687899272718955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739752129791932848479303 5609628194687899272718955)
        ·
          refine ⟨8414442292031848909078433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609628194687899272718955 8414442292031848909078433)
          ·
            refine ⟨6310831719023886681808825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8414442292031848909078433 6310831719023886681808825)
            ·
              refine ⟨4733123789267915011356619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6310831719023886681808825 4733123789267915011356619)
              ·
                refine ⟨7099685683901872517034929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733123789267915011356619 7099685683901872517034929)
                ·
                  refine ⟨5324764262926404387776197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7099685683901872517034929 5324764262926404387776197)
                  ·
                    refine ⟨998393299298700822708037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5324764262926404387776197 998393299298700822708037)
                    ·
                      rfl

theorem cell22_2916546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2916546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916546 prefixEnd_2916546 := by exact prefixLift 2916546
  have htrace : WordTrace (prefixWord ++ tailWord_2916546) baseStart_2916546 baseEnd_2916546 := by
    simpa [prefixWord, tailWord_2916546, baseEnd_2916546] using wordTrace_append hprefix tailTrace_2916546
  have hstable : (prefixWord ++ tailWord_2916546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916546).length < 2 ^ (prefixWord ++ tailWord_2916546).sum := by decide
  have hdescent : baseEnd_2916546 < baseStart_2916546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916553 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 7]
def baseStart_2916553 : Nat := 118140960795 + 2916553 * 2 ^ 59
def prefixEnd_2916553 : Nat := 4983230072969 + 3 ^ 40 * 2916553 * 2
def baseEnd_2916553 : Nat := 998395695541755137783015

theorem tailTrace_2916553 : CollatzResearch.WordTrace tailWord_2916553 prefixEnd_2916553 998395695541755137783015 := by
  unfold tailWord_2916553
  simp only [CollatzResearch.WordTrace]
  refine ⟨106375427002834063441138313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70916951335222708960758875 106375427002834063441138313)
  ·
    refine ⟨79781570252125547580853735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106375427002834063441138313 79781570252125547580853735)
    ·
      refine ⟨119672355378188321371280603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79781570252125547580853735 119672355378188321371280603)
      ·
        refine ⟨179508533067282482056920905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119672355378188321371280603 179508533067282482056920905)
        ·
          refine ⟨134631399800461861542690679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179508533067282482056920905 134631399800461861542690679)
          ·
            refine ⟨201947099700692792314036019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134631399800461861542690679 201947099700692792314036019)
            ·
              refine ⟨302920649551039188471054029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201947099700692792314036019 302920649551039188471054029)
              ·
                refine ⟨113595243581639695676645261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302920649551039188471054029 113595243581639695676645261)
                ·
                  refine ⟨42598216343114885878741973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 113595243581639695676645261 42598216343114885878741973)
                  ·
                    refine ⟨998395695541755137783015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42598216343114885878741973 998395695541755137783015)
                    ·
                      rfl

theorem cell22_2916553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 7].length) (baseStart_2916553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916553 prefixEnd_2916553 := by exact prefixLift 2916553
  have htrace : WordTrace (prefixWord ++ tailWord_2916553) baseStart_2916553 baseEnd_2916553 := by
    simpa [prefixWord, tailWord_2916553, baseEnd_2916553] using wordTrace_append hprefix tailTrace_2916553
  have hstable : (prefixWord ++ tailWord_2916553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916553).length < 2 ^ (prefixWord ++ tailWord_2916553).sum := by decide
  have hdescent : baseEnd_2916553 < baseStart_2916553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916578 : List Nat := [3, 3, 4, 1, 2, 1, 1, 7]
def baseStart_2916578 : Nat := 118140960795 + 2916578 * 2 ^ 59
def prefixEnd_2916578 : Nat := 4983230072969 + 3 ^ 40 * 2916578 * 2
def baseEnd_2916578 : Nat := 110933805950295933989771

theorem tailTrace_2916578 : CollatzResearch.WordTrace tailWord_2916578 prefixEnd_2916578 110933805950295933989771 := by
  unfold tailWord_2916578
  simp only [CollatzResearch.WordTrace]
  refine ⟨26594084706935873177699597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70917559218495661807198925 26594084706935873177699597)
  ·
    refine ⟨9972781765100952441637349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26594084706935873177699597 9972781765100952441637349)
    ·
      refine ⟨1869896580956428582807003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9972781765100952441637349 1869896580956428582807003)
      ·
        refine ⟨2804844871434642874210505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869896580956428582807003 2804844871434642874210505)
        ·
          refine ⟨2103633653575982155657879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2804844871434642874210505 2103633653575982155657879)
          ·
            refine ⟨3155450480363973233486819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103633653575982155657879 3155450480363973233486819)
            ·
              refine ⟨4733175720545959850230229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155450480363973233486819 4733175720545959850230229)
              ·
                refine ⟨110933805950295933989771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4733175720545959850230229 110933805950295933989771)
                ·
                  rfl

theorem cell22_2916578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_2916578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916578 prefixEnd_2916578 := by exact prefixLift 2916578
  have htrace : WordTrace (prefixWord ++ tailWord_2916578) baseStart_2916578 baseEnd_2916578 := by
    simpa [prefixWord, tailWord_2916578, baseEnd_2916578] using wordTrace_append hprefix tailTrace_2916578
  have hstable : (prefixWord ++ tailWord_2916578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916578).length < 2 ^ (prefixWord ++ tailWord_2916578).sum := by decide
  have hdescent : baseEnd_2916578 < baseStart_2916578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916617 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 4]
def baseStart_2916617 : Nat := 118140960795 + 2916617 * 2 ^ 59
def prefixEnd_2916617 : Nat := 4983230072969 + 3 ^ 40 * 2916617 * 2
def baseEnd_2916617 : Nat := 332805868016560101394273

theorem tailTrace_2916617 : CollatzResearch.WordTrace tailWord_2916617 prefixEnd_2916617 332805868016560101394273 := by
  unfold tailWord_2916617
  simp only [CollatzResearch.WordTrace]
  refine ⟨106377761274602202371468105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70918507516401468247645403 106377761274602202371468105)
  ·
    refine ⟨79783320955951651778601079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106377761274602202371468105 79783320955951651778601079)
    ·
      refine ⟨119674981433927477667901619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79783320955951651778601079 119674981433927477667901619)
      ·
        refine ⟨179512472150891216501852429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119674981433927477667901619 179512472150891216501852429)
        ·
          refine ⟨67317177056584206188194661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179512472150891216501852429 67317177056584206188194661)
          ·
            refine ⟨12621970698109538660286499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67317177056584206188194661 12621970698109538660286499)
            ·
              refine ⟨18932956047164307990429749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12621970698109538660286499 18932956047164307990429749)
              ·
                refine ⟨1774964629421653874102789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18932956047164307990429749 1774964629421653874102789)
                ·
                  refine ⟨332805868016560101394273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774964629421653874102789 332805868016560101394273)
                  ·
                    rfl

theorem cell22_2916617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 4].length) (baseStart_2916617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916617 prefixEnd_2916617 := by exact prefixLift 2916617
  have htrace : WordTrace (prefixWord ++ tailWord_2916617) baseStart_2916617 baseEnd_2916617 := by
    simpa [prefixWord, tailWord_2916617, baseEnd_2916617] using wordTrace_append hprefix tailTrace_2916617
  have hstable : (prefixWord ++ tailWord_2916617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916617).length < 2 ^ (prefixWord ++ tailWord_2916617).sum := by decide
  have hdescent : baseEnd_2916617 < baseStart_2916617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916632 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 4, 3]
def baseStart_2916632 : Nat := 118140960795 + 2916632 * 2 ^ 59
def prefixEnd_2916632 : Nat := 4983230072969 + 3 ^ 40 * 2916632 * 2
def baseEnd_2916632 : Nat := 998422738856225265057773

theorem tailTrace_2916632 : CollatzResearch.WordTrace tailWord_2916632 prefixEnd_2916632 998422738856225265057773 := by
  unfold tailWord_2916632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53189154184773929966632075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70918872246365239955509433 53189154184773929966632075)
  ·
    refine ⟨79783731277160894949948113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53189154184773929966632075 79783731277160894949948113)
    ·
      refine ⟨59837798457870671212461085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79783731277160894949948113 59837798457870671212461085)
      ·
        refine ⟨22439174421701501704672907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59837798457870671212461085 22439174421701501704672907)
        ·
          refine ⟨33658761632552252557009361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22439174421701501704672907 33658761632552252557009361)
          ·
            refine ⟨25244071224414189417757021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33658761632552252557009361 25244071224414189417757021)
            ·
              refine ⟨9466526709155321031658883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25244071224414189417757021 9466526709155321031658883)
              ·
                refine ⟨14199790063732981547488325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9466526709155321031658883 14199790063732981547488325)
                ·
                  refine ⟨2662460636949934040154061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14199790063732981547488325 2662460636949934040154061)
                  ·
                    refine ⟨998422738856225265057773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662460636949934040154061 998422738856225265057773)
                    ·
                      rfl

theorem cell22_2916632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4, 3].length) (baseStart_2916632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916632 prefixEnd_2916632 := by exact prefixLift 2916632
  have htrace : WordTrace (prefixWord ++ tailWord_2916632) baseStart_2916632 baseEnd_2916632 := by
    simpa [prefixWord, tailWord_2916632, baseEnd_2916632] using wordTrace_append hprefix tailTrace_2916632
  have hstable : (prefixWord ++ tailWord_2916632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916632).length < 2 ^ (prefixWord ++ tailWord_2916632).sum := by decide
  have hdescent : baseEnd_2916632 < baseStart_2916632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916700 : List Nat := [2, 2, 4, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2916700 : Nat := 118140960795 + 2916700 * 2 ^ 59
def prefixEnd_2916700 : Nat := 4983230072969 + 3 ^ 40 * 2916700 * 2
def baseEnd_2916700 : Nat := 998446016645895754357565

theorem tailTrace_2916700 : CollatzResearch.WordTrace tailWord_2916700 prefixEnd_2916700 998446016645895754357565 := by
  unfold tailWord_2916700
  simp only [CollatzResearch.WordTrace]
  refine ⟨53190394266650753773369777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70920525688867671697826369 53190394266650753773369777)
  ·
    refine ⟨39892795699988065330027333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53190394266650753773369777 39892795699988065330027333)
    ·
      refine ⟨7479899193747762249380125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39892795699988065330027333 7479899193747762249380125)
      ·
        refine ⟨2804962197655410843517547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7479899193747762249380125 2804962197655410843517547)
        ·
          refine ⟨4207443296483116265276321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2804962197655410843517547 4207443296483116265276321)
          ·
            refine ⟨3155582472362337198957241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207443296483116265276321 3155582472362337198957241)
            ·
              refine ⟨2366686854271752899217931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155582472362337198957241 2366686854271752899217931)
              ·
                refine ⟨3550030281407629348826897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366686854271752899217931 3550030281407629348826897)
                ·
                  refine ⟨2662522711055722011620173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3550030281407629348826897 2662522711055722011620173)
                  ·
                    refine ⟨998446016645895754357565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662522711055722011620173 998446016645895754357565)
                    ·
                      rfl

theorem cell22_2916700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2916700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916700 prefixEnd_2916700 := by exact prefixLift 2916700
  have htrace : WordTrace (prefixWord ++ tailWord_2916700) baseStart_2916700 baseEnd_2916700 := by
    simpa [prefixWord, tailWord_2916700, baseEnd_2916700] using wordTrace_append hprefix tailTrace_2916700
  have hstable : (prefixWord ++ tailWord_2916700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916700).length < 2 ^ (prefixWord ++ tailWord_2916700).sum := by decide
  have hdescent : baseEnd_2916700 < baseStart_2916700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916707 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 5]
def baseStart_2916707 : Nat := 118140960795 + 2916707 * 2 ^ 59
def prefixEnd_2916707 : Nat := 4983230072969 + 3 ^ 40 * 2916707 * 2
def baseEnd_2916707 : Nat := 332816137629650023144181

theorem tailTrace_2916707 : CollatzResearch.WordTrace tailWord_2916707 prefixEnd_2916707 332816137629650023144181 := by
  unfold tailWord_2916707
  simp only [CollatzResearch.WordTrace]
  refine ⟨106381043844276147742244375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70920695896184098494829583 106381043844276147742244375)
  ·
    refine ⟨159571565766414221613366563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106381043844276147742244375 159571565766414221613366563)
    ·
      refine ⟨239357348649621332420049845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159571565766414221613366563 239357348649621332420049845)
      ·
        refine ⟨22439751435901999914379673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 239357348649621332420049845 22439751435901999914379673)
        ·
          refine ⟨16829813576926499935784755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22439751435901999914379673 16829813576926499935784755)
          ·
            refine ⟨25244720365389749903677133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16829813576926499935784755 25244720365389749903677133)
            ·
              refine ⟨9466770137021156213878925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25244720365389749903677133 9466770137021156213878925)
              ·
                refine ⟨3550038801382933580204597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9466770137021156213878925 3550038801382933580204597)
                ·
                  refine ⟨332816137629650023144181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550038801382933580204597 332816137629650023144181)
                  ·
                    rfl

theorem cell22_2916707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 5].length) (baseStart_2916707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916707 prefixEnd_2916707 := by exact prefixLift 2916707
  have htrace : WordTrace (prefixWord ++ tailWord_2916707) baseStart_2916707 baseEnd_2916707 := by
    simpa [prefixWord, tailWord_2916707, baseEnd_2916707] using wordTrace_append hprefix tailTrace_2916707
  have hstable : (prefixWord ++ tailWord_2916707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916707).length < 2 ^ (prefixWord ++ tailWord_2916707).sum := by decide
  have hdescent : baseEnd_2916707 < baseStart_2916707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916735 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 8]
def baseStart_2916735 : Nat := 118140960795 + 2916735 * 2 ^ 59
def prefixEnd_2916735 : Nat := 4983230072969 + 3 ^ 40 * 2916735 * 2
def baseEnd_2916735 : Nat := 332819332620389109910819

theorem tailTrace_2916735 : CollatzResearch.WordTrace tailWord_2916735 prefixEnd_2916735 332819332620389109910819 := by
  unfold tailWord_2916735
  simp only [CollatzResearch.WordTrace]
  refine ⟨106382065088174708524263659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70921376725449805682842439 106382065088174708524263659)
  ·
    refine ⟨159573097632262062786395489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106382065088174708524263659 159573097632262062786395489)
    ·
      refine ⟨119679823224196547089796617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159573097632262062786395489 119679823224196547089796617)
      ·
        refine ⟨89759867418147410317347463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119679823224196547089796617 89759867418147410317347463)
        ·
          refine ⟨134639801127221115476021195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89759867418147410317347463 134639801127221115476021195)
          ·
            refine ⟨201959701690831673214031793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134639801127221115476021195 201959701690831673214031793)
            ·
              refine ⟨151469776268123754910523845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 201959701690831673214031793 151469776268123754910523845)
              ·
                refine ⟨28400583050273204045723221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 151469776268123754910523845 28400583050273204045723221)
                ·
                  refine ⟨332819332620389109910819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28400583050273204045723221 332819332620389109910819)
                  ·
                    rfl

theorem cell22_2916735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 8].length) (baseStart_2916735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916735 prefixEnd_2916735 := by exact prefixLift 2916735
  have htrace : WordTrace (prefixWord ++ tailWord_2916735) baseStart_2916735 baseEnd_2916735 := by
    simpa [prefixWord, tailWord_2916735, baseEnd_2916735] using wordTrace_append hprefix tailTrace_2916735
  have hstable : (prefixWord ++ tailWord_2916735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916735).length < 2 ^ (prefixWord ++ tailWord_2916735).sum := by decide
  have hdescent : baseEnd_2916735 < baseStart_2916735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916797 : List Nat := [1, 4, 1, 2, 2, 3, 9]
def baseStart_2916797 : Nat := 118140960795 + 2916797 * 2 ^ 59
def prefixEnd_2916797 : Nat := 4983230072969 + 3 ^ 40 * 2916797 * 2
def baseEnd_2916797 : Nat := 36980711915859993877121

theorem tailTrace_2916797 : CollatzResearch.WordTrace tailWord_2916797 prefixEnd_2916797 36980711915859993877121 := by
  unfold tailWord_2916797
  simp only [CollatzResearch.WordTrace]
  refine ⟨106384326413950093113020645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70922884275966728742013763 106384326413950093113020645)
  ·
    refine ⟨19947061202615642458691371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106384326413950093113020645 19947061202615642458691371)
    ·
      refine ⟨29920591803923463688037057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19947061202615642458691371 29920591803923463688037057)
      ·
        refine ⟨22440443852942597766027793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29920591803923463688037057 22440443852942597766027793)
        ·
          refine ⟨16830332889706948324520845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22440443852942597766027793 16830332889706948324520845)
          ·
            refine ⟨6311374833640105621695317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16830332889706948324520845 6311374833640105621695317)
            ·
              refine ⟨36980711915859993877121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6311374833640105621695317 36980711915859993877121)
              ·
                rfl

theorem cell22_2916797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 9].length) (baseStart_2916797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916797 prefixEnd_2916797 := by exact prefixLift 2916797
  have htrace : WordTrace (prefixWord ++ tailWord_2916797) baseStart_2916797 baseEnd_2916797 := by
    simpa [prefixWord, tailWord_2916797, baseEnd_2916797] using wordTrace_append hprefix tailTrace_2916797
  have hstable : (prefixWord ++ tailWord_2916797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916797).length < 2 ^ (prefixWord ++ tailWord_2916797).sum := by decide
  have hdescent : baseEnd_2916797 < baseStart_2916797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916818 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2916818 : Nat := 118140960795 + 2916818 * 2 ^ 59
def prefixEnd_2916818 : Nat := 4983230072969 + 3 ^ 40 * 2916818 * 2
def baseEnd_2916818 : Nat := 998486410457382779907203

theorem tailTrace_2916818 : CollatzResearch.WordTrace tailWord_2916818 prefixEnd_2916818 998486410457382779907203 := by
  unfold tailWord_2916818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26596273086718503424883777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70923394897916009133023405 26596273086718503424883777)
  ·
    refine ⟨19947204815038877568662833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26596273086718503424883777 19947204815038877568662833)
    ·
      refine ⟨14960403611279158176497125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19947204815038877568662833 14960403611279158176497125)
      ·
        refine ⟨2805075677114842158093211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14960403611279158176497125 2805075677114842158093211)
        ·
          refine ⟨4207613515672263237139817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805075677114842158093211 4207613515672263237139817)
          ·
            refine ⟨3155710136754197427854863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4207613515672263237139817 3155710136754197427854863)
            ·
              refine ⟨4733565205131296141782295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155710136754197427854863 4733565205131296141782295)
              ·
                refine ⟨7100347807696944212673443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4733565205131296141782295 7100347807696944212673443)
                ·
                  refine ⟨10650521711545416319010165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100347807696944212673443 10650521711545416319010165)
                  ·
                    refine ⟨998486410457382779907203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10650521711545416319010165 998486410457382779907203)
                    ·
                      rfl

theorem cell22_2916818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2916818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916818 prefixEnd_2916818 := by exact prefixLift 2916818
  have htrace : WordTrace (prefixWord ++ tailWord_2916818) baseStart_2916818 baseEnd_2916818 := by
    simpa [prefixWord, tailWord_2916818, baseEnd_2916818] using wordTrace_append hprefix tailTrace_2916818
  have hstable : (prefixWord ++ tailWord_2916818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916818).length < 2 ^ (prefixWord ++ tailWord_2916818).sum := by decide
  have hdescent : baseEnd_2916818 < baseStart_2916818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916857 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 4, 5]
def baseStart_2916857 : Nat := 118140960795 + 2916857 * 2 ^ 59
def prefixEnd_2916857 : Nat := 4983230072969 + 3 ^ 40 * 2916857 * 2
def baseEnd_2916857 : Nat := 998499760954399678182083

theorem tailTrace_2916857 : CollatzResearch.WordTrace tailWord_2916857 prefixEnd_2916857 998499760954399678182083 := by
  unfold tailWord_2916857
  simp only [CollatzResearch.WordTrace]
  refine ⟨106386514793732723360204825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70924343195821815573469883 106386514793732723360204825)
  ·
    refine ⟨79789886095299542520153619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106386514793732723360204825 79789886095299542520153619)
    ·
      refine ⟨119684829142949313780230429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79789886095299542520153619 119684829142949313780230429)
      ·
        refine ⟨44881810928605992667586411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119684829142949313780230429 44881810928605992667586411)
        ·
          refine ⟨67322716392908989001379617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44881810928605992667586411 67322716392908989001379617)
          ·
            refine ⟨50492037294681741751034713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67322716392908989001379617 50492037294681741751034713)
            ·
              refine ⟨37869027971011306313276035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50492037294681741751034713 37869027971011306313276035)
              ·
                refine ⟨56803541956516959469914053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37869027971011306313276035 56803541956516959469914053)
                ·
                  refine ⟨10650664116846929900608885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56803541956516959469914053 10650664116846929900608885)
                  ·
                    refine ⟨998499760954399678182083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10650664116846929900608885 998499760954399678182083)
                    ·
                      rfl

theorem cell22_2916857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 5].length) (baseStart_2916857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916857 prefixEnd_2916857 := by exact prefixLift 2916857
  have htrace : WordTrace (prefixWord ++ tailWord_2916857) baseStart_2916857 baseEnd_2916857 := by
    simpa [prefixWord, tailWord_2916857, baseEnd_2916857] using wordTrace_append hprefix tailTrace_2916857
  have hstable : (prefixWord ++ tailWord_2916857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916857).length < 2 ^ (prefixWord ++ tailWord_2916857).sum := by decide
  have hdescent : baseEnd_2916857 < baseStart_2916857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916863 : List Nat := [1, 1, 2, 2, 1, 2, 7, 2, 1, 3]
def baseStart_2916863 : Nat := 118140960795 + 2916863 * 2 ^ 59
def prefixEnd_2916863 : Nat := 4983230072969 + 3 ^ 40 * 2916863 * 2
def baseEnd_2916863 : Nat := 998501814877017662532065

theorem tailTrace_2916863 : CollatzResearch.WordTrace tailWord_2916863 prefixEnd_2916863 998501814877017662532065 := by
  unfold tailWord_2916863
  simp only [CollatzResearch.WordTrace]
  refine ⟨106386733631710986384923243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70924489087807324256615495 106386733631710986384923243)
  ·
    refine ⟨159580100447566479577384865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106386733631710986384923243 159580100447566479577384865)
    ·
      refine ⟨119685075335674859683038649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 159580100447566479577384865 119685075335674859683038649)
      ·
        refine ⟨89763806501756144762278987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119685075335674859683038649 89763806501756144762278987)
        ·
          refine ⟨134645709752634217143418481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89763806501756144762278987 134645709752634217143418481)
          ·
            refine ⟨100984282314475662857563861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134645709752634217143418481 100984282314475662857563861)
            ·
              refine ⟨2366819116745523348224153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 100984282314475662857563861 2366819116745523348224153)
              ·
                refine ⟨1775114337559142511168115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366819116745523348224153 1775114337559142511168115)
                ·
                  refine ⟨2662671506338713766752173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775114337559142511168115 2662671506338713766752173)
                  ·
                    refine ⟨998501814877017662532065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662671506338713766752173 998501814877017662532065)
                    ·
                      rfl

theorem cell22_2916863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 2, 1, 3].length) (baseStart_2916863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916863 prefixEnd_2916863 := by exact prefixLift 2916863
  have htrace : WordTrace (prefixWord ++ tailWord_2916863) baseStart_2916863 baseEnd_2916863 := by
    simpa [prefixWord, tailWord_2916863, baseEnd_2916863] using wordTrace_append hprefix tailTrace_2916863
  have hstable : (prefixWord ++ tailWord_2916863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916863).length < 2 ^ (prefixWord ++ tailWord_2916863).sum := by decide
  have hdescent : baseEnd_2916863 < baseStart_2916863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916872 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2916872 : Nat := 118140960795 + 2916872 * 2 ^ 59
def prefixEnd_2916872 : Nat := 4983230072969 + 3 ^ 40 * 2916872 * 2
def baseEnd_2916872 : Nat := 998504895760944639057037

theorem tailTrace_2916872 : CollatzResearch.WordTrace tailWord_2916872 prefixEnd_2916872 998504895760944639057037 := by
  unfold tailWord_2916872
  simp only [CollatzResearch.WordTrace]
  refine ⟨53193530944339190461000435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70924707925785587281333913 53193530944339190461000435)
  ·
    refine ⟨79790296416508785691500653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53193530944339190461000435 79790296416508785691500653)
    ·
      refine ⟨29921361156190794634312745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79790296416508785691500653 29921361156190794634312745)
      ·
        refine ⟨22441020867143095975734559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29921361156190794634312745 22441020867143095975734559)
        ·
          refine ⟨33661531300714643963601839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22441020867143095975734559 33661531300714643963601839)
          ·
            refine ⟨50492296951071965945402759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33661531300714643963601839 50492296951071965945402759)
            ·
              refine ⟨75738445426607948918104139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50492296951071965945402759 75738445426607948918104139)
              ·
                refine ⟨113607668139911923377156209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75738445426607948918104139 113607668139911923377156209)
                ·
                  refine ⟨85205751104933942532867157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113607668139911923377156209 85205751104933942532867157)
                  ·
                    refine ⟨998504895760944639057037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85205751104933942532867157 998504895760944639057037)
                    ·
                      rfl

theorem cell22_2916872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2916872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916872 prefixEnd_2916872 := by exact prefixLift 2916872
  have htrace : WordTrace (prefixWord ++ tailWord_2916872) baseStart_2916872 baseEnd_2916872 := by
    simpa [prefixWord, tailWord_2916872, baseEnd_2916872] using wordTrace_append hprefix tailTrace_2916872
  have hstable : (prefixWord ++ tailWord_2916872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916872).length < 2 ^ (prefixWord ++ tailWord_2916872).sum := by decide
  have hdescent : baseEnd_2916872 < baseStart_2916872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916876 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 5]
def baseStart_2916876 : Nat := 118140960795 + 2916876 * 2 ^ 59
def prefixEnd_2916876 : Nat := 4983230072969 + 3 ^ 40 * 2916876 * 2
def baseEnd_2916876 : Nat := 332835421680896653985675

theorem tailTrace_2916876 : CollatzResearch.WordTrace tailWord_2916876 prefixEnd_2916876 332835421680896653985675 := by
  unfold tailWord_2916876
  simp only [CollatzResearch.WordTrace]
  refine ⟨53193603890331944802573241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70924805187109259736764321 53193603890331944802573241)
  ·
    refine ⟨39895202917748958601929931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53193603890331944802573241 39895202917748958601929931)
    ·
      refine ⟨59842804376623437902894897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39895202917748958601929931 59842804376623437902894897)
      ·
        refine ⟨44882103282467578427171173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59842804376623437902894897 44882103282467578427171173)
        ·
          refine ⟨8415394365462670955094595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44882103282467578427171173 8415394365462670955094595)
          ·
            refine ⟨12623091548194006432641893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415394365462670955094595 12623091548194006432641893)
            ·
              refine ⟨2366829665286376206120355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12623091548194006432641893 2366829665286376206120355)
              ·
                refine ⟨3550244497929564309180533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366829665286376206120355 3550244497929564309180533)
                ·
                  refine ⟨332835421680896653985675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550244497929564309180533 332835421680896653985675)
                  ·
                    rfl

theorem cell22_2916876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 5].length) (baseStart_2916876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916876 prefixEnd_2916876 := by exact prefixLift 2916876
  have htrace : WordTrace (prefixWord ++ tailWord_2916876) baseStart_2916876 baseEnd_2916876 := by
    simpa [prefixWord, tailWord_2916876, baseEnd_2916876] using wordTrace_append hprefix tailTrace_2916876
  have hstable : (prefixWord ++ tailWord_2916876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916876).length < 2 ^ (prefixWord ++ tailWord_2916876).sum := by decide
  have hdescent : baseEnd_2916876 < baseStart_2916876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2916921 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 4]
def baseStart_2916921 : Nat := 118140960795 + 2916921 * 2 ^ 59
def prefixEnd_2916921 : Nat := 4983230072969 + 3 ^ 40 * 2916921 * 2
def baseEnd_2916921 : Nat := 332840556487441614860629

theorem tailTrace_2916921 : CollatzResearch.WordTrace tailWord_2916921 prefixEnd_2916921 332840556487441614860629 := by
  unfold tailWord_2916921
  simp only [CollatzResearch.WordTrace]
  refine ⟨106388849065500862290534617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70925899377000574860356411 106388849065500862290534617)
  ·
    refine ⟨79791636799125646717900963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106388849065500862290534617 79791636799125646717900963)
    ·
      refine ⟨119687455198688470076851445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79791636799125646717900963 119687455198688470076851445)
      ·
        refine ⟨11220698924877044069704823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119687455198688470076851445 11220698924877044069704823)
        ·
          refine ⟨16831048387315566104557235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220698924877044069704823 16831048387315566104557235)
          ·
            refine ⟨25246572580973349156835853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16831048387315566104557235 25246572580973349156835853)
            ·
              refine ⟨9467464717865005933813445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25246572580973349156835853 9467464717865005933813445)
              ·
                refine ⟨1775149634599688612590021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9467464717865005933813445 1775149634599688612590021)
                ·
                  refine ⟨332840556487441614860629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775149634599688612590021 332840556487441614860629)
                  ·
                    rfl

theorem cell22_2916921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 4].length) (baseStart_2916921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2916921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2916921 prefixEnd_2916921 := by exact prefixLift 2916921
  have htrace : WordTrace (prefixWord ++ tailWord_2916921) baseStart_2916921 baseEnd_2916921 := by
    simpa [prefixWord, tailWord_2916921, baseEnd_2916921] using wordTrace_append hprefix tailTrace_2916921
  have hstable : (prefixWord ++ tailWord_2916921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2916921).length < 2 ^ (prefixWord ++ tailWord_2916921).sum := by decide
  have hdescent : baseEnd_2916921 < baseStart_2916921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2916921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917045 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 5]
def baseStart_2917045 : Nat := 118140960795 + 2917045 * 2 ^ 59
def prefixEnd_2917045 : Nat := 4983230072969 + 3 ^ 40 * 2917045 * 2
def baseEnd_2917045 : Nat := 332854705732143284827169

theorem tailTrace_2917045 : CollatzResearch.WordTrace tailWord_2917045 prefixEnd_2917045 332854705732143284827169 := by
  unfold tailWord_2917045
  simp only [CollatzResearch.WordTrace]
  refine ⟨106393371717051631468048589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70928914478034420978699059 106393371717051631468048589)
  ·
    refine ⟨39897514393894361800518221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106393371717051631468048589 39897514393894361800518221)
    ·
      refine ⟨14961567897710385675194333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39897514393894361800518221 14961567897710385675194333)
      ·
        refine ⟨5610587961641394628197875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14961567897710385675194333 5610587961641394628197875)
        ·
          refine ⟨8415881942462091942296813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610587961641394628197875 8415881942462091942296813)
          ·
            refine ⟨3155955728423284478361305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8415881942462091942296813 3155955728423284478361305)
            ·
              refine ⟨2366966796317463358770979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155955728423284478361305 2366966796317463358770979)
              ·
                refine ⟨3550450194476195038156469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366966796317463358770979 3550450194476195038156469)
                ·
                  refine ⟨332854705732143284827169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550450194476195038156469 332854705732143284827169)
                  ·
                    rfl

theorem cell22_2917045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 5].length) (baseStart_2917045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917045 prefixEnd_2917045 := by exact prefixLift 2917045
  have htrace : WordTrace (prefixWord ++ tailWord_2917045) baseStart_2917045 baseEnd_2917045 := by
    simpa [prefixWord, tailWord_2917045, baseEnd_2917045] using wordTrace_append hprefix tailTrace_2917045
  have hstable : (prefixWord ++ tailWord_2917045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917045).length < 2 ^ (prefixWord ++ tailWord_2917045).sum := by decide
  have hdescent : baseEnd_2917045 < baseStart_2917045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917099 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 2, 7]
def baseStart_2917099 : Nat := 118140960795 + 2917099 * 2 ^ 59
def prefixEnd_2917099 : Nat := 4983230072969 + 3 ^ 40 * 2917099 * 2
def baseEnd_2917099 : Nat := 998582602499991713631341

theorem tailTrace_2917099 : CollatzResearch.WordTrace tailWord_2917099 prefixEnd_2917099 998582602499991713631341 := by
  unfold tailWord_2917099
  simp only [CollatzResearch.WordTrace]
  refine ⟨106395341258855998690514351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70930227505903999127009567 106395341258855998690514351)
  ·
    refine ⟨159593011888283998035771527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106395341258855998690514351 159593011888283998035771527)
    ·
      refine ⟨239389517832425997053657291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159593011888283998035771527 239389517832425997053657291)
      ·
        refine ⟨359084276748638995580485937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239389517832425997053657291 359084276748638995580485937)
        ·
          refine ⟨269313207561479246685364453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 359084276748638995580485937 269313207561479246685364453)
          ·
            refine ⟨50496226417777358753505835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 269313207561479246685364453 50496226417777358753505835)
            ·
              refine ⟨75744339626666038130258753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50496226417777358753505835 75744339626666038130258753)
              ·
                refine ⟨56808254719999528597694065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75744339626666038130258753 56808254719999528597694065)
                ·
                  refine ⟨42606191039999646448270549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56808254719999528597694065 42606191039999646448270549)
                  ·
                    refine ⟨998582602499991713631341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42606191039999646448270549 998582602499991713631341)
                    ·
                      rfl

theorem cell22_2917099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 7].length) (baseStart_2917099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917099 prefixEnd_2917099 := by exact prefixLift 2917099
  have htrace : WordTrace (prefixWord ++ tailWord_2917099) baseStart_2917099 baseEnd_2917099 := by
    simpa [prefixWord, tailWord_2917099, baseEnd_2917099] using wordTrace_append hprefix tailTrace_2917099
  have hstable : (prefixWord ++ tailWord_2917099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917099).length < 2 ^ (prefixWord ++ tailWord_2917099).sum := by decide
  have hdescent : baseEnd_2917099 < baseStart_2917099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917146 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_2917146 : Nat := 118140960795 + 2917146 * 2 ^ 59
def prefixEnd_2917146 : Nat := 4983230072969 + 3 ^ 40 * 2917146 * 2
def baseEnd_2917146 : Nat := 332866230520166419235399

theorem tailTrace_2917146 : CollatzResearch.WordTrace tailWord_2917146 prefixEnd_2917146 332866230520166419235399 := by
  unfold tailWord_2917146
  simp only [CollatzResearch.WordTrace]
  refine ⟨26599263872421431429368823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70931370326457150478316861 26599263872421431429368823)
  ·
    refine ⟨39898895808632147144053235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26599263872421431429368823 39898895808632147144053235)
    ·
      refine ⟨59848343712948220716079853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39898895808632147144053235 59848343712948220716079853)
      ·
        refine ⟨22443128892355582768529945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59848343712948220716079853 22443128892355582768529945)
        ·
          refine ⟨16832346669266687076397459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22443128892355582768529945 16832346669266687076397459)
          ·
            refine ⟨25248520003900030614596189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16832346669266687076397459 25248520003900030614596189)
            ·
              refine ⟨9468195001462511480473571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25248520003900030614596189 9468195001462511480473571)
              ·
                refine ⟨14202292502193767220710357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468195001462511480473571 14202292502193767220710357)
                ·
                  refine ⟨332866230520166419235399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14202292502193767220710357 332866230520166419235399)
                  ·
                    rfl

theorem cell22_2917146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_2917146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917146 prefixEnd_2917146 := by exact prefixLift 2917146
  have htrace : WordTrace (prefixWord ++ tailWord_2917146) baseStart_2917146 baseEnd_2917146 := by
    simpa [prefixWord, tailWord_2917146, baseEnd_2917146] using wordTrace_append hprefix tailTrace_2917146
  have hstable : (prefixWord ++ tailWord_2917146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917146).length < 2 ^ (prefixWord ++ tailWord_2917146).sum := by decide
  have hdescent : baseEnd_2917146 < baseStart_2917146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917193 : List Nat := [1, 2, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_2917193 : Nat := 118140960795 + 2917193 * 2 ^ 59
def prefixEnd_2917193 : Nat := 4983230072969 + 3 ^ 40 * 2917193 * 2
def baseEnd_2917193 : Nat := 998614780621006801781053

theorem tailTrace_2917193 : CollatzResearch.WordTrace tailWord_2917193 prefixEnd_2917193 998614780621006801781053 := by
  unfold tailWord_2917193
  simp only [CollatzResearch.WordTrace]
  refine ⟨106398769720515452744436233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70932513147010301829624155 106398769720515452744436233)
  ·
    refine ⟨79799077290386589558327175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106398769720515452744436233 79799077290386589558327175)
    ·
      refine ⟨119698615935579884337490763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79799077290386589558327175 119698615935579884337490763)
      ·
        refine ⟨179547923903369826506236145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119698615935579884337490763 179547923903369826506236145)
        ·
          refine ⟨134660942927527369879677109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179547923903369826506236145 134660942927527369879677109)
          ·
            refine ⟨12624463399455690926219729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134660942927527369879677109 12624463399455690926219729)
            ·
              refine ⟨9468347549591768194664797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624463399455690926219729 9468347549591768194664797)
              ·
                refine ⟨3550630331096913072999299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9468347549591768194664797 3550630331096913072999299)
                ·
                  refine ⟨5325945496645369609498949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550630331096913072999299 5325945496645369609498949)
                  ·
                    refine ⟨998614780621006801781053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5325945496645369609498949 998614780621006801781053)
                    ·
                      rfl

theorem cell22_2917193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_2917193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917193 prefixEnd_2917193 := by exact prefixLift 2917193
  have htrace : WordTrace (prefixWord ++ tailWord_2917193) baseStart_2917193 baseEnd_2917193 := by
    simpa [prefixWord, tailWord_2917193, baseEnd_2917193] using wordTrace_append hprefix tailTrace_2917193
  have hstable : (prefixWord ++ tailWord_2917193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917193).length < 2 ^ (prefixWord ++ tailWord_2917193).sum := by decide
  have hdescent : baseEnd_2917193 < baseStart_2917193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917208 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 4]
def baseStart_2917208 : Nat := 118140960795 + 2917208 * 2 ^ 59
def prefixEnd_2917208 : Nat := 4983230072969 + 3 ^ 40 * 2917208 * 2
def baseEnd_2917208 : Nat := 332873305142517254218669

theorem tailTrace_2917208 : CollatzResearch.WordTrace tailWord_2917208 prefixEnd_2917208 332873305142517254218669 := by
  unfold tailWord_2917208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53199658407730555153116139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70932877876974073537488185 53199658407730555153116139)
  ·
    refine ⟨79799487611595832729674209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53199658407730555153116139 79799487611595832729674209)
    ·
      refine ⟨59849615708696874547255657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79799487611595832729674209 59849615708696874547255657)
      ·
        refine ⟨44887211781522655910441743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59849615708696874547255657 44887211781522655910441743)
        ·
          refine ⟨67330817672283983865662615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44887211781522655910441743 67330817672283983865662615)
          ·
            refine ⟨100996226508425975798493923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67330817672283983865662615 100996226508425975798493923)
            ·
              refine ⟨151494339762638963697740885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100996226508425975798493923 151494339762638963697740885)
              ·
                refine ⟨1775324294093425355832901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 151494339762638963697740885 1775324294093425355832901)
                ·
                  refine ⟨332873305142517254218669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775324294093425355832901 332873305142517254218669)
                  ·
                    rfl

theorem cell22_2917208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 4].length) (baseStart_2917208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917208 prefixEnd_2917208 := by exact prefixLift 2917208
  have htrace : WordTrace (prefixWord ++ tailWord_2917208) baseStart_2917208 baseEnd_2917208 := by
    simpa [prefixWord, tailWord_2917208, baseEnd_2917208] using wordTrace_append hprefix tailTrace_2917208
  have hstable : (prefixWord ++ tailWord_2917208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917208).length < 2 ^ (prefixWord ++ tailWord_2917208).sum := by decide
  have hdescent : baseEnd_2917208 < baseStart_2917208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917221 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2917221 : Nat := 118140960795 + 2917221 * 2 ^ 59
def prefixEnd_2917221 : Nat := 4983230072969 + 3 ^ 40 * 2917221 * 2
def baseEnd_2917221 : Nat := 998624365593224062080967

theorem tailTrace_2917221 : CollatzResearch.WordTrace tailWord_2917221 prefixEnd_2917221 998624365593224062080967 := by
  unfold tailWord_2917221
  simp only [CollatzResearch.WordTrace]
  refine ⟨106399790964414013526455517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70933193976276009017637011 106399790964414013526455517)
  ·
    refine ⟨39899921611655255072420819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106399790964414013526455517 39899921611655255072420819)
    ·
      refine ⟨59849882417482882608631229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39899921611655255072420819 59849882417482882608631229)
      ·
        refine ⟨22443705906556080978236711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59849882417482882608631229 22443705906556080978236711)
        ·
          refine ⟨33665558859834121467355067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22443705906556080978236711 33665558859834121467355067)
          ·
            refine ⟨50498338289751182201032601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33665558859834121467355067 50498338289751182201032601)
            ·
              refine ⟨37873753717313386650774451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50498338289751182201032601 37873753717313386650774451)
              ·
                refine ⟨56810630575970079976161677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37873753717313386650774451 56810630575970079976161677)
                ·
                  refine ⟨21303986465988779991060629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56810630575970079976161677 21303986465988779991060629)
                  ·
                    refine ⟨998624365593224062080967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21303986465988779991060629 998624365593224062080967)
                    ·
                      rfl

theorem cell22_2917221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2917221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917221 prefixEnd_2917221 := by exact prefixLift 2917221
  have htrace : WordTrace (prefixWord ++ tailWord_2917221) baseStart_2917221 baseEnd_2917221 := by
    simpa [prefixWord, tailWord_2917221, baseEnd_2917221] using wordTrace_append hprefix tailTrace_2917221
  have hstable : (prefixWord ++ tailWord_2917221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917221).length < 2 ^ (prefixWord ++ tailWord_2917221).sum := by decide
  have hdescent : baseEnd_2917221 < baseStart_2917221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917330 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2917330 : Nat := 118140960795 + 2917330 * 2 ^ 59
def prefixEnd_2917330 : Nat := 4983230072969 + 3 ^ 40 * 2917330 * 2
def baseEnd_2917330 : Nat := 998661678520784111105633

theorem tailTrace_2917330 : CollatzResearch.WordTrace tailWord_2917330 prefixEnd_2917330 998661678520784111105633 := by
  unfold tailWord_2917330
  simp only [CollatzResearch.WordTrace]
  refine ⟨26600941630254781285543361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70935844347346083428115629 26600941630254781285543361)
  ·
    refine ⟨19950706222691085964157521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26600941630254781285543361 19950706222691085964157521)
    ·
      refine ⟨14963029667018314473118141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19950706222691085964157521 14963029667018314473118141)
      ·
        refine ⟨5611136125131867927419303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14963029667018314473118141 5611136125131867927419303)
        ·
          refine ⟨8416704187697801891128955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611136125131867927419303 8416704187697801891128955)
          ·
            refine ⟨12625056281546702836693433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416704187697801891128955 12625056281546702836693433)
            ·
              refine ⟨9468792211160027127520075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12625056281546702836693433 9468792211160027127520075)
              ·
                refine ⟨14203188316740040691280113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468792211160027127520075 14203188316740040691280113)
                ·
                  refine ⟨10652391237555030518460085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14203188316740040691280113 10652391237555030518460085)
                  ·
                    refine ⟨998661678520784111105633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10652391237555030518460085 998661678520784111105633)
                    ·
                      rfl

theorem cell22_2917330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2917330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917330 prefixEnd_2917330 := by exact prefixLift 2917330
  have htrace : WordTrace (prefixWord ++ tailWord_2917330) baseStart_2917330 baseEnd_2917330 := by
    simpa [prefixWord, tailWord_2917330, baseEnd_2917330] using wordTrace_append hprefix tailTrace_2917330
  have hstable : (prefixWord ++ tailWord_2917330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917330).length < 2 ^ (prefixWord ++ tailWord_2917330).sum := by decide
  have hdescent : baseEnd_2917330 < baseStart_2917330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917332 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 5]
def baseStart_2917332 : Nat := 118140960795 + 2917332 * 2 ^ 59
def prefixEnd_2917332 : Nat := 4983230072969 + 3 ^ 40 * 2917332 * 2
def baseEnd_2917332 : Nat := 332887454387218924185209

theorem tailTrace_2917332 : CollatzResearch.WordTrace tailWord_2917332 prefixEnd_2917332 332887454387218924185209 := by
  unfold tailWord_2917332
  simp only [CollatzResearch.WordTrace]
  refine ⟨53201919733505939741873125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70935892978007919655830833 53201919733505939741873125)
  ·
    refine ⟨9975359950032363701601211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53201919733505939741873125 9975359950032363701601211)
    ·
      refine ⟨14963039925048545552401817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975359950032363701601211 14963039925048545552401817)
      ·
        refine ⟨11222279943786409164301363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14963039925048545552401817 11222279943786409164301363)
        ·
          refine ⟨16833419915679613746452045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11222279943786409164301363 16833419915679613746452045)
          ·
            refine ⟨6312532468379855154919517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16833419915679613746452045 6312532468379855154919517)
            ·
              refine ⟨2367199675642445683094819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6312532468379855154919517 2367199675642445683094819)
              ·
                refine ⟨3550799513463668524642229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367199675642445683094819 3550799513463668524642229)
                ·
                  refine ⟨332887454387218924185209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550799513463668524642229 332887454387218924185209)
                  ·
                    rfl

theorem cell22_2917332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_2917332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917332 prefixEnd_2917332 := by exact prefixLift 2917332
  have htrace : WordTrace (prefixWord ++ tailWord_2917332) baseStart_2917332 baseEnd_2917332 := by
    simpa [prefixWord, tailWord_2917332, baseEnd_2917332] using wordTrace_append hprefix tailTrace_2917332
  have hstable : (prefixWord ++ tailWord_2917332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917332).length < 2 ^ (prefixWord ++ tailWord_2917332).sum := by decide
  have hdescent : baseEnd_2917332 < baseStart_2917332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917388 : List Nat := [2, 2, 1, 2, 3, 2, 1, 9]
def baseStart_2917388 : Nat := 118140960795 + 2917388 * 2 ^ 59
def prefixEnd_2917388 : Nat := 4983230072969 + 3 ^ 40 * 2917388 * 2
def baseEnd_2917388 : Nat := 110964614789565699239495

theorem tailTrace_2917388 : CollatzResearch.WordTrace tailWord_2917388 prefixEnd_2917388 110964614789565699239495 := by
  unfold tailWord_2917388
  simp only [CollatzResearch.WordTrace]
  refine ⟨53202940977404500523892409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70937254636539334031856545 53202940977404500523892409)
  ·
    refine ⟨39902205733053375392919307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53202940977404500523892409 39902205733053375392919307)
    ·
      refine ⟨59853308599580063089378961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39902205733053375392919307 59853308599580063089378961)
      ·
        refine ⟨44889981449685047317034221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59853308599580063089378961 44889981449685047317034221)
        ·
          refine ⟨16833743043631892743887833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44889981449685047317034221 16833743043631892743887833)
          ·
            refine ⟨12625307282723919557915875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16833743043631892743887833 12625307282723919557915875)
            ·
              refine ⟨18937960924085879336873813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625307282723919557915875 18937960924085879336873813)
              ·
                refine ⟨110964614789565699239495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18937960924085879336873813 110964614789565699239495)
                ·
                  rfl

theorem cell22_2917388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_2917388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917388 prefixEnd_2917388 := by exact prefixLift 2917388
  have htrace : WordTrace (prefixWord ++ tailWord_2917388) baseStart_2917388 baseEnd_2917388 := by
    simpa [prefixWord, tailWord_2917388, baseEnd_2917388] using wordTrace_append hprefix tailTrace_2917388
  have hstable : (prefixWord ++ tailWord_2917388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917388).length < 2 ^ (prefixWord ++ tailWord_2917388).sum := by decide
  have hdescent : baseEnd_2917388 < baseStart_2917388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917450 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_2917450 : Nat := 118140960795 + 2917450 * 2 ^ 59
def prefixEnd_2917450 : Nat := 4983230072969 + 3 ^ 40 * 2917450 * 2
def baseEnd_2917450 : Nat := 332900918991047932701755

theorem tailTrace_2917450 : CollatzResearch.WordTrace tailWord_2917450 prefixEnd_2917450 332900918991047932701755 := by
  unfold tailWord_2917450
  simp only [CollatzResearch.WordTrace]
  refine ⟨26602035820146096409135451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70938762187056257091027869 26602035820146096409135451)
  ·
    refine ⟨39903053730219144613703177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26602035820146096409135451 39903053730219144613703177)
    ·
      refine ⟨29927290297664358460277383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39903053730219144613703177 29927290297664358460277383)
      ·
        refine ⟨44890935446496537690416075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29927290297664358460277383 44890935446496537690416075)
        ·
          refine ⟨67336403169744806535624113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44890935446496537690416075 67336403169744806535624113)
          ·
            refine ⟨50502302377308604901718085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67336403169744806535624113 50502302377308604901718085)
            ·
              refine ⟨9469181695745363419072141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50502302377308604901718085 9469181695745363419072141)
              ·
                refine ⟨3550943135904511282152053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9469181695745363419072141 3550943135904511282152053)
                ·
                  refine ⟨332900918991047932701755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550943135904511282152053 332900918991047932701755)
                  ·
                    rfl

theorem cell22_2917450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_2917450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917450 prefixEnd_2917450 := by exact prefixLift 2917450
  have htrace : WordTrace (prefixWord ++ tailWord_2917450) baseStart_2917450 baseEnd_2917450 := by
    simpa [prefixWord, tailWord_2917450, baseEnd_2917450] using wordTrace_append hprefix tailTrace_2917450
  have hstable : (prefixWord ++ tailWord_2917450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917450).length < 2 ^ (prefixWord ++ tailWord_2917450).sum := by decide
  have hdescent : baseEnd_2917450 < baseStart_2917450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917495 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 6]
def baseStart_2917495 : Nat := 118140960795 + 2917495 * 2 ^ 59
def prefixEnd_2917495 : Nat := 4983230072969 + 3 ^ 40 * 2917495 * 2
def baseEnd_2917495 : Nat := 332906053797592893576709

theorem tailTrace_2917495 : CollatzResearch.WordTrace tailWord_2917495 prefixEnd_2917495 332906053797592893576709 := by
  unfold tailWord_2917495
  simp only [CollatzResearch.WordTrace]
  refine ⟨106409784565421358321929939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70939856376947572214619959 106409784565421358321929939)
  ·
    refine ⟨159614676848132037482894909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106409784565421358321929939 159614676848132037482894909)
    ·
      refine ⟨59855503818049514056085591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159614676848132037482894909 59855503818049514056085591)
      ·
        refine ⟨89783255727074271084128387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59855503818049514056085591 89783255727074271084128387)
        ·
          refine ⟨134674883590611406626192581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89783255727074271084128387 134674883590611406626192581)
          ·
            refine ⟨25251540673239638742411109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134674883590611406626192581 25251540673239638742411109)
            ·
              refine ⟨4734663876232432264202083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25251540673239638742411109 4734663876232432264202083)
              ·
                refine ⟨7101995814348648396303125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734663876232432264202083 7101995814348648396303125)
                ·
                  refine ⟨332906053797592893576709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7101995814348648396303125 332906053797592893576709)
                  ·
                    rfl

theorem cell22_2917495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 6].length) (baseStart_2917495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917495 prefixEnd_2917495 := by exact prefixLift 2917495
  have htrace : WordTrace (prefixWord ++ tailWord_2917495) baseStart_2917495 baseEnd_2917495 := by
    simpa [prefixWord, tailWord_2917495, baseEnd_2917495] using wordTrace_append hprefix tailTrace_2917495
  have hstable : (prefixWord ++ tailWord_2917495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917495).length < 2 ^ (prefixWord ++ tailWord_2917495).sum := by decide
  have hdescent : baseEnd_2917495 < baseStart_2917495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917527 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 4, 3]
def baseStart_2917527 : Nat := 118140960795 + 2917527 * 2 ^ 59
def prefixEnd_2917527 : Nat := 4983230072969 + 3 ^ 40 * 2917527 * 2
def baseEnd_2917527 : Nat := 998729115646741263930029

theorem tailTrace_2917527 : CollatzResearch.WordTrace tailWord_2917527 prefixEnd_2917527 998729115646741263930029 := by
  unfold tailWord_2917527
  simp only [CollatzResearch.WordTrace]
  refine ⟨106410951701305427787094835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70940634467536951858063223 106410951701305427787094835)
  ·
    refine ⟨159616427551958141680642253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106410951701305427787094835 159616427551958141680642253)
    ·
      refine ⟨59856160331984303130240845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159616427551958141680642253 59856160331984303130240845)
      ·
        refine ⟨22446060124494113673840317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59856160331984303130240845 22446060124494113673840317)
        ·
          refine ⟨8417272546685292627690119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22446060124494113673840317 8417272546685292627690119)
          ·
            refine ⟨12625908820027938941535179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8417272546685292627690119 12625908820027938941535179)
            ·
              refine ⟨18938863230041908412302769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625908820027938941535179 18938863230041908412302769)
              ·
                refine ⟨14204147422531431309227077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18938863230041908412302769 14204147422531431309227077)
                ·
                  refine ⟨2663277641724643370480077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14204147422531431309227077 2663277641724643370480077)
                  ·
                    refine ⟨998729115646741263930029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663277641724643370480077 998729115646741263930029)
                    ·
                      rfl

theorem cell22_2917527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 3].length) (baseStart_2917527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917527 prefixEnd_2917527 := by exact prefixLift 2917527
  have htrace : WordTrace (prefixWord ++ tailWord_2917527) baseStart_2917527 baseEnd_2917527 := by
    simpa [prefixWord, tailWord_2917527, baseEnd_2917527] using wordTrace_append hprefix tailTrace_2917527
  have hstable : (prefixWord ++ tailWord_2917527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917527).length < 2 ^ (prefixWord ++ tailWord_2917527).sum := by decide
  have hdescent : baseEnd_2917527 < baseStart_2917527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917540 : List Nat := [2, 3, 1, 2, 3, 1, 10]
def baseStart_2917540 : Nat := 118140960795 + 2917540 * 2 ^ 59
def prefixEnd_2917540 : Nat := 4983230072969 + 3 ^ 40 * 2917540 * 2
def baseEnd_2917540 : Nat := 36990132067126428272407

theorem tailTrace_2917540 : CollatzResearch.WordTrace tailWord_2917540 prefixEnd_2917540 36990132067126428272407 := by
  unfold tailWord_2917540
  simp only [CollatzResearch.WordTrace]
  refine ⟨53205712925129165503659037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70940950566838887338212049 53205712925129165503659037)
  ·
    refine ⟨19952142346923437063872139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53205712925129165503659037 19952142346923437063872139)
    ·
      refine ⟨29928213520385155595808209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19952142346923437063872139 29928213520385155595808209)
      ·
        refine ⟨22446160140288866696856157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29928213520385155595808209 22446160140288866696856157)
        ·
          refine ⟨8417310052608325011321059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22446160140288866696856157 8417310052608325011321059)
          ·
            refine ⟨12625965078912487516981589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8417310052608325011321059 12625965078912487516981589)
            ·
              refine ⟨36990132067126428272407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12625965078912487516981589 36990132067126428272407)
              ·
                rfl

theorem cell22_2917540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 10].length) (baseStart_2917540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917540 prefixEnd_2917540 := by exact prefixLift 2917540
  have htrace : WordTrace (prefixWord ++ tailWord_2917540) baseStart_2917540 baseEnd_2917540 := by
    simpa [prefixWord, tailWord_2917540, baseEnd_2917540] using wordTrace_append hprefix tailTrace_2917540
  have hstable : (prefixWord ++ tailWord_2917540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917540).length < 2 ^ (prefixWord ++ tailWord_2917540).sum := by decide
  have hdescent : baseEnd_2917540 < baseStart_2917540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917561 : List Nat := [1, 2, 1, 4, 1, 5, 2, 1, 2, 3]
def baseStart_2917561 : Nat := 118140960795 + 2917561 * 2 ^ 59
def prefixEnd_2917561 : Nat := 4983230072969 + 3 ^ 40 * 2917561 * 2
def baseEnd_2917561 : Nat := 998740754541576508579925

theorem tailTrace_2917561 : CollatzResearch.WordTrace tailWord_2917561 prefixEnd_2917561 998740754541576508579925 := by
  unfold tailWord_2917561
  simp only [CollatzResearch.WordTrace]
  refine ⟨106412191783182251593832537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70941461188788167729221691 106412191783182251593832537)
  ·
    refine ⟨79809143837386688695374403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106412191783182251593832537 79809143837386688695374403)
    ·
      refine ⟨119713715756080033043061605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79809143837386688695374403 119713715756080033043061605)
      ·
        refine ⟨22446321704265006195574051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119713715756080033043061605 22446321704265006195574051)
        ·
          refine ⟨33669482556397509293361077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446321704265006195574051 33669482556397509293361077)
          ·
            refine ⟨3156513989662266496252601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33669482556397509293361077 3156513989662266496252601)
            ·
              refine ⟨2367385492246699872189451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3156513989662266496252601 2367385492246699872189451)
              ·
                refine ⟨3551078238370049808284177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367385492246699872189451 3551078238370049808284177)
                ·
                  refine ⟨2663308678777537356213133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551078238370049808284177 2663308678777537356213133)
                  ·
                    refine ⟨998740754541576508579925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663308678777537356213133 998740754541576508579925)
                    ·
                      rfl

theorem cell22_2917561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 2, 1, 2, 3].length) (baseStart_2917561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917561 prefixEnd_2917561 := by exact prefixLift 2917561
  have htrace : WordTrace (prefixWord ++ tailWord_2917561) baseStart_2917561 baseEnd_2917561 := by
    simpa [prefixWord, tailWord_2917561, baseEnd_2917561] using wordTrace_append hprefix tailTrace_2917561
  have hstable : (prefixWord ++ tailWord_2917561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917561).length < 2 ^ (prefixWord ++ tailWord_2917561).sum := by decide
  have hdescent : baseEnd_2917561 < baseStart_2917561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917632 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_2917632 : Nat := 118140960795 + 2917632 * 2 ^ 59
def prefixEnd_2917632 : Nat := 4983230072969 + 3 ^ 40 * 2917632 * 2
def baseEnd_2917632 : Nat := 998765059292555990054707

theorem tailTrace_2917632 : CollatzResearch.WordTrace tailWord_2917632 prefixEnd_2917632 998765059292555990054707 := by
  unfold tailWord_2917632
  simp only [CollatzResearch.WordTrace]
  refine ⟨53207390682962515359833575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70943187577283353813111433 53207390682962515359833575)
  ·
    refine ⟨79811086024443773039750363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53207390682962515359833575 79811086024443773039750363)
    ·
      refine ⟨119716629036665659559625545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79811086024443773039750363 119716629036665659559625545)
      ·
        refine ⟨89787471777499244669719159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119716629036665659559625545 89787471777499244669719159)
        ·
          refine ⟨134681207666248867004578739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89787471777499244669719159 134681207666248867004578739)
          ·
            refine ⟨202021811499373300506868109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134681207666248867004578739 202021811499373300506868109)
            ·
              refine ⟨75758179312264987690075541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202021811499373300506868109 75758179312264987690075541)
              ·
                refine ⟨3551164655262421297972291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75758179312264987690075541 3551164655262421297972291)
                ·
                  refine ⟨5326746982893631946958437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551164655262421297972291 5326746982893631946958437)
                  ·
                    refine ⟨998765059292555990054707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5326746982893631946958437 998765059292555990054707)
                    ·
                      rfl

theorem cell22_2917632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_2917632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917632 prefixEnd_2917632 := by exact prefixLift 2917632
  have htrace : WordTrace (prefixWord ++ tailWord_2917632) baseStart_2917632 baseEnd_2917632 := by
    simpa [prefixWord, tailWord_2917632, baseEnd_2917632] using wordTrace_append hprefix tailTrace_2917632
  have hstable : (prefixWord ++ tailWord_2917632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917632).length < 2 ^ (prefixWord ++ tailWord_2917632).sum := by decide
  have hdescent : baseEnd_2917632 < baseStart_2917632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917664 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_2917664 : Nat := 118140960795 + 2917664 * 2 ^ 59
def prefixEnd_2917664 : Nat := 4983230072969 + 3 ^ 40 * 2917664 * 2
def baseEnd_2917664 : Nat := 332925337848839524418203

theorem tailTrace_2917664 : CollatzResearch.WordTrace tailWord_2917664 prefixEnd_2917664 332925337848839524418203 := by
  unfold tailWord_2917664
  simp only [CollatzResearch.WordTrace]
  refine ⟨53207974250904550092416023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70943965667872733456554697 53207974250904550092416023)
  ·
    refine ⟨79811961376356825138624035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53207974250904550092416023 79811961376356825138624035)
    ·
      refine ⟨119717942064535237707936053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79811961376356825138624035 119717942064535237707936053)
      ·
        refine ⟨11223557068550178535119005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119717942064535237707936053 11223557068550178535119005)
        ·
          refine ⟨4208833900706316950669627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11223557068550178535119005 4208833900706316950669627)
          ·
            refine ⟨6313250851059475426004441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208833900706316950669627 6313250851059475426004441)
            ·
              refine ⟨4734938138294606569503331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6313250851059475426004441 4734938138294606569503331)
              ·
                refine ⟨7102407207441909854254997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734938138294606569503331 7102407207441909854254997)
                ·
                  refine ⟨332925337848839524418203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7102407207441909854254997 332925337848839524418203)
                  ·
                    rfl

theorem cell22_2917664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_2917664 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917664 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917664 prefixEnd_2917664 := by exact prefixLift 2917664
  have htrace : WordTrace (prefixWord ++ tailWord_2917664) baseStart_2917664 baseEnd_2917664 := by
    simpa [prefixWord, tailWord_2917664, baseEnd_2917664] using wordTrace_append hprefix tailTrace_2917664
  have hstable : (prefixWord ++ tailWord_2917664).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917664).length < 2 ^ (prefixWord ++ tailWord_2917664).sum := by decide
  have hdescent : baseEnd_2917664 < baseStart_2917664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917692 : List Nat := [2, 2, 2, 2, 1, 4, 1, 8]
def baseStart_2917692 : Nat := 118140960795 + 2917692 * 2 ^ 59
def prefixEnd_2917692 : Nat := 4983230072969 + 3 ^ 40 * 2917692 * 2
def baseEnd_2917692 : Nat := 110976177613192870394947

theorem tailTrace_2917692 : CollatzResearch.WordTrace tailWord_2917692 prefixEnd_2917692 110976177613192870394947 := by
  unfold tailWord_2917692
  simp only [CollatzResearch.WordTrace]
  refine ⟨53208484872853830483425665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70944646497138440644567553 53208484872853830483425665)
  ·
    refine ⟨39906363654640372862569249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53208484872853830483425665 39906363654640372862569249)
    ·
      refine ⟨29929772740980279646926937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39906363654640372862569249 29929772740980279646926937)
      ·
        refine ⟨22447329555735209735195203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29929772740980279646926937 22447329555735209735195203)
        ·
          refine ⟨33670994333602814602792805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22447329555735209735195203 33670994333602814602792805)
          ·
            refine ⟨6313311437550527738023651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33670994333602814602792805 6313311437550527738023651)
            ·
              refine ⟨9469967156325791607035477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313311437550527738023651 9469967156325791607035477)
              ·
                refine ⟨110976177613192870394947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9469967156325791607035477 110976177613192870394947)
                ·
                  rfl

theorem cell22_2917692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_2917692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917692 prefixEnd_2917692 := by exact prefixLift 2917692
  have htrace : WordTrace (prefixWord ++ tailWord_2917692) baseStart_2917692 baseEnd_2917692 := by
    simpa [prefixWord, tailWord_2917692, baseEnd_2917692] using wordTrace_append hprefix tailTrace_2917692
  have hstable : (prefixWord ++ tailWord_2917692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917692).length < 2 ^ (prefixWord ++ tailWord_2917692).sum := by decide
  have hdescent : baseEnd_2917692 < baseStart_2917692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917694 : List Nat := [4, 2, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_2917694 : Nat := 118140960795 + 2917694 * 2 ^ 59
def prefixEnd_2917694 : Nat := 4983230072969 + 3 ^ 40 * 2917694 * 2
def baseEnd_2917694 : Nat := 998786283159608495004517

theorem tailTrace_2917694 : CollatzResearch.WordTrace tailWord_2917694 prefixEnd_2917694 998786283159608495004517 := by
  unfold tailWord_2917694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302130336462551913553017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70944695127800276872282757 13302130336462551913553017)
  ·
    refine ⟨9976597752346913935164763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13302130336462551913553017 9976597752346913935164763)
    ·
      refine ⟨14964896628520370902747145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9976597752346913935164763 14964896628520370902747145)
      ·
        refine ⟨11223672471390278177060359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14964896628520370902747145 11223672471390278177060359)
        ·
          refine ⟨16835508707085417265590539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11223672471390278177060359 16835508707085417265590539)
          ·
            refine ⟨25253263060628125898385809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16835508707085417265590539 25253263060628125898385809)
            ·
              refine ⟨18939947295471094423789357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25253263060628125898385809 18939947295471094423789357)
              ·
                refine ⟨7102480235801660408921009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18939947295471094423789357 7102480235801660408921009)
                ·
                  refine ⟨5326860176851245306690757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7102480235801660408921009 5326860176851245306690757)
                  ·
                    refine ⟨998786283159608495004517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5326860176851245306690757 998786283159608495004517)
                    ·
                      rfl

theorem cell22_2917694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_2917694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917694 prefixEnd_2917694 := by exact prefixLift 2917694
  have htrace : WordTrace (prefixWord ++ tailWord_2917694) baseStart_2917694 baseEnd_2917694 := by
    simpa [prefixWord, tailWord_2917694, baseEnd_2917694] using wordTrace_append hprefix tailTrace_2917694
  have hstable : (prefixWord ++ tailWord_2917694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917694).length < 2 ^ (prefixWord ++ tailWord_2917694).sum := by decide
  have hdescent : baseEnd_2917694 < baseStart_2917694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917799 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 6]
def baseStart_2917799 : Nat := 118140960795 + 2917799 * 2 ^ 59
def prefixEnd_2917799 : Nat := 4983230072969 + 3 ^ 40 * 2917799 * 2
def baseEnd_2917799 : Nat := 332940742268474407043065

theorem tailTrace_2917799 : CollatzResearch.WordTrace tailWord_2917799 prefixEnd_2917799 332940742268474407043065 := by
  unfold tailWord_2917799
  simp only [CollatzResearch.WordTrace]
  refine ⟨106420872356320018240996451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70947248237546678827330967 106420872356320018240996451)
  ·
    refine ⟨159631308534480027361494677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106420872356320018240996451 159631308534480027361494677)
    ·
      refine ⟨7482717587553751282570063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 159631308534480027361494677 7482717587553751282570063)
      ·
        refine ⟨11224076381330626923855095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7482717587553751282570063 11224076381330626923855095)
        ·
          refine ⟨16836114571995940385782643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11224076381330626923855095 16836114571995940385782643)
          ·
            refine ⟨25254171857993910578673965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16836114571995940385782643 25254171857993910578673965)
            ·
              refine ⟨9470314446747716467002737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25254171857993910578673965 9470314446747716467002737)
              ·
                refine ⟨7102735835060787350252053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9470314446747716467002737 7102735835060787350252053)
                ·
                  refine ⟨332940742268474407043065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7102735835060787350252053 332940742268474407043065)
                  ·
                    rfl

theorem cell22_2917799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_2917799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917799 prefixEnd_2917799 := by exact prefixLift 2917799
  have htrace : WordTrace (prefixWord ++ tailWord_2917799) baseStart_2917799 baseEnd_2917799 := by
    simpa [prefixWord, tailWord_2917799, baseEnd_2917799] using wordTrace_append hprefix tailTrace_2917799
  have hstable : (prefixWord ++ tailWord_2917799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917799).length < 2 ^ (prefixWord ++ tailWord_2917799).sum := by decide
  have hdescent : baseEnd_2917799 < baseStart_2917799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917846 : List Nat := [5, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2917846 : Nat := 118140960795 + 2917846 * 2 ^ 59
def prefixEnd_2917846 : Nat := 4983230072969 + 3 ^ 40 * 2917846 * 2
def baseEnd_2917846 : Nat := 998838315865930765204051

theorem tailTrace_2917846 : CollatzResearch.WordTrace tailWord_2917846 prefixEnd_2917846 998838315865930765204051 := by
  unfold tailWord_2917846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651411661696859079247337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70948391058099830178638261 6651411661696859079247337)
  ·
    refine ⟨4988558746272644309435503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6651411661696859079247337 4988558746272644309435503)
    ·
      refine ⟨7482838119408966464153255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4988558746272644309435503 7482838119408966464153255)
      ·
        refine ⟨11224257179113449696229883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7482838119408966464153255 11224257179113449696229883)
        ·
          refine ⟨16836385768670174544344825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11224257179113449696229883 16836385768670174544344825)
          ·
            refine ⟨12627289326502630908258619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16836385768670174544344825 12627289326502630908258619)
            ·
              refine ⟨18940933989753946362387929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627289326502630908258619 18940933989753946362387929)
              ·
                refine ⟨14205700492315459771790947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18940933989753946362387929 14205700492315459771790947)
                ·
                  refine ⟨21308550738473189657686421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14205700492315459771790947 21308550738473189657686421)
                  ·
                    refine ⟨998838315865930765204051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21308550738473189657686421 998838315865930765204051)
                    ·
                      rfl

theorem cell22_2917846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2917846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917846 prefixEnd_2917846 := by exact prefixLift 2917846
  have htrace : WordTrace (prefixWord ++ tailWord_2917846) baseStart_2917846 baseEnd_2917846 := by
    simpa [prefixWord, tailWord_2917846, baseEnd_2917846] using wordTrace_append hprefix tailTrace_2917846
  have hstable : (prefixWord ++ tailWord_2917846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917846).length < 2 ^ (prefixWord ++ tailWord_2917846).sum := by decide
  have hdescent : baseEnd_2917846 < baseStart_2917846 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917861 : List Nat := [1, 3, 1, 5, 1, 1, 4, 6]
def baseStart_2917861 : Nat := 118140960795 + 2917861 * 2 ^ 59
def prefixEnd_2917861 : Nat := 4983230072969 + 3 ^ 40 * 2917861 * 2
def baseEnd_2917861 : Nat := 110982605630275080675445

theorem tailTrace_2917861 : CollatzResearch.WordTrace tailWord_2917861 prefixEnd_2917861 110982605630275080675445 := by
  unfold tailWord_2917861
  simp only [CollatzResearch.WordTrace]
  refine ⟨106423133682095402829753437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70948755788063601886502291 106423133682095402829753437)
  ·
    refine ⟨39908675130785776061157539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106423133682095402829753437 39908675130785776061157539)
    ·
      refine ⟨59863012696178664091736309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39908675130785776061157539 59863012696178664091736309)
      ·
        refine ⟨5612157440266749758600279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59863012696178664091736309 5612157440266749758600279)
        ·
          refine ⟨8418236160400124637900419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612157440266749758600279 8418236160400124637900419)
          ·
            refine ⟨12627354240600186956850629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418236160400124637900419 12627354240600186956850629)
            ·
              refine ⟨2367628920112535054409493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12627354240600186956850629 2367628920112535054409493)
              ·
                refine ⟨110982605630275080675445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2367628920112535054409493 110982605630275080675445)
                ·
                  rfl

theorem cell22_2917861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 6].length) (baseStart_2917861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917861 prefixEnd_2917861 := by exact prefixLift 2917861
  have htrace : WordTrace (prefixWord ++ tailWord_2917861) baseStart_2917861 baseEnd_2917861 := by
    simpa [prefixWord, tailWord_2917861, baseEnd_2917861] using wordTrace_append hprefix tailTrace_2917861
  have hstable : (prefixWord ++ tailWord_2917861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917861).length < 2 ^ (prefixWord ++ tailWord_2917861).sum := by decide
  have hdescent : baseEnd_2917861 < baseStart_2917861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2917966 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_2917966 : Nat := 118140960795 + 2917966 * 2 ^ 59
def prefixEnd_2917966 : Nat := 4983230072969 + 3 ^ 40 * 2917966 * 2
def baseEnd_2917966 : Nat := 998879394318290452203683

theorem tailTrace_2917966 : CollatzResearch.WordTrace tailWord_2917966 prefixEnd_2917966 998879394318290452203683 := by
  unfold tailWord_2917966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303370418339375720290719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70951308897810003841550501 13303370418339375720290719)
  ·
    refine ⟨19955055627509063580436079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13303370418339375720290719 19955055627509063580436079)
    ·
      refine ⟨29932583441263595370654119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19955055627509063580436079 29932583441263595370654119)
      ·
        refine ⟨44898875161895393055981179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29932583441263595370654119 44898875161895393055981179)
        ·
          refine ⟨67348312742843089583971769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44898875161895393055981179 67348312742843089583971769)
          ·
            refine ⟨50511234557132317187978827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67348312742843089583971769 50511234557132317187978827)
            ·
              refine ⟨75766851835698475781968241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50511234557132317187978827 75766851835698475781968241)
              ·
                refine ⟨56825138876773856836476181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75766851835698475781968241 56825138876773856836476181)
                ·
                  refine ⟨2663678384848774539209821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56825138876773856836476181 2663678384848774539209821)
                  ·
                    refine ⟨998879394318290452203683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663678384848774539209821 998879394318290452203683)
                    ·
                      rfl

theorem cell22_2917966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_2917966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2917966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2917966 prefixEnd_2917966 := by exact prefixLift 2917966
  have htrace : WordTrace (prefixWord ++ tailWord_2917966) baseStart_2917966 baseEnd_2917966 := by
    simpa [prefixWord, tailWord_2917966, baseEnd_2917966] using wordTrace_append hprefix tailTrace_2917966
  have hstable : (prefixWord ++ tailWord_2917966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2917966).length < 2 ^ (prefixWord ++ tailWord_2917966).sum := by decide
  have hdescent : baseEnd_2917966 < baseStart_2917966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2917966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918000 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 2, 3]
def baseStart_2918000 : Nat := 118140960795 + 2918000 * 2 ^ 59
def prefixEnd_2918000 : Nat := 4983230072969 + 3 ^ 40 * 2918000 * 2
def baseEnd_2918000 : Nat := 998891033213125696853579

theorem tailTrace_2918000 : CollatzResearch.WordTrace tailWord_2918000 prefixEnd_2918000 998891033213125696853579 := by
  unfold tailWord_2918000
  simp only [CollatzResearch.WordTrace]
  refine ⟨53214101714295914784531727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70952135619061219712708969 53214101714295914784531727)
  ·
    refine ⟨79821152571443872176797591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53214101714295914784531727 79821152571443872176797591)
    ·
      refine ⟨119731728857165808265196387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79821152571443872176797591 119731728857165808265196387)
      ·
        refine ⟨179597593285748712397794581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119731728857165808265196387 179597593285748712397794581)
        ·
          refine ⟨8418637185269470893646621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 179597593285748712397794581 8418637185269470893646621)
          ·
            refine ⟨3156988944476051585117483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8418637185269470893646621 3156988944476051585117483)
            ·
              refine ⟨4735483416714077377676225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156988944476051585117483 4735483416714077377676225)
              ·
                refine ⟨3551612562535558033257169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735483416714077377676225 3551612562535558033257169)
                ·
                  refine ⟨2663709421901668524942877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3551612562535558033257169 2663709421901668524942877)
                  ·
                    refine ⟨998891033213125696853579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663709421901668524942877 998891033213125696853579)
                    ·
                      rfl

theorem cell22_2918000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 2, 3].length) (baseStart_2918000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918000 prefixEnd_2918000 := by exact prefixLift 2918000
  have htrace : WordTrace (prefixWord ++ tailWord_2918000) baseStart_2918000 baseEnd_2918000 := by
    simpa [prefixWord, tailWord_2918000, baseEnd_2918000] using wordTrace_append hprefix tailTrace_2918000
  have hstable : (prefixWord ++ tailWord_2918000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918000).length < 2 ^ (prefixWord ++ tailWord_2918000).sum := by decide
  have hdescent : baseEnd_2918000 < baseStart_2918000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2918103 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 4]
def baseStart_2918103 : Nat := 118140960795 + 2918103 * 2 ^ 59
def prefixEnd_2918103 : Nat := 4983230072969 + 3 ^ 40 * 2918103 * 2
def baseEnd_2918103 : Nat := 332975430739355920509421

theorem tailTrace_2918103 : CollatzResearch.WordTrace tailWord_2918103 prefixEnd_2918103 332975430739355920509421 := by
  unfold tailWord_2918103
  simp only [CollatzResearch.WordTrace]
  refine ⟨106431960147218678160062963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70954640098145785440041975 106431960147218678160062963)
  ·
    refine ⟨159647940220828017240094445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106431960147218678160062963 159647940220828017240094445)
    ·
      refine ⟨59867977582810506465035417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 159647940220828017240094445 59867977582810506465035417)
      ·
        refine ⟨44900983187107879848776563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59867977582810506465035417 44900983187107879848776563)
        ·
          refine ⟨67351474780661819773164845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44900983187107879848776563 67351474780661819773164845)
          ·
            refine ⟨25256803042748182414936817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67351474780661819773164845 25256803042748182414936817)
            ·
              refine ⟨18942602282061136811202613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25256803042748182414936817 18942602282061136811202613)
              ·
                refine ⟨1775868963943231576050245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18942602282061136811202613 1775868963943231576050245)
                ·
                  refine ⟨332975430739355920509421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775868963943231576050245 332975430739355920509421)
                  ·
                    rfl

theorem cell22_2918103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 4].length) (baseStart_2918103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2918103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2918103 prefixEnd_2918103 := by exact prefixLift 2918103
  have htrace : WordTrace (prefixWord ++ tailWord_2918103) baseStart_2918103 baseEnd_2918103 := by
    simpa [prefixWord, tailWord_2918103, baseEnd_2918103] using wordTrace_append hprefix tailTrace_2918103
  have hstable : (prefixWord ++ tailWord_2918103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2918103).length < 2 ^ (prefixWord ++ tailWord_2918103).sum := by decide
  have hdescent : baseEnd_2918103 < baseStart_2918103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2918103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
